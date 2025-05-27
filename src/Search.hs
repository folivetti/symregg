module Search where

import Algorithm.EqSat.Egraph
import Algorithm.EqSat.Simplify
import Algorithm.EqSat.Build
import Algorithm.EqSat.Queries
import Algorithm.EqSat.Info
import Algorithm.EqSat.DB
import Algorithm.SRTree.Likelihoods
import Algorithm.SRTree.ModelSelection
import Control.Monad ( forM_, forM, when, filterM )
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as IM
import Data.Massiv.Array as MA hiding (forM_, forM)
import Data.Maybe ( fromJust, isNothing )
import Data.SRTree
import Data.SRTree.Print ( showExpr, showPython )
import Options.Applicative as Opt hiding (Const)
import System.Random
import Data.List ( intercalate, zip4 )
import qualified Data.IntSet as IntSet
import Algorithm.EqSat (runEqSat)
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Debug.Trace
import qualified Data.HashSet as Set
import Control.Lens (over)
import qualified Data.Map.Strict as Map

--import Algorithm.EqSat.SearchSR
import Data.SRTree.Random
import Data.SRTree.Datasets
import Text.ParseSR

import Algorithm.EqSat.SearchSR

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)

data Args = Args
  { _dataset      :: String,
    _testData     :: String,
    _gens         :: Int,
    _alg          :: Alg,
    _maxSize      :: Int,
    _split        :: Int,
    _trace        :: Bool,
    _simplify     :: Bool,
    _distribution :: Distribution,
    _optIter      :: Int,
    _optRepeat    :: Int,
    _nParams      :: Int,
    _nonterminals :: String,
    _dumpTo       :: String,
    _loadFrom     :: String
  }
  deriving (Show)

csvHeader :: String
csvHeader = "id,view,Expression,Numpy,theta,size,loss_train,loss_val,loss_test,maxloss,R2_train,R2_val,R2_test,mdl_train,mdl_val,mdl_test"

egraphSearch :: [(DataSet, DataSet)] -> [DataSet] -> Args -> StateT EGraph (StateT StdGen IO) String
egraphSearch dataTrainVals dataTests args = do
  if null (_loadFrom args)
    then do ecFst <- insertRndExpr (_maxSize args) rndTerm rndNonTerm
            updateIfNothing fitFun ecFst
            insertTerms
            evaluateUnevaluated fitFun
            runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1
            cleanDB
    else (io $ BS.readFile (_loadFrom args)) >>= \eg -> put (decode eg)
  nCls <- gets (IM.size . _eClass)
  nUnev <- gets (IntSet.size . _unevaluated . _eDB)
  let nEvs = nCls - nUnev
  allEcs <- getAllEvaluatedEClasses >>= Prelude.mapM canonical
  eqs <- if _trace args
            then forM (Prelude.zip [0..] allEcs) $ uncurry printExpr
            else pure []


  (outputs,_) <- while ((<(_gens args)) . snd) (eqs, nEvs) $
    \(output, nEvs) ->
      do
       nCls  <- gets (IM.size . _eClass)
       ecN <- case (_alg args) of
                    OnlyRandom -> do let ratio = fromIntegral nEvs / fromIntegral nCls
                                     b <- rnd (tossBiased ratio)
                                     ec <- if b && ratio > 0.99
                                              then insertRndExpr (_maxSize args) rndTerm rndNonTerm >>= canonical
                                              else do mEc <- pickRndSubTree
                                                      case mEc of
                                                           Nothing ->insertRndExpr (_maxSize args) rndTerm rndNonTerm >>= canonical
                                                           Just ec' -> pure ec'
                                     pure ec
                    BestFirst  -> do
                      ecsPareto <- getParetoEcsUpTo 50 (_maxSize args)
                      ecPareto     <- combineFrom ecsPareto >>= canonical
                      curFitPareto <- getFitness ecPareto

                      if isNothing curFitPareto
                        then pure ecPareto
                        else do ecsBest    <- getTopFitEClassThat 100 (isSizeOf (<(_maxSize args)))
                                ecBest     <- combineFrom ecsBest >>= canonical
                                curFitBest <- getFitness ecBest
                                if isNothing curFitBest
                                  then pure ecBest
                                  else do ee <- pickRndSubTree
                                          case ee of
                                            Nothing -> insertRndExpr (_maxSize args) rndTerm rndNonTerm >>= canonical
                                            Just c  -> pure c

       -- when upd $
       ecN' <- canonical ecN
       upd <- updateIfNothing fitFun ecN'
       when upd $ runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1 >> cleanDB >> refitChanged

       output' <- if (upd && (_trace args))
                     then (:output) <$> (canonical ecN' >>= printExpr nEvs)
                     else pure output

       let nEvs'    = nEvs + if upd then 1 else 0
       pure (output', nEvs')

  when ((not.null) (_dumpTo args)) $ get >>= (io . BS.writeFile (_dumpTo args) . encode )
  pf <- if _trace args
           then pure (Prelude.reverse outputs)
           else paretoFront fitFun (_maxSize args) printExpr
  pure $ unlines (csvHeader : concat pf)

  where
    maxSize        = _maxSize args
    relabel        = if (_nParams args == -1) then relabelParams else relabelParamsOrder
    shouldReparam  = _nParams args == -1

    fitFun :: Fix SRTree -> StateT EGraph (StateT StdGen IO) (Double, [PVector])
    fitFun = fitnessMV shouldReparam (_optRepeat args) (_optIter args) (_distribution args) dataTrainVals

    refitChanged = do ids <- gets (_refits . _eDB) >>= Prelude.mapM canonical . Set.toList
                      modify' $ over (eDB . refits) (const Set.empty)
                      forM_ ids $ \ec -> do t <- getBestExpr ec
                                            (f, p) <- fitFun t
                                            insertFitness ec f p

    combineFrom [] = pure 0
    combineFrom ecs = do
      p1  <- rnd (randomFrom ecs) >>= canonical
      p2  <- rnd (randomFrom ecs) >>= canonical
      coin <- rnd toss
      if coin
         then crossover p1 p2 >>= canonical
         else mutate p1 >>= canonical

    nonTerms   = parseNonTerms (_nonterminals args)
    (Sz2 _ nFeats) = MA.size (getX . fst . head $ dataTrainVals)
    terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]]
                               <> if _nParams args == -1
                                     then [param 0]
                                     else Prelude.map param [0 .. _nParams args - 1]
    rndTerm    = randomFrom terms
    rndNonTerm = randomFrom nonTerms
    uniNonTerms = Prelude.filter isUni nonTerms
    binNonTerms = Prelude.filter isBin nonTerms
    isUni (Uni _ _)   = True
    isUni _           = False
    isBin (Bin _ _ _) = True
    isBin _           = False

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical


    printExpr :: Int -> EClassId -> RndEGraph [String]
    printExpr ix ec = do
        thetas' <- gets (_theta . _info . (IM.! ec) . _eClass)
        bestExpr <- (if _simplify args then simplifyEqSatDefault else id) <$> getBestExpr ec

        let best'   = if shouldReparam then relabelParams bestExpr else relabelParamsOrder bestExpr
            nParams = countParamsUniq best'
            fromSz (MA.Sz x) = x
            nThetas = Prelude.map (fromSz . MA.size) thetas'
        (_, thetas) <- if Prelude.any (/=nParams) nThetas
                        then fitFun best'
                        else pure (1.0, thetas')

        maxLoss <- negate . fromJust <$> getFitness ec
        ts <- forM (Data.List.zip4 [0..] dataTrainVals dataTests thetas) $ \(view, (dataTrain, dataVal), dataTest, theta) -> do
            let (x, y, mYErr) = dataTrain
                (x_val, y_val, mYErr_val) = dataVal
                (x_te, y_te, mYErr_te) = dataTest
                distribution = _distribution args

                expr      = paramsToConst (MA.toList theta) best'
                showNA z  = if isNaN z then "" else show z
                r2_train  = r2 x y best' theta
                r2_val    = r2 x_val y_val best' theta
                r2_te     = r2 x_te y_te best' theta
                nll_train  = nll distribution mYErr x y best' theta
                nll_val    = nll distribution mYErr_val x_val y_val best' theta
                nll_te     = nll distribution mYErr_te x_te y_te best' theta
                mdl_train  = mdl distribution mYErr x y theta best'
                mdl_val    = mdl distribution mYErr_val x_val y_val theta best'
                mdl_te     = mdl distribution mYErr_te x_te y_te theta best'
                vals       = intercalate ","
                           $ Prelude.map showNA [ nll_train, nll_val, nll_te, maxLoss
                                                , r2_train, r2_val, r2_te
                                                , mdl_train, mdl_val, mdl_te]
                thetaStr   = intercalate ";" $ Prelude.map show (MA.toList theta)
            pure $ show ix <> "," <> show view <> "," <> showExpr expr <> "," <> "\"" <> showPython best' <> "\","
                           <> thetaStr <> "," <> show (countNodes $ convertProtectedOps expr)
                           <> "," <> vals
        pure ts


    -- From eggp
    crossover p1 p2 = do sz <- getSize p1
                         if sz == 1
                          then rnd (randomFrom [p1, p2])
                          else do pos <- rnd $ randomRange (1, sz-1)
                                  cands <- getAllSubClasses p2
                                  tree <- getSubtree pos 0 Nothing [] cands p1
                                  fromTree myCost (relabel tree) >>= canonical

    getSubtree :: Int -> Int -> Maybe (EClassId -> ENode) -> [Maybe (EClassId -> ENode)] -> [EClassId] -> EClassId -> RndEGraph (Fix SRTree)
    getSubtree 0 sz (Just parent) mGrandParents cands p' = do
      p <- canonical p'
      candidates' <- filterM (\c -> (<maxSize-sz) <$> getSize c) cands
      candidates  <- filterM (\c -> doesNotExistGens mGrandParents (parent c)) candidates'
                        >>= traverse canonical
      if null candidates
          then getBestExpr p
          else do subtree <- rnd (randomFrom candidates)
                  getBestExpr subtree
    getSubtree pos sz parent mGrandParents cands p' = do
      p <- canonical p'
      root <- getBestENode p >>= canonize
      case root of
        Param ix -> pure . Fix $ Param ix
        Const x  -> pure . Fix $ Const x
        Var   ix -> pure . Fix $ Var ix
        Uni f t' -> do t <- canonical t'
                       (Fix . Uni f) <$> getSubtree (pos-1) (sz+1) (Just $ Uni f) (parent:mGrandParents) cands t
        Bin op l'' r'' ->
                      do  l <- canonical l''
                          r <- canonical r''
                          szLft <- getSize l
                          szRgt <- getSize r
                          if szLft < pos
                            then do l' <- getBestExpr l
                                    r' <- getSubtree (pos-szLft-1) (sz+szLft+1) (Just $ Bin op l) (parent:mGrandParents) cands r
                                    pure . Fix $ Bin op l' r'
                            else do l' <- getSubtree (pos-1) (sz+szRgt+1) (Just (\t -> Bin op t r)) (parent:mGrandParents) cands l
                                    r' <- getBestExpr r
                                    pure . Fix $ Bin op l' r'

    getAllSubClasses p' = do
      p  <- canonical p'
      en <- getBestENode p
      case en of
        Bin _ l r -> do ls <- getAllSubClasses l
                        rs <- getAllSubClasses r
                        pure (p : (ls <> rs))
        Uni _ t   -> (p:) <$> getAllSubClasses t
        _         -> pure [p]

    mutate p = do sz <- getSize p
                  pos <- rnd $ randomRange (0, sz-1)
                  tree <- mutAt pos maxSize Nothing p
                  fromTree myCost (relabel tree) >>= canonical

    peel :: Fix SRTree -> SRTree ()
    peel (Fix (Bin op l r)) = Bin op () ()
    peel (Fix (Uni f t)) = Uni f ()
    peel (Fix (Param ix)) = Param ix
    peel (Fix (Var ix)) = Var ix
    peel (Fix (Const x)) = Const x

    mutAt :: Int -> Int -> Maybe (EClassId -> ENode) -> EClassId -> RndEGraph (Fix SRTree)
    mutAt 0 sizeLeft Nothing       _ = (insertRndExpr sizeLeft rndTerm rndNonTerm >>= canonical) >>= getBestExpr -- we chose to mutate the root
    mutAt 0 1        _             _ = rnd $ randomFrom terms -- we don't have size left
    mutAt 0 sizeLeft (Just parent) _ = do -- we reached the mutation place
      ec    <- insertRndExpr sizeLeft rndTerm rndNonTerm >>= canonical -- create a random expression with the size limit
      (Fix tree) <- getBestExpr ec           --
      root  <- getBestENode ec
      exist <- canonize (parent ec) >>= doesExist
      if exist
          -- the expression `parent ec` already exists, try to fix
          then do let children = childrenOf root
                  candidates <- case length children of
                                0  -> filterM (checkToken parent . (replaceChildren children)) (Prelude.map peel terms)
                                1 -> filterM (checkToken parent . (replaceChildren children)) uniNonTerms
                                2 -> filterM (checkToken parent . (replaceChildren children)) binNonTerms
                  if null candidates
                      then pure $ Fix tree -- there's no candidate, so we failed and admit defeat
                      else do newToken <- rnd (randomFrom candidates)
                              pure . Fix $ replaceChildren (childrenOf tree) newToken

          else pure . Fix $ tree

    mutAt pos sizeLeft parent p' = do
        p <- canonical p'
        root <- getBestENode p >>= canonize
        case root of
          Param ix -> pure . Fix $ Param ix
          Const x  -> pure . Fix $ Const x
          Var   ix -> pure . Fix $ Var ix
          Uni f t'  -> canonical t' >>= \t -> (Fix . Uni f) <$> mutAt (pos-1) (sizeLeft-1) (Just $ Uni f) t
          Bin op ln rn -> do  l <- canonical ln
                              r <- canonical rn
                              szLft <- getSize l
                              szRgt <- getSize r
                              if szLft < pos
                                then do l' <- getBestExpr l
                                        r' <- mutAt (pos-szLft-1) (sizeLeft-szLft-1) (Just $ Bin op l) r
                                        pure . Fix $ Bin op l' r'
                                else do l' <- mutAt (pos-1) (sizeLeft-szRgt-1) (Just (\t -> Bin op t r)) l
                                        r' <- getBestExpr r
                                        pure . Fix $ Bin op l' r'



