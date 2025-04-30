{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  BangPatterns #-}
{-# LANGUAGE  TypeSynonymInstances, FlexibleInstances #-}

module Pysymregg where

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
import Random
import System.Random
import Data.List ( intercalate )
import qualified Data.IntSet as IntSet
import Algorithm.EqSat (runEqSat)
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Debug.Trace
import qualified Data.HashSet as Set
import Control.Lens (over)
import qualified Data.Map.Strict as Map

import Util

import Foreign.C (CInt (..), CDouble (..))
import Foreign.C.String (CString, newCString, withCString, peekCString, peekCAString, newCAString)
import Paths_Pysymregg (version)
import System.Environment (getArgs)
import System.Exit (ExitCode (..))
import Text.Read (readMaybe)
import Data.Version (showVersion)
import Control.Exception (Exception (..), SomeException (..), handle)

foreign import ccall unsafe_py_write_stdout :: CString -> IO ()

py_write_stdout :: String -> IO ()
py_write_stdout str = withCString str unsafe_py_write_stdout

foreign import ccall unsafe_py_write_stderr :: CString -> IO ()

py_write_stderr :: String -> IO ()
py_write_stderr str = withCString str unsafe_py_write_stderr

foreign export ccall hs_pysymregg_version :: IO CString

hs_pysymregg_version :: IO CString
hs_pysymregg_version =
  newCString (showVersion version)

foreign export ccall hs_pysymregg_main :: IO CInt

exitHandler :: ExitCode -> IO CInt
exitHandler ExitSuccess = return 0
exitHandler (ExitFailure n) = return (fromIntegral n)

uncaughtExceptionHandler :: SomeException -> IO CInt
uncaughtExceptionHandler (SomeException e) =
  py_write_stderr (displayException e) >> return 1

hs_pysymregg_main :: IO CInt
hs_pysymregg_main =
  handle uncaughtExceptionHandler $
    handle exitHandler $ do
      getArgs >>= \args -> do
        --out <- pyeggp args
        case "" of
          ""  -> py_write_stdout $ "wrong arguments"
          css -> py_write_stdout css
      return 0

foreign export ccall hs_pysymregg_run :: CString -> CInt -> CString -> CInt -> CString -> CString -> CInt -> CInt -> CInt -> CInt -> CString -> CString -> IO CString

hs_pysymregg_run :: CString -> CInt -> CString -> CInt -> CString -> CString -> CInt -> CInt -> CInt -> CInt -> CString -> CString -> IO CString
hs_pysymregg_run dataset gens alg maxSize nonterminals loss optIter optRepeat nParams split dumpTo loadFrom = do
  dataset' <- peekCString dataset
  nonterminals' <- peekCString nonterminals
  alg' <- peekCString alg
  loss' <- peekCString loss
  dumpTo' <- peekCString dumpTo
  loadFrom' <- peekCString loadFrom
  out  <- pysymregg dataset' (fromIntegral gens) alg' (fromIntegral maxSize) nonterminals' loss' (fromIntegral optIter) (fromIntegral optRepeat) (fromIntegral nParams) (fromIntegral split) dumpTo' loadFrom'
  newCString out

data Alg = OnlyRandom | BestFirst deriving (Show, Read, Eq)

egraphSearch :: [(DataSet, DataSet)] -> Args -> StateT EGraph (StateT StdGen IO) String
egraphSearch dataTrainVals args = do
  if null (_loadFrom args)
    then do ecFst <- insertRndExpr (_maxSize args) rndTerm rndNonTerm2
            updateIfNothing fitFun ecFst
            insertTerms
            evaluateUnevaluated fitFun
            runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1
            cleanDB
    else (io $ BS.readFile (_loadFrom args)) >>= \eg -> put (decode eg)
  nCls <- gets (IM.size . _eClass)
  nUnev <- gets (IntSet.size . _unevaluated . _eDB)
  let nEvs = nCls - nUnev

  while ((<(_gens args)) . snd) (10, nEvs) $
    \(radius, nEvs) ->
      do
       nCls  <- gets (IM.size . _eClass)
       ecN <- case (_alg args) of
                    OnlyRandom -> do let ratio = fromIntegral nEvs / fromIntegral nCls
                                     b <- rnd (tossBiased ratio)
                                     ec <- if b && ratio > 0.99
                                              then insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
                                              else do mEc <- pickRndSubTree
                                                      case mEc of
                                                           Nothing ->insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
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
                                            Nothing -> insertRndExpr (_maxSize args) rndTerm rndNonTerm2 >>= canonical
                                            Just c  -> pure c

       -- when upd $
       ecN' <- canonical ecN
       upd <- updateIfNothing fitFun ecN'
       when upd $ runEqSat myCost (if _nParams args == 0 then rewritesWithConstant else rewritesParams) 1 >> cleanDB >> refitChanged

       let radius' = if (not upd) then (max 10 $ min (500 `div` (_maxSize args)) (radius+1)) else (max 10 $ radius-1)
           nEvs'    = nEvs + if upd then 1 else 0
       pure (radius', nEvs')

  when ((not.null) (_dumpTo args)) $ get >>= (io . BS.writeFile (_dumpTo args) . encode )
  pf <- paretoFront fitFun (_maxSize args) printExpr
  pure $ "id,Expression,Numpy,theta,size,loss,maxLoss\n" <> pf

  where
    maxSize = _maxSize args
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

    combineFrom' [] = pure 0 -- this is the first terminal and it will always be already evaluated
    combineFrom' ecs = do
        nt  <- rnd rndNonTerm
        p1  <- rnd (randomFrom ecs)
        p2  <- rnd (randomFrom ecs)
        l1  <- rnd (randomFrom [2..(_maxSize args)-2]) -- sz 10: [2..8]

        e1  <- randomChildFrom p1 l1 >>= canonical
        ml  <- gets (_size . _info . (IM.! e1) . _eClass)
        l2  <- rnd (randomFrom [1..((_maxSize args) - ml - 1)]) -- maxSize - maxSize + 2 - 2= 0 -- sz 10: [1..7] (2) / [1..1] (8)
        e2  <- randomChildFrom p2 l2 >>= canonical
        case nt of
          Uni Id ()    -> canonical e1
          Uni f ()     -> add myCost (Uni f e1) >>= canonical
          Bin op () () -> do b <- rnd toss
                             if b
                              then add myCost (Bin op e1 e2) >>= canonical
                              else add myCost (Bin op e2 e1) >>= canonical
          _            -> canonical e1 -- it is a terminal, should it happen?

    randomChildFrom ec' maxL = do
      p <- rnd toss -- whether to go deeper or return this level
      ec <- canonical ec'
      l <- gets (_size . _info . (IM.! ec) . _eClass )

      if p || l > maxL
          then do --enodes <- gets (_eNodes . (IM.! ec) . _eClass)
                  enode  <- gets (_best . _info . (IM.! ec) . _eClass) -- we should return the best otherwise we may build larger exprs
                  case enode of
                      Uni _ eci     -> randomChildFrom eci maxL
                      Bin _ ecl ecr -> do coin <- rnd toss
                                          if coin
                                            then randomChildFrom ecl maxL
                                            else randomChildFrom ecr maxL
                      _ -> pure ec -- this shouldn't happen unless maxL==0
          else pure ec

    nonTerms   = parseNonTerms (_nonterminals args)
    --[ Bin Add () (), Bin Sub () (), Bin Mul () (), Bin Div () (), Bin PowerAbs () (),  Uni Recip ()]
    (Sz2 _ nFeats) = MA.size (getX . fst . head $ dataTrainVals)
    terms          = if _distribution args == ROXY
                          then [var 0, param 0]
                          else [var ix | ix <- [0 .. nFeats-1]]
                               <> if _nParams args == -1
                                     then [param 0]
                                     else Prelude.map param [0 .. _nParams args - 1]
    rndTerm    = Random.randomFrom terms
    rndNonTerm = Random.randomFrom $ (Uni Id ()) : nonTerms
    rndNonTerm2 = Random.randomFrom nonTerms
    uniNonTerms = Prelude.filter isUni nonTerms
    binNonTerms = Prelude.filter isBin nonTerms
    isUni (Uni _ _) = True
    isUni _         = False
    isBin (Bin _ _ _) = True
    isBin _           = False

    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical


    printExpr :: Int -> EClassId -> RndEGraph String
    printExpr ix ec = do
        thetas' <- gets (_theta . _info . (IM.! ec) . _eClass)
        bestExpr <- getBestExpr ec
        let nParams = countParamsUniq bestExpr
            fromSz (MA.Sz x) = x 
            nThetas  = Prelude.map (fromSz . MA.size) thetas'
        (_, thetas) <- if Prelude.any (/=nParams) nThetas
                        then fitFun bestExpr
                        else pure (1.0, thetas')

        maxLoss <- negate . fromJust <$> getFitness ec
        ts <- forM (Prelude.zip3 [0..] dataTrainVals thetas) $ \(view, (dataTrain, dataVal), theta) -> do
            let (x, y, mYErr) = dataTrain
                (x_val, y_val, mYErr_val) = dataVal
                distribution = _distribution args
                best'     = if shouldReparam then relabelParams bestExpr else relabelParamsOrder bestExpr
                expr      = paramsToConst (MA.toList theta) best'
                thetaStr  = intercalate ";" $ Prelude.map show (MA.toList theta)
                showFun   = showExpr expr
                showFunNp = showPython best'
                mse_train = nll distribution mYErr_val x_val y_val best' theta
            pure . (<> "\n") . intercalate "," $ [show ix, show view, showFun, "\"" <> showFunNp <> "\"", thetaStr, show (countNodes $ convertProtectedOps expr), if isNaN mse_train then "1e+10" else show mse_train, show (negate maxLoss) ]
        pure (concat ts)
    insertTerms =
        forM terms $ \t -> do fromTree myCost t >>= canonical



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

    checkToken parent en' = do  en <- canonize en'
                                mEc <- gets ((Map.!? en) . _eNodeToEClass)
                                case mEc of
                                    Nothing -> pure True
                                    Just ec -> do ec' <- canonical ec
                                                  ec'' <- canonize (parent ec')
                                                  not <$> doesExist ec''
    doesExist, doesNotExist :: ENode -> RndEGraph Bool
    doesExist en = gets ((Map.member en) . _eNodeToEClass)
    doesNotExist en = gets ((Map.notMember en) . _eNodeToEClass)

    doesNotExistGens :: [Maybe (EClassId -> ENode)] -> ENode -> RndEGraph Bool
    doesNotExistGens []              en = gets ((Map.notMember en) . _eNodeToEClass)
    doesNotExistGens (mGrand:grands) en = do  b <- gets ((Map.notMember en) . _eNodeToEClass)
                                              if b
                                                then pure True
                                                else case mGrand of
                                                    Nothing -> pure False
                                                    Just gf -> do ec  <- gets ((Map.! en) . _eNodeToEClass)
                                                                  en' <- canonize (gf ec)
                                                                  doesNotExistGens grands en'

data Args = Args
  { _dataset      :: String,
    -- _testData     :: String,
    _gens         :: Int,
    _alg          :: Alg,
    _maxSize      :: Int,
    _split        :: Int,
    -- _printPareto  :: Bool,
    -- _trace        :: Bool,
    _distribution :: Distribution,
    _optIter      :: Int,
    _optRepeat    :: Int,
    _nParams      :: Int,
    _nonterminals :: String,
    _dumpTo       :: String,
    _loadFrom     :: String
  }
  deriving (Show)

pysymregg :: String -> Int -> String -> Int -> String -> String -> Int -> Int -> Int -> Int -> String -> String -> IO String
pysymregg dataset gens alg maxSize nonterminals loss optIter optRepeat nParams split dumpTo loadFrom =
  case readMaybe alg of
       Nothing -> pure $ "Invalid algorithm " <> alg
       Just a  -> case readMaybe loss of
                       Nothing -> pure $ "Invalid loss function " <> loss
                       Just l  -> let arg = Args dataset gens a maxSize split l optIter optRepeat nParams nonterminals dumpTo loadFrom
                                  in symregg arg

symregg :: Args -> IO String
symregg args = do
  g    <- getStdGen
  let datasets = words (_dataset args)
  dataTrains' <- Prelude.mapM (flip loadTrainingOnly True) datasets -- load all datasets

  let (dataTrainVals, g') = runState (Prelude.mapM (`splitData` (_split args)) dataTrains') g
      alg = evalStateT (egraphSearch dataTrainVals args) emptyGraph
  evalStateT alg g'
