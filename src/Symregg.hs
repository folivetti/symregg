{-# LANGUAGE  BlockArguments #-}
{-# LANGUAGE  TupleSections #-}
{-# LANGUAGE  MultiWayIf #-}
{-# LANGUAGE  OverloadedStrings #-}
{-# LANGUAGE  BangPatterns #-}
{-# LANGUAGE  TypeSynonymInstances, FlexibleInstances #-}

module Symregg where

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
import Data.List ( intercalate )
import qualified Data.IntSet as IntSet
import Algorithm.EqSat (runEqSat)
import Data.Binary ( encode, decode )
import qualified Data.ByteString.Lazy as BS
import Debug.Trace
import qualified Data.HashSet as Set
import Control.Lens (over)
import qualified Data.Map.Strict as Map


import Search
import Algorithm.EqSat.SearchSR
import Data.SRTree.Random
import Data.SRTree.Datasets

import Foreign.C (CInt (..), CDouble (..))
import Foreign.C.String (CString, newCString, withCString, peekCString, peekCAString, newCAString)
import Paths_symregg (version)
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

foreign export ccall hs_symregg_version :: IO CString

hs_symregg_version :: IO CString
hs_symregg_version =
  newCString (showVersion version)

foreign export ccall hs_symregg_main :: IO CInt

exitHandler :: ExitCode -> IO CInt
exitHandler ExitSuccess = return 0
exitHandler (ExitFailure n) = return (fromIntegral n)

uncaughtExceptionHandler :: SomeException -> IO CInt
uncaughtExceptionHandler (SomeException e) =
  py_write_stderr (displayException e) >> return 1

hs_symregg_main :: IO CInt
hs_symregg_main =
  handle uncaughtExceptionHandler $
    handle exitHandler $ do
      args <- execParser opts
      g    <- getStdGen
      let datasets = words (_dataset args)
      dataTrains' <- Prelude.mapM (flip loadTrainingOnly True) datasets -- load all datasets
      dataTests   <- if null (_testData args)
                      then pure dataTrains'
                      else Prelude.mapM (flip loadTrainingOnly True) $ words (_testData args)

      let (dataTrainVals, g') = runState (Prelude.mapM (`splitData` (_split args)) dataTrains') g
          alg = evalStateT (egraphSearch dataTrainVals dataTests args) emptyGraph
      out <- evalStateT alg g'
      py_write_stdout out
      pure 0
  where
    opts = Opt.info (opt <**> helper)
            ( fullDesc <> progDesc "Symbolic Regression search algorithm\
                                   \ exploiting the potentials of equality saturation\
                                   \ and e-graphs."
           <> header "SymRegg - symbolic regression with e-graphs."
            )

foreign export ccall hs_symregg_run :: CString -> CInt -> CString -> CInt -> CString -> CString -> CInt -> CInt -> CInt -> CInt -> CInt -> CInt -> CString -> CString -> IO CString

hs_symregg_run :: CString -> CInt -> CString -> CInt -> CString -> CString -> CInt -> CInt -> CInt -> CInt -> CInt -> CInt -> CString -> CString -> IO CString
hs_symregg_run dataset gens alg maxSize nonterminals loss optIter optRepeat nParams folds trace simplify dumpTo loadFrom = do
  dataset' <- peekCString dataset
  nonterminals' <- peekCString nonterminals
  alg' <- peekCString alg
  loss' <- peekCString loss
  dumpTo' <- peekCString dumpTo
  loadFrom' <- peekCString loadFrom
  out  <- symregg_run dataset' (fromIntegral gens) alg' (fromIntegral maxSize) nonterminals' loss' (fromIntegral optIter) (fromIntegral optRepeat) (fromIntegral nParams) (fromIntegral folds) (fromIntegral trace /= 0) (fromIntegral simplify /= 0) dumpTo' loadFrom'
  newCString out


csvHeader :: String
csvHeader = "id,view,Expression,Numpy,theta,size,loss_train,loss_val,loss_test,maxloss,R2_train,R2_val,R2_test,mdl_train,mdl_val,mdl_test"

opt :: Parser Args
opt = Args
   <$> strOption
       ( long "dataset"
       <> short 'd'
       <> metavar "INPUT-FILE"
       <> help "CSV dataset." )
  <*> strOption
       ( long "test"
       <> short 't'
       <> value ""
       <> showDefault
       <> help "test data")
   <*> option auto
      ( long "generations"
      <> short 'g'
      <> metavar "GENS"
      <> showDefault
      <> value 100
      <> help "Number of generations." )
   <*> option auto
       ( long "algorithm"
       <> short 'a'
       <> metavar "ALG"
       <> help "Algorithm." )
  <*> option auto
       ( long "maxSize"
       <> short 's'
       <> help "max-size." )
  <*> option auto
       ( long "folds"
       <> short 'k'
       <> value 1
       <> showDefault
       <> help "number of folds for a k-split training-validation")
  <*> switch
       ( long "trace"
       <> help "print all evaluated expressions.")
  <*> switch
      ( long "Simplify"
      <> help "simplify the expressions before printing.")
  <*> option auto
       ( long "loss"
       <> value MSE
       <> showDefault
       <> help "distribution of the data.")
  <*> option auto
       ( long "opt-iter"
       <> value 30
       <> showDefault
       <> help "number of iterations in parameter optimization.")
  <*> option auto
       ( long "opt-retries"
       <> value 1
       <> showDefault
       <> help "number of retries of parameter fitting.")
  <*> option auto
       ( long "number-params"
       <> value (-1)
       <> showDefault
       <> help "maximum number of parameters in the model. If this argument is absent, the number is bounded by the maximum size of the expression and there will be no repeated parameter.")
  <*> strOption
       ( long "non-terminals"
       <> value "Add,Sub,Mul,Div,PowerAbs,Recip"
       <> showDefault
       <> help "set of non-terminals to use in the search."
       )
  <*> strOption
       ( long "dump-to"
       <> value ""
       <> showDefault
       <> help "dump final e-graph to a file."
       )
  <*> strOption
       ( long "load-from"
       <> value ""
       <> showDefault
       <> help "load initial e-graph from a file."
       )

symregg_run :: String -> Int -> String -> Int -> String -> String -> Int -> Int -> Int -> Int -> Bool -> Bool -> String -> String -> IO String
symregg_run dataset gens alg maxSize nonterminals loss optIter optRepeat nParams folds trace simplify dumpTo loadFrom =
  case readMaybe alg of
       Nothing -> pure $ "Invalid algorithm " <> alg
       Just a  -> case readMaybe loss of
                       Nothing -> pure $ "Invalid loss function " <> loss
                       Just l  -> let arg = Args dataset "" gens a maxSize folds trace simplify l optIter optRepeat nParams nonterminals dumpTo loadFrom
                                  in symregg arg

symregg :: Args -> IO String
symregg args = do
  g    <- getStdGen
  let datasets = words (_dataset args)
  dataTrains' <- Prelude.mapM (flip loadTrainingOnly True) datasets -- load all datasets

  let (dataTrainVals, g') = runState (Prelude.mapM (`splitData` (_split args)) dataTrains') g
      alg = evalStateT (egraphSearch dataTrainVals dataTrains' args) emptyGraph
  evalStateT alg g'
