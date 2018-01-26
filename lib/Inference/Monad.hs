{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Monad where

import qualified Data.Text
import           Control.Lens

import           Types
import           Praeludium

data TcEnv = TcEnv
  { _bindingTypes       :: Map Sym Poly
  , _topLevelAxioms :: AxiomSch
  , _tcRecursionDepth :: Int
  }

type TcWriter = [LogItem]

newtype TcState = TcState
  { _supply :: Int -- ^ For `fresh` things. TODO use concurrent-supply?
  }

newtype TcErr =
  ErrText Text
  deriving (Show)

newtype TcM a = TcM
  { unTcM :: ExceptT [TcErr] (RWST TcEnv TcWriter TcState Identity) a
  } deriving ( Functor
             , Applicative
             , Monad
             , Alternative
             , MonadReader TcEnv
             , MonadWriter TcWriter
             , MonadState TcState
             , MonadRWS TcEnv TcWriter TcState
             , MonadError [TcErr]
             )

runTcM :: TcEnv -> TcState -> TcM a -> (Either [TcErr] a, TcState, TcWriter)
runTcM r s ma = runRWS (runExceptT (unTcM ma)) r s

bindingTypes :: Lens' TcEnv (Map Sym Poly)
bindingTypes = lens _bindingTypes (\t b -> t { _bindingTypes = b })

topLevelAxioms :: Lens' TcEnv AxiomSch
topLevelAxioms = lens _topLevelAxioms (\t b -> t { _topLevelAxioms = b })

supply :: Lens' TcState Int
supply = lens _supply (\t b -> t { _supply = b })

tcRecursionDepth :: Lens' TcEnv Int
tcRecursionDepth = lens _tcRecursionDepth (\t b -> t { _tcRecursionDepth = b })

instance HasRecursionDepth TcEnv where
  recursionDepth = tcRecursionDepth
