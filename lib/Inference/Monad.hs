{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Monad where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.Map                 (Map)
import           Data.Text                (Text)
import           Control.Lens

import           Types

data TcEnv = TcEnv
  { _bindings       :: Map Sym Poly
  , _topLevelAxioms :: AxiomSch
  }

type TcWriter = ()

data TcState = TcState
  { _supply :: Int -- ^ For `fresh` things. TODO use concurrent-supply?
  }

data TcErr =
  ErrText Text
  deriving (Show)

newtype TcM a = TcM
  { unTcM :: ExceptT TcErr (RWST TcEnv TcWriter TcState Identity) a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadReader TcEnv
             , MonadWriter TcWriter
             , MonadState TcState
             , MonadRWS TcEnv TcWriter TcState
             , MonadError TcErr
             )

bindings :: Lens' TcEnv (Map Sym Poly)
bindings = lens _bindings (\t b -> t { _bindings = b })

topLevelAxioms :: Lens' TcEnv AxiomSch
topLevelAxioms = lens _topLevelAxioms (\t b -> t { _topLevelAxioms = b })

supply :: Lens' TcState Int
supply = lens _supply (\t b -> t { _supply = b })
