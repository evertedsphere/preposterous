{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Monad where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.Map                 (Map)
import           Data.Text                (Text)
import           Control.Lens

import           Types

data TcEnv i = TcEnv
  { _bindings       :: Map (Sym i) (Poly i)
  , _topLevelAxioms :: AxiomSch i
  }

type TcWriter i = ()

data TcState i = TcState
  { _supply :: Int -- ^ For `fresh` things. TODO use concurrent-supply?
  }

data TcErr =
  ErrText Text
  deriving (Show)

newtype TcM i a = TcM
  { unTcM :: ExceptT TcErr (RWST (TcEnv i) (TcWriter i) (TcState i) Identity) a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadReader (TcEnv i)
             , MonadWriter (TcWriter i)
             , MonadState (TcState i)
             , MonadRWS (TcEnv i) (TcWriter i) (TcState i)
             , MonadError TcErr
             )

bindings :: Lens' (TcEnv i) (Map (Sym i) (Poly i))
bindings = lens _bindings (\t b -> t { _bindings = b })

topLevelAxioms :: Lens' (TcEnv i) (AxiomSch i)
topLevelAxioms = lens _topLevelAxioms (\t b -> t { _topLevelAxioms = b })

supply :: Lens' (TcState i) Int
supply = lens _supply (\t b -> t { _supply = b })
