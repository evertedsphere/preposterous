{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Inference.Monad where

import           Control.Category         ((<<<), (>>>))
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.IO.Class
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.List.NonEmpty       (NonEmpty (..), nonEmpty, (!!))
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Maybe
import           Data.Set                 (Set)
import qualified Data.Set                 as Set
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           Data.Traversable

import           Types

data TcEnv i = TcEnv
  { bindings       :: Map (Sym i) (Poly i)
  , topLevelAxioms :: AxiomSch i
  }

type TcWriter i = ()

data TcState i = TcState
  { supply :: Int
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
