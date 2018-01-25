{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Inference.Monad where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.Map                 (Map)
import           Data.Text                (Text)
import qualified Data.Text
import           Control.Lens

import           Types

data LogItem = LogItem { _messageDepth :: !Int, _messageContents :: Message }

instance Show LogItem where
  show (LogItem d (MsgText m)) = show d ++ ": " ++ Data.Text.unpack m
  -- show (LogItem d m) = show d ++ ": " ++ show m

data Message = MsgText Text
  deriving Show

data TcEnv = TcEnv
  { _bindings       :: Map Sym Poly
  , _topLevelAxioms :: AxiomSch
  , _recursionDepth :: Int
  }

type TcWriter = [LogItem]

data TcState = TcState
  { _supply :: Int -- ^ For `fresh` things. TODO use concurrent-supply?
  }

data TcErr =
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

bindings :: Lens' TcEnv (Map Sym Poly)
bindings = lens _bindings (\t b -> t { _bindings = b })

topLevelAxioms :: Lens' TcEnv AxiomSch
topLevelAxioms = lens _topLevelAxioms (\t b -> t { _topLevelAxioms = b })

supply :: Lens' TcState Int
supply = lens _supply (\t b -> t { _supply = b })

recursionDepth :: Lens' TcEnv Int
recursionDepth = lens _recursionDepth (\t b -> t { _recursionDepth = b })

