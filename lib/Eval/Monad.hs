{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Eval.Monad where

import           Control.Lens

import           Praeludium
import           Types

newtype EvalM a = EvalM { unEvalM :: ExceptT Text (ReaderT EvalEnv (Writer [LogItem])) a }
  deriving
   ( Functor
   , Applicative
   , Monad
   , MonadReader EvalEnv
   , MonadError  Text
   , MonadWriter [LogItem]
   )

data EvalEnv = EvalEnv { _evalBindings :: !(Map Text Exp), _evalRecursionDepth :: !Int }

runEvalM :: Show a => Map Text Exp -> EvalM a -> (Either Text a, [LogItem])
runEvalM env action =
  action
    & (   unEvalM
      >>> runExceptT
      >>> flip runReaderT
               (EvalEnv {_evalBindings = env, _evalRecursionDepth = 0})
      >>> runWriter
      )

bindings :: Lens' EvalEnv (Map Text Exp)
bindings = lens _evalBindings (\e b -> e { _evalBindings = b })

evalRecursionDepth :: Lens' EvalEnv Int
evalRecursionDepth =
  lens _evalRecursionDepth (\t b -> t { _evalRecursionDepth = b })

instance HasRecursionDepth EvalEnv where
  recursionDepth = evalRecursionDepth
