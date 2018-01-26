module Praeludium (module X, (>>>)) where

import           Control.Applicative         as X
import           Control.Monad               as X
import           Data.Foldable               as X
import           Data.Semigroup              as X
import           Data.Traversable            as X

import           Control.Monad.Identity      as X (Identity (..))

-- Data structures
import           Data.List.NonEmpty          as X (NonEmpty (..))
import           Data.Map                    as X (Map)
import           Data.Text                   as X (Text)

-- Monad transformers
import           Control.Monad.Except        as X (Except, ExceptT,
                                                   MonadError (..), runExcept,
                                                   runExceptT)
import           Control.Monad.Reader        as X (MonadReader (..), Reader,
                                                   ReaderT, runReader,
                                                   runReaderT)
import           Control.Monad.RWS.Strict    as X (MonadRWS (..), RWS, RWST,
                                                   runRWS, runRWST)
import           Control.Monad.State         as X (MonadState (..), State,
                                                   StateT, runState, runStateT)
import           Control.Monad.Writer.Strict as X (MonadWriter (..), Writer,
                                                   WriterT, runWriter,
                                                   runWriterT)

import qualified Control.Category

(>>>) :: (a -> b) -> (b -> c) -> a -> c
(>>>) = (Control.Category.>>>)
