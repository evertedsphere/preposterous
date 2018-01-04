{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Types where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.IO.Class
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.Set                 (Set)
import           Data.Map                 (Map)
import qualified Data.Set                 as Set
import qualified Data.Map                 as Map
import qualified Data.Text                as Text
import           Data.Text                (Text)
import           Data.Maybe
import           Data.Traversable
import           Control.Category ((>>>),(<<<))
import           Data.List.NonEmpty (NonEmpty(..), (!!), nonEmpty)

-- Names

newtype Var = Var Text deriving (Eq, Ord, Show)
newtype UnifVar = UnifVar Text deriving (Eq)
newtype SkolVar = SkolVar Text deriving (Eq)

newtype DataCon = DataCon Text deriving (Eq, Ord, Show)
newtype TyCon = TyCon Text deriving (Eq,Show)

data TyVar = Unif UnifVar | Skol SkolVar deriving (Eq)

data Sym i = SymCon DataCon | SymVar Var deriving (Eq, Ord, Show)

-- | Primitive types.
data PrimTy = PrimInt | PrimBool
  deriving (Show,Eq)

data Ct i = CtTriv | CtConj (Ct i) (Ct i) | CtEq (Mono i) (Mono i)
  deriving (Eq)
newtype Prog i = Prog [Decl i]
  deriving Show
data Decl i = Decl Var (Exp i) | DeclAnn Var (Poly i) (Exp i)
  deriving Show

data Mono i
  = MonoVar TyVar
  | MonoPrim PrimTy
  | MonoList [Mono i]
  | MonoConApp TyCon [Mono i]
  | MonoFun (Mono i) (Mono i)
  deriving (Eq)

data Poly i = Forall [SkolVar] (Ct i) (Mono i)
  deriving Show

type Tau = Mono
type Sigma = Poly
data Exp i = ESym (Sym i) | ELam Var (Exp i) | EApp (Exp i) (Exp i) | ECase (Exp i) (NonEmpty (Alt i))
  deriving Show

-- pattern ECon con = ESym (SymCon con)
-- pattern EVar var = ESym (SymVar var)

data Alt i = Alt DataCon [Var] (Exp i)
  deriving Show

data AxiomSch i = AxiomTriv | AxiomConj (AxiomSch i) (AxiomSch i) | AxiomImp [SkolVar] (Ct i) (Ct i)
  deriving Show

type Subst i = [(TyVar, Mono i)]
type Unifier i = [(UnifVar, Mono i)]
newtype GenCt i = GenCt (Ct i)
  deriving Show

instance Show UnifVar where showsPrec n (UnifVar v) = showString (Text.unpack v)
instance Show SkolVar where showsPrec n (SkolVar v) = showString (Text.unpack v)

instance Show TyVar where
  showsPrec n (Unif v) = showsPrec n v
  showsPrec n (Skol v) = showsPrec n v

instance Show (Ct i) where
  showsPrec _ CtTriv = shows ()
  showsPrec n (CtConj l r) = showsPrec n l . showString " /\\ " . showsPrec n r
  showsPrec n (CtEq l r) = showParen (n > 9) (showsPrec 9 l . showString " ~ " . showsPrec 9 r)

instance Show (Mono i) where
  showsPrec n (MonoVar v) = showsPrec n v
  showsPrec n (MonoPrim p) = showsPrec n p
  showsPrec n (MonoList ms) = showList ms
  showsPrec n (MonoConApp (TyCon con) ms) = showString (Text.unpack con) . showList ms
  showsPrec n (MonoFun l r) = showParen (n > 0) (showsPrec 1 l . showString " -> " . shows r)

