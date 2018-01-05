{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Types where

import           Data.List.NonEmpty (NonEmpty)
import           Data.Text          (Text)
import qualified Data.Text          as Text

-- Names
newtype Var =
  Var Text
  deriving (Eq, Ord, Show)

newtype UnifVar =
  UnifVar Text
  deriving (Eq)

newtype SkolVar =
  SkolVar Text
  deriving (Eq)

newtype DataCon =
  DataCon Text
  deriving (Eq, Ord, Show)

newtype TyCon =
  TyCon Text
  deriving (Eq, Show)

data TyVar
  = Unif UnifVar
  | Skol SkolVar
  deriving (Eq)

data Sym
  = SymCon DataCon
  | SymVar Var
  deriving (Eq, Ord, Show)

-- | Primitive types.
data PrimTy
  = PrimInt
  | PrimBool
  deriving (Show, Eq)

data Ct
  = CtTriv
  | CtConj Ct
           Ct
  | CtEq Mono
         Mono
  deriving (Eq)

newtype Prog =
  Prog [Decl]
  deriving (Show)

data Decl
  = Decl Var
         Exp
  | DeclAnn Var
            Poly
            Exp
  deriving (Show)

data Mono
  = MonoVar TyVar
  | MonoPrim PrimTy
  | MonoList [Mono]
  | MonoConApp TyCon
               [Mono]
  | MonoFun Mono
            Mono
  deriving (Eq)

data Poly =
  Forall [SkolVar]
         Ct
         Mono
  deriving (Show)

type Tau = Mono

type Sigma = Poly

data Exp
  = ESym Sym
  | ELam Var
         Exp
  | EApp Exp
         Exp
  | ECase Exp
          (NonEmpty Alt)
  deriving (Show)

data Alt =
  Alt DataCon
      [Var]
      Exp
  deriving (Show)

data AxiomSch
  = AxiomTriv
  | AxiomConj AxiomSch
              AxiomSch
  | AxiomImp [SkolVar]
             Ct
             Ct
  deriving (Show)

type Subst = [(TyVar, Mono)]

type Unifier = [(UnifVar, Mono)]

newtype GenCt =
  GenCt Ct
  deriving (Show)

instance Show UnifVar where
  showsPrec n (UnifVar v) = showString (Text.unpack v)

instance Show SkolVar where
  showsPrec n (SkolVar v) = showString (Text.unpack v)

instance Show TyVar where
  showsPrec n (Unif v) = showsPrec n v
  showsPrec n (Skol v) = showsPrec n v

instance Show Ct where
  showsPrec _ CtTriv = shows ()
  showsPrec n (CtConj l r) = showsPrec n l . showString " /\\ " . showsPrec n r
  showsPrec n (CtEq l r) =
    showParen (n > 9) (showsPrec 9 l . showString " ~ " . showsPrec 9 r)

instance Show Mono where
  showsPrec n (MonoVar v) = showsPrec n v
  showsPrec n (MonoPrim p) = showsPrec n p
  showsPrec n (MonoList ms) = showList ms
  showsPrec n (MonoConApp (TyCon con) ms) =
    showString (Text.unpack con) . showList ms
  showsPrec n (MonoFun l r) =
    showParen (n > 0) (showsPrec 1 l . showString " -> " . shows r)
