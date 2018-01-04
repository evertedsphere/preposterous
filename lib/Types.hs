module Types where

import Data.Text (Text)

newtype TmVar = TmVar Text
newtype TyVar = TyVar Text
newtype DataCon = DataCon Text

newtype Prog = Prog [Decl]
data Decl = Decl TmVar Exp | DeclAnn TmVar Poly Exp
data Cond = CondTriv | CondConj Cond Cond | CondEq Mono Mono
data Mono 
data Poly = Forall [TyVar] Cond Mono
data Sym = SymCon DataCon | SymVar TmVar
data Exp = EVar TmVar | ECon DataCon | ELam TmVar Exp | EApp Exp Exp | ECase Exp [Alt]
data Alt = Alt DataCon [TmVar] Exp

data AxSch = AxiomTriv | AxiomConj AxSch AxSch | AxiomImp [TyVar] Cond Cond
