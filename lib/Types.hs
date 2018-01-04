{-# LANGUAGE OverloadedStrings #-}
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
import           Data.Traversable
import           Control.Category hiding ((.))

newtype Var = Var Text
  deriving (Eq, Ord, Show)
newtype UnifVar = UnifVar Text
  deriving Show
newtype SkolVar = SkolVar { unSkol :: Text }
  deriving Show
data TyVar = Unif UnifVar | Skol SkolVar
  deriving Show

newtype DataCon = DataCon Text
  deriving (Eq, Ord, Show)
newtype TyCon = TyCon Text
  deriving Show

data PrimTy = PrimInt | PrimBool
  deriving Show

data Cst i = CstTriv | CstConj (Cst i) (Cst i) | CstEq (Mono i) (Mono i)
  deriving Show

newtype Prog i = Prog [Decl i]
  deriving Show
data Decl i = Decl Var (Exp i) | DeclAnn Var (Poly i) (Exp i)
  deriving Show

data Mono i
  = MonoVar TyVar
  | MonoPrim PrimTy
  | MonoList [Mono i]
  | MonoTyCon TyCon [Mono i]
  | MonoFun (Mono i) (Mono i)
  deriving Show

data Poly i = Forall [SkolVar] (Cst i) (Mono i)
  deriving Show

type Tau = Mono
type Sigma = Poly

data Sym i = SymCon DataCon | SymVar Var
  deriving (Eq, Ord, Show)
data Exp i = ESym (Sym i) | ELam Var (Exp i) | EApp (Exp i) (Exp i) | ECase (Exp i) [Alt i]
  deriving Show

-- pattern ECon con = ESym (SymCon con)
-- pattern EVar var = ESym (SymVar var)

data Alt i = Alt DataCon [Var] (Exp i)
  deriving Show

data AxiomSch i = AxiomTriv | AxiomConj (AxiomSch i) (AxiomSch i) | AxiomImp [SkolVar] (Cst i) (Cst i)
  deriving Show

-- |  TODO "type annotations are closed"
-- data TcData i = Ann (Sym i) (Poly i)

type Subst i = [(TyVar, Mono i)]
type Unifier i = [(UnifVar, Mono i)]
newtype GenCst i = GenCst (Cst i)
  deriving Show

--

fresh :: TcM i Int
fresh = do
  x <- gets supply
  modify (\t -> t { supply = x + 1 })
  pure x

freshUnif' :: TcM i TyVar
freshUnif' = freshUnif "u"

freshUnif :: Text -> TcM i TyVar
freshUnif t = do
  x <- fresh
  pure (Unif (UnifVar (t <> tshow x)))

data TcEnv i = TcEnv { bindings :: Map (Sym i) (Poly i), topLevelAxioms :: AxiomSch i }
type TcWriter i = ()
data TcState i = TcState { supply :: Int }

newtype TcM i a = TcM
  { unTcM :: RWST (TcEnv i) (TcWriter i) (TcState i) Identity a
  } deriving ( Functor
             , Applicative
             , Monad
             , MonadReader (TcEnv i)
             , MonadWriter (TcWriter i)
             , MonadState (TcState i)
             , MonadRWS (TcEnv i) (TcWriter i) (TcState i)
             )

simple :: GenCst i -> Cst i
simple (GenCst x) = x

freeUnifVars = undefined

instMono :: Subst i -> Mono i -> TcM i (Mono i)
instMono unif ty = pure ty

instCst :: Subst i -> Cst i -> TcM i (Cst i)
instCst unif cst = pure cst

poly :: Mono i -> Poly i
poly = Forall [] CstTriv

infixr /\
class Conj a where 
  (/\) :: a -> a -> a

instance Conj (Cst i) where (/\) = cstConj

cstConj :: Cst i -> Cst i -> Cst i
cstConj x CstTriv = x
cstConj CstTriv x = x
cstConj a b = CstConj a b

-- | sch; env |-> prog
wellTyped :: TcEnv i -> Prog i -> TcM i ()
wellTyped env prog = pure ()

tshow :: Show a => a -> Text
tshow = Text.pack . show

-- | Constraint generation
--
-- env |-> e : typ ~> gen
infer :: forall i . Exp i -> TcM i (Mono i, GenCst i)
infer (ESym sym) = do
  rhs <- asks (Map.lookup sym . bindings)
  case rhs of
    Nothing                  -> error "foo"
    Just (Forall as q1 tau1) -> do
      als <- for as $ \sk -> do
        ctr <- fresh
        pure (Skol sk, MonoVar (Unif (UnifVar (unSkol sk <> tshow ctr))))
      typ <- instMono als tau1
      gen <- instCst als q1
      pure (typ, GenCst gen)

infer (EApp e1 e2) = do
  (tau1, GenCst c1) <- infer e1
  (tau2, GenCst c2) <- infer e2
  alpha             <- MonoVar <$> freshUnif'
  let cst = c1 /\ c2 /\ CstEq tau1 (MonoFun tau2 alpha)
  pure (alpha, GenCst cst)

infer (ELam x e) = do
  alpha    <- MonoVar <$> freshUnif'
  (tau, c) <- local
    (\t -> t { bindings = Map.insert (SymVar x) (poly alpha) (bindings t) })
    (infer e)
  pure (MonoFun alpha tau, c)

infer e = pure (typ, gen)
 where
  typ = undefined
  gen = undefined

-- sch is given by the Reader environment.
-- sch; given |->simp wanted ~> residual; unifier
solve :: Cst i -> TcM i (Cst i, Cst i, Subst i)
solve given = pure (wanted, residual, unifier)
 where
  wanted   = undefined
  residual = undefined
  unifier  = undefined

runTcM :: TcEnv i -> TcState i -> TcM i a -> (a, TcState i, TcWriter i)
runTcM r s ma = runRWS (unTcM ma) r s

runTc :: TcM i a -> a
runTc ma = let (a, _, _) = runTcM initEnv initState ma in a
 where
  initEnv :: TcEnv i
  initEnv = TcEnv bd AxiomTriv
   where
    bd = Map.fromList
      [ (SymVar (Var "n"), Forall [] CstTriv (MonoPrim PrimInt))
      , ( SymVar (Var "id")
        , Forall [SkolVar "a"]
                 CstTriv
                 (MonoFun (MonoPrim PrimInt) (MonoPrim PrimInt))
        )
      ]

  initState :: TcState i
  initState = TcState 0

tests :: IO ()
tests = do
  print $ runTc $ infer (EApp (ESym (SymVar (Var "id"))) (ESym (SymVar (Var "n"))))
