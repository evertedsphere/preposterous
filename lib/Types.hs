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
import Debug.Trace as Trace

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
  deriving Show

data Ct i = CtTriv | CtConj (Ct i) (Ct i) | CtEq (Mono i) (Mono i)
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


--

fresh :: TcM i Int
fresh = do
  x <- gets supply
  modify (\t -> t { supply = x + 1 })
  pure x

freshUnif :: TcM i TyVar
freshUnif = freshUnifHint "u"

freshUnifHint :: Text -> TcM i TyVar
freshUnifHint t = do
  x <- fresh
  pure (Unif (UnifVar (t <> tshow x)))

freshMono :: TcM i (Mono i)
freshMono = MonoVar <$> freshUnif

data TcEnv i = TcEnv { bindings :: Map (Sym i) (Poly i), topLevelAxioms :: AxiomSch i }
type TcWriter i = ()
data TcState i = TcState { supply :: Int }

data TcErr
  = ErrText Text
  deriving Show

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

simple :: GenCt i -> Ct i
simple (GenCt x) = x

freeUnifVars = undefined

instMono :: forall i . Subst i -> Mono i -> TcM i (Mono i)
instMono unif ty = foldM (\t (v, r) -> instMono1 v r t) ty unif

instMono1 :: TyVar -> Mono i -> Mono i -> TcM i (Mono i)
instMono1 v r ty = case ty of
  MonoVar v'        -> pure $ if v == v' then r else ty
  MonoPrim{}        -> pure ty
  MonoList ms       -> MonoList <$> traverse (instMono1 v r) ms
  MonoConApp con ms -> MonoConApp con <$> traverse (instMono1 v r) ms
  MonoFun    x   y  -> MonoFun <$> instMono1 v r x <*> instMono1 v r y

instCt :: Subst i -> Ct i -> TcM i (Ct i)
instCt unif cst = foldM (\c (v, r) -> instCt1 v r c) cst unif
 where
  instCt1 v r ct = case ct of
    CtTriv     -> pure ct
    CtConj x y -> CtConj <$> instCt1 v r x <*> instCt1 v r y
    CtEq   m n -> CtEq <$> instMono1 v r m <*> instMono1 v r n



poly :: Mono i -> Poly i
poly = Forall [] CtTriv

infixr /\
class Conj a where
  (/\) :: a -> a -> a

instance Conj (Ct i) where (/\) = cstConj

cstConj :: Ct i -> Ct i -> Ct i
cstConj x      CtTriv = x
cstConj CtTriv x      = x
cstConj a      b      = CtConj a b

-- | [sch]; [env] |-> prog
wellTyped :: Prog i -> TcM i ()
wellTyped prog = pure ()

tshow :: Show a => a -> Text
tshow = Text.pack . show

-- | Constraint generation
--
-- [env] |-> e : typ ~> gen
infer :: forall i . Exp i -> TcM i (Mono i, GenCt i)
infer (ESym sym) = do
  rhs <- asks (Map.lookup sym . bindings)
  case rhs of
    Nothing                  -> throwError (ErrText "Unknown symbol")
    Just (Forall as q1 tau1) -> do
      als <- for as $ \sk -> do
        ctr <- fresh
        let SkolVar v = sk
        pure (Skol sk, MonoVar (Unif (UnifVar (v <> tshow ctr))))
      typ <- instMono als tau1
      gen <- instCt als q1
      pure (typ, GenCt gen)

infer (EApp e1 e2) = do
  (tau1, GenCt c1) <- infer e1
  (tau2, GenCt c2) <- infer e2
  alpha            <- freshMono
  let cst = c1 /\ c2 /\ CtEq tau1 (MonoFun tau2 alpha)
  pure (alpha, GenCt cst)

infer (ELam x e) = do
  alpha    <- freshMono
  (tau, c) <- local
    (\t -> t { bindings = Map.insert (SymVar x) (poly alpha) (bindings t) })
    (infer e)
  pure (MonoFun alpha tau, c)

infer (ECase e alts@(Alt dcon vs _:|_)) = do
  (tau, GenCt c) <- infer e

  beta           <- freshMono

  rhs            <- asks (Map.lookup (SymCon dcon) . bindings)
  Forall _ _ ty  <- unwrap rhs (ErrText "nonexistent data constructor")
  (_, tycon, as) <- unwrap (toTyCon ty) (ErrText "not a data constructor!")
  let num_gamma = length as
  gamma <- replicateM num_gamma freshMono

  let c' = CtEq (MonoConApp tycon gamma) tau /\ c
  let go :: Ct i -> Alt i -> TcM i (Ct i)
      go ct_prev (Alt k_i xs_i e_i) = do
        Forall as_i _q_i fn <-
          asks (Map.lookup (SymCon k_i) . bindings)
            >>= (`unwrap` ErrText "Unknown data-constructor in case")
        (vs_i, tycon', _) <- unwrap (toTyCon fn) (ErrText "???")
        assert
          (tycon == tycon')
          (ErrText "Datacon in match different from head con of expression")
        let sub   = zipWith (\a g -> (Skol a, g)) as_i gamma
            xvs_i = zip xs_i vs_i
        bds <- for xvs_i $ \(x, v) -> do
          v' <- instMono sub v
          pure (SymVar x, poly v')

        (tau_i, GenCt ct_i) <- local
          (\t -> t { bindings = Map.union (Map.fromList bds) (bindings t) })
          (infer e_i)
        let ct_new = ct_prev /\ CtEq beta tau_i
        pure ct_new
  ct <- foldM go c' alts
  pure (beta, GenCt ct)

unwrap :: Maybe a -> TcErr -> TcM i a
unwrap ma err = maybe (throwError err) pure ma

assert :: Bool -> TcErr -> TcM i ()
assert cond = unless cond . throwError

toTyCon :: Mono i -> Maybe ([Mono i], TyCon, [Mono i])
toTyCon = go []
 where
  go xs (MonoFun l r) = do
    (xs', con, as) <- go xs r
    pure (l : xs', con, as)
  go xs (MonoConApp con as) = pure ([], con, as)

getTy :: Mono i -> Maybe (Mono i)
getTy m = case m of
  MonoFun _ r  -> getTy r
  MonoConApp{} -> pure m
  _            -> Nothing

getTyCon :: Mono i -> Maybe TyCon
getTyCon = \case
  MonoFun    _   r -> getTyCon r
  MonoConApp con _ -> pure con
  _                -> Nothing

-- sch is given by the Reader environment.
-- [sch]; given |->simp wanted ~> residual; unifier
solve :: Ct i -> TcM i (Ct i, Ct i, Subst i)
solve given = pure (wanted, residual, unifier)
 where
  wanted   = undefined
  residual = undefined
  unifier  = undefined

runTcM
  :: TcEnv i -> TcState i -> TcM i a -> (Either TcErr a, TcState i, TcWriter i)
runTcM r s ma = runRWS (runExceptT (unTcM ma)) r s

runTc :: TcM i a -> Either TcErr a
runTc ma = let (a, _, _) = runTcM initEnv initState ma in a
 where
  initEnv :: TcEnv i
  initEnv = TcEnv bd AxiomTriv
   where
    bd = Map.fromList
      [ (SymVar (Var "n"), Forall [] CtTriv (MonoPrim PrimInt))
      , ( SymVar (Var "idint")
        , Forall [] CtTriv (MonoFun (MonoPrim PrimInt) (MonoPrim PrimInt))
        )
      , ( SymVar (Var "id")
        , Forall
          [SkolVar "t"]
          CtTriv
          ( MonoFun (MonoVar (Skol (SkolVar "t")))
                    (MonoVar (Skol (SkolVar "t")))
          )
        )
      , ( SymCon (DataCon "MkIntWrap")
        , Forall
          []
          CtTriv
          (MonoFun (MonoPrim PrimInt) (MonoConApp (TyCon "IntWrap") []))
        )
      , (SymVar (Var "w"), poly (MonoConApp (TyCon "IntWrap") []))
      , ( SymCon (DataCon "MkPair")
        , Forall
          [ska, skb]
          CtTriv
          (MonoFun mska (MonoFun mskb (MonoConApp (TyCon "Pair") [mska, mskb])))
        )
      , scon "Nothing" (Forall [ska] CtTriv (MonoConApp (TyCon "Maybe") [mska]))
      , scon
        "Just"
        (Forall [ska] CtTriv (MonoFun mska (MonoConApp (TyCon "Maybe") [mska])))
      ]
    svar x rhs = (SymVar (Var x), rhs)
    scon x rhs = (SymCon (DataCon x), rhs)
    ska  = SkolVar "a"
    mska = MonoVar (Skol ska)
    skb  = SkolVar "b"
    mskb = MonoVar (Skol skb)

  initState :: TcState i
  initState = TcState 0

tests :: IO ()
tests = do
  putStrLn "\nidint n"
  print $ runTc $ infer (EApp (evar "idint") (evar "n"))

  putStrLn "\nid"
  print $ runTc $ infer (evar "id")

  putStrLn "\n\\x -> id x"
  print $ runTc $ infer (ELam (Var "x") (EApp (evar "id") (evar "x")))

  putStrLn "\nidint"
  print $ runTc $ infer (evar "idint")

  putStrLn "\n\\x -> idint x"
  print $ runTc $ infer (ELam (Var "x") (EApp (evar "idint") (evar "x")))

  putStrLn "\ncase w of MkIntWrap x -> x"
  print $ runTc $ infer $ ECase (evar "w")
                                (Alt (DataCon "MkIntWrap") [Var "x"] x :| [])

  putStrLn "\ncase w of MkIntWrap x -> MkIntWrap x"
  print $ runTc $ infer $ ECase
    (evar "w")
    (  Alt (DataCon "MkIntWrap")
           [Var "x"]
           (EApp (ESym (SymCon (DataCon "MkIntWrap"))) x)
    :| []
    )

  putStrLn "\nid id"
  print $ runTc $ infer (EApp (evar "id") (evar "id"))

  putStrLn "\nid \\x -> x"
  print $ runTc $ infer (EApp (evar "id") (ELam (var "x") x))

  putStrLn "\n(\\x -> x) (\\x -> x)"
  print $ runTc $ infer (EApp (ELam (var "x") x) (ELam (var "x") x))

  putStrLn "\n(\\x -> x) (\\y -> y)"
  print $ runTc $ infer (EApp (ELam (var "x") x) (ELam (var "y") y))

  putStrLn "\nMkPair"
  print $ runTc $ infer (econ "MkPair")

  putStrLn "\nMkPair n"
  print $ runTc $ infer (EApp (econ "MkPair") (evar "n"))

  putStrLn "\nNonExistentCon"
  print $ runTc $ infer (econ "NonExistentCon")

  putStrLn "\nid (MkPair MkPair MkPair)"
  print $ runTc $ infer
    ( EApp (evar "id")
           (EApp (econ "MkPair") (EApp (econ "MkPair") (econ "MkPair")))
    )

  putStrLn "\n\\def -> \\ma -> case ma of Nothing -> def; Just x -> x"
  print $ runTc $ infer
    ( ELam
      (var "def")
      ( ELam
        (var "ma")
        ( ECase
          (evar "ma")
          (  Alt (DataCon "Nothing") [] (evar "def")
          :| [Alt (DataCon "Just") [var "x"] (evar "x")]
          )
        )
      )
    )

  putStrLn "\n\\def -> \\ma -> case ma of Just x -> x; Nothing -> def"
  print $ runTc $ infer
    ( ELam
      (var "def")
      ( ELam
        (var "ma")
        ( ECase
          (evar "ma")
          (  Alt (DataCon "Nothing") [] (evar "def")
          :| [Alt (DataCon "Just") [var "x"] (evar "x")]
          )
        )
      )
    )
 where
  var  = Var
  evar = ESym . SymVar . Var
  econ = ESym . SymCon . DataCon
  n    = evar "n"
  x    = evar "x"
  y    = evar "y"
