{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Inference.Engine where

import           Control.Monad.Except
import           Control.Monad.RWS.Strict hiding (Alt (..))
import           Data.List.NonEmpty       (NonEmpty (..))
import qualified Data.Map                 as Map
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           Data.Traversable
import Data.Foldable
import Control.Lens

import           Inference.Monad
import           Types

fresh :: TcM Int
fresh = do
  x <- use supply
  supply += 1
  pure x

freshUnifVarHint :: Text -> TcM UnifVar
freshUnifVarHint t = do
  x <- fresh
  pure (UnifVar (t <> tshow x))

freshUnif :: TcM TyVar
freshUnif = freshUnifHint "u"

freshSkol :: Text -> TcM SkolVar
freshSkol t = do
  x <- fresh
  pure (SkolVar (t <> tshow x))

freshUnifHint :: Text -> TcM TyVar
freshUnifHint t = do
  x <- fresh
  pure (Unif (UnifVar (t <> tshow x)))

freshMono :: TcM Mono
freshMono = MonoVar <$> freshUnif

simpleCt :: GenCt -> [Ct]
simpleCt = \case
  GenImplic{} -> [CtTriv]
  GenSimp x   -> [x]
  GenConj l r -> simpleCt l ++ simpleCt r

implicationCt :: GenCt -> [GenCt]
implicationCt ct = case ct of
  GenImplic{} -> [ct]
  GenSimp{}   -> [GenSimp CtTriv]
  GenConj l r -> implicationCt l ++ implicationCt r

instMono :: Subst -> Mono -> TcM Mono
instMono unif ty = foldM (\t (v, r) -> instMono1 v r t) ty unif

instMono1 :: TyVar -> Mono -> Mono -> TcM Mono
instMono1 v r ty = case ty of
  MonoVar v'        -> pure $ if v == v' then r else ty
  MonoPrim{}        -> pure ty
  MonoList ms       -> MonoList <$> traverse (instMono1 v r) ms
  MonoConApp con ms -> MonoConApp con <$> traverse (instMono1 v r) ms
  MonoFun    x   y  -> MonoFun <$> instMono1 v r x <*> instMono1 v r y

instCt :: Subst -> Ct -> TcM Ct
instCt unif cst = foldM (\c (v, r) -> instCt1 v r c) cst unif
 where
  instCt1 v r ct = case ct of
    CtTriv     -> pure ct
    CtConj x y -> CtConj <$> instCt1 v r x <*> instCt1 v r y
    CtEq   m n -> CtEq <$> instMono1 v r m <*> instMono1 v r n

-- TODO check als # fuv(theta)? even though the paper says
-- the "side-condition is not significant algorithmically"
instGenCt :: Subst -> GenCt -> TcM GenCt
instGenCt theta = \case
  GenSimp ct        -> GenSimp <$> instCt theta ct
  GenConj l r       -> GenConj <$> instGenCt theta l <*> instGenCt theta r
  GenImplic als q c -> GenImplic als <$> instCt theta q <*> instGenCt theta c

poly :: Mono -> Poly
poly = Forall [] CtTriv

infixr /\
class Conj a where
  (/\) :: a -> a -> a

instance Conj Ct where
  x      /\ CtTriv = x
  CtTriv /\ x      = x
  a      /\ b      = CtConj a b

instance Conj GenCt where
  GenSimp x      /\ GenSimp y      = GenSimp (x /\ y)
  x              /\ GenSimp CtTriv = x
  GenSimp CtTriv /\ x              = x
  a              /\ b              = GenConj a b

tshow :: Show a => a -> Text
tshow = Text.pack . show

-- | Constraint generation
--
-- [env] |-> e : typ ~> gen
infer :: Exp -> TcM (Mono, GenCt)
infer (ESym sym) = do
  rhs <- views bindings (Map.lookup sym)
  case rhs of
    Nothing                  -> throwError (ErrText "Unknown symbol")
    Just (Forall as q1 tau1) -> do
      als <- for as $ \sk -> do
        ctr <- fresh
        let SkolVar v = sk
        pure (Skol sk, MonoVar (Unif (UnifVar (v <> tshow ctr))))
      typ <- instMono als tau1
      gen <- instCt als q1
      pure (typ, GenSimp gen)

infer (EApp e1 e2) = do
  (tau1, GenSimp c1) <- infer e1
  (tau2, GenSimp c2) <- infer e2
  alpha              <- freshMono
  let cst = c1 /\ c2 /\ CtEq tau1 (MonoFun tau2 alpha)
  pure (alpha, GenSimp cst)

infer (ELam x e) = do
  alpha    <- freshMono
  (tau, c) <- local (bindings %~ Map.insert (SymVar x) (poly alpha)) (infer e)
  pure (MonoFun alpha tau, c)

infer (ECase e alts@(Alt dcon vs _:|_)) = do
  (tau, GenSimp c) <- infer e
  beta             <- freshMono
  rhs              <- views bindings (Map.lookup (SymCon dcon))
  Forall _ _ ty    <- unwrap rhs (ErrText "nonexistent data constructor")
  (_, tycon, as)   <- unwrap (toTConName ty) (ErrText "not a data constructor!")
  let num_gamma = length as
  gamma <- replicateM num_gamma freshMono

  let c' = CtEq (MonoConApp tycon gamma) tau /\ c
  let go :: Ct -> Alt -> TcM Ct
      go ct_prev (Alt k_i xs_i e_i) = do
        Forall as_i _q_i fn <-
          views bindings (Map.lookup (SymCon k_i))
            >>= (`unwrap` ErrText "Unknown data-constructor in case")
        (vs_i, tycon', _) <- unwrap (toTConName fn) (ErrText "???")
        assert
          (tycon == tycon')
          (ErrText "Datacon in match different from head con of expression")
        let sub   = zipWith (\a g -> (Skol a, g)) as_i gamma
            xvs_i = zip xs_i vs_i
        bds <- for xvs_i $ \(x, v) -> do
          v' <- instMono sub v
          pure (SymVar x, poly v')

        (tau_i, GenSimp ct_i) <- local
          (bindings %~ Map.union (Map.fromList bds))
          (infer e_i)
        let ct_new = ct_prev /\ CtEq beta tau_i
        pure ct_new
  ct <- foldM go c' alts
  pure (beta, GenSimp ct)

unwrap :: Maybe a -> TcErr -> TcM a
unwrap ma err = maybe (throwError err) pure ma

assert :: Bool -> TcErr -> TcM ()
assert cond = unless cond . throwError

toTConName :: Mono -> Maybe ([Mono], TConName, [Mono])
toTConName = go []
 where
  go xs (MonoFun l r) = do
    (xs', con, as) <- go xs r
    pure (l : xs', con, as)
  go xs (MonoConApp con as) = pure ([], con, as)

getTy :: Mono -> Maybe Mono
getTy m = case m of
  MonoFun _ r  -> getTy r
  MonoConApp{} -> pure m
  _            -> Nothing

getTConName :: Mono -> Maybe TConName
getTConName = \case
  MonoFun    _   r -> getTConName r
  MonoConApp con _ -> pure con
  _                -> Nothing

fuvMono :: Mono -> TcM [UnifVar]
fuvMono m = case m of
  MonoVar (Unif v) -> pure [v]
  MonoVar _        -> pure []
  MonoPrim{}       -> pure []
  MonoFun    l r   -> (++) <$> fuvMono l <*> fuvMono r
  MonoConApp _ ms  -> concat <$> traverse fuvMono ms
  MonoList ms      -> concat <$> traverse fuvMono ms

fuvCt :: Ct -> TcM [UnifVar]
fuvCt ct = case ct of
  CtTriv     -> pure []
  CtConj l r -> (++) <$> fuvCt l <*> fuvCt r
  CtEq   l r -> (++) <$> fuvMono l <*> fuvMono r

-- | fuv(T,C)
fuvIn :: Mono -> GenCt -> TcM [UnifVar]
fuvIn = undefined

-- | [sch]; [env] |-> prog
wellTyped :: Prog -> TcM ()
wellTyped (Prog []      ) = pure ()
wellTyped (Prog (d:prog)) = go d
 where
  go (DeclAnn f p@(Forall as q tau) e) = do
    (v, q_wanted)     <- infer e
    fuvs              <- fuvIn v q_wanted
    (residual, theta) <- solve q fuvs (q_wanted /\ GenSimp (CtEq v tau))
    assert (residual == CtTriv) (ErrText "residual constraints")
    local (bindings %~ Map.insert (SymVar f) p) (wellTyped (Prog prog))
  go (Decl f e) = do
    (tau, q_wanted) <- infer e
    fuvs            <- fuvIn tau q_wanted
    (q, theta)      <- solve CtTriv fuvs q_wanted
    tau'            <- instMono theta tau
    ty              <- do
      fuv1 <- fuvMono tau'
      fuv2 <- fuvCt q
      let als = fuv1 ++ fuv2
      as <- replicateM (length als) (freshSkol "sk")
      let sub = zipWith (\al a -> (Unif al, MonoVar (Skol a))) als as
      Forall as <$> instCt sub q <*> instMono sub tau'
    local (bindings %~ Map.insert (SymVar f) ty) (wellTyped (Prog prog))

-- sch is given by the Reader environment.
-- [sch]; given |->solv wanted ~> residual; unifier
solve :: Ct -> [UnifVar] -> GenCt -> TcM (Ct, Subst)
solve q_given als_tch c_wanted = do
  let simple = simpleCt c_wanted
  (q_residual, theta) <- simplify q_given als_tch (foldr (/\) CtTriv simple)
  implics             <- implicationCt <$> instGenCt theta c_wanted
  for_ implics $ \(GenImplic als_i q_i c_i) -> do
    (q_residual', _theta_i) <- solve (q_given /\ q_residual /\ q_i) als_tch c_i
    assert (q_residual' == CtTriv) (ErrText "solve: residual constraints")
  pure (q_residual, theta)

simplify :: Ct -> [UnifVar] -> Ct -> TcM (Ct, Subst)
simplify q_given als_tch q_wanted = pure (q_residual, theta)
 where
  q_residual = undefined
  theta      = undefined

runTcM :: TcEnv -> TcState -> TcM a -> (Either TcErr a, TcState, TcWriter)
runTcM r s ma = runRWS (runExceptT (unTcM ma)) r s

runTc :: TcM a -> Either TcErr a
runTc ma = let (a, _, _) = runTcM initEnv initState ma in a
 where
  initEnv :: TcEnv
  initEnv = TcEnv bd AxTriv
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
      , ( SymCon (DConName "MkIntWrap")
        , Forall
          []
          CtTriv
          (MonoFun (MonoPrim PrimInt) (MonoConApp (TConName "IntWrap") []))
        )
      , (SymVar (Var "w"), poly (MonoConApp (TConName "IntWrap") []))
      , ( SymCon (DConName "MkPair")
        , Forall
          [ska, skb]
          CtTriv
          ( MonoFun mska
                    (MonoFun mskb (MonoConApp (TConName "Pair") [mska, mskb]))
          )
        )
      , scon "Nothing"
             (Forall [ska] CtTriv (MonoConApp (TConName "Maybe") [mska]))
      , scon
        "Just"
        ( Forall [ska]
                 CtTriv
                 (MonoFun mska (MonoConApp (TConName "Maybe") [mska]))
        )
      ]
    svar x rhs = (SymVar (Var x), rhs)
    scon x rhs = (SymCon (DConName x), rhs)
    ska  = SkolVar "a"
    mska = MonoVar (Skol ska)
    skb  = SkolVar "b"
    mskb = MonoVar (Skol skb)

  initState :: TcState
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
                                (Alt (DConName "MkIntWrap") [Var "x"] x :| [])

  putStrLn "\ncase w of MkIntWrap x -> MkIntWrap x"
  print $ runTc $ infer $ ECase
    (evar "w")
    (  Alt (DConName "MkIntWrap")
           [Var "x"]
           (EApp (ESym (SymCon (DConName "MkIntWrap"))) x)
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
  putStrLn "\n\\def -> \\ma -> case ma of Just x -> x; Nothing -> def"
  print $ runTc $ infer
    ( ELam
      (var "def")
      ( ELam
        (var "ma")
        ( ECase
          (evar "ma")
          (  Alt (DConName "Nothing") [] (evar "def")
          :| [Alt (DConName "Just") [var "x"] (evar "x")]
          )
        )
      )
    )

  let bdFromMaybe = ELam
        (var "def")
        ( ELam
          (var "ma")
          ( ECase
            (evar "ma")
            (  Alt (DConName "Nothing") [] (evar "def")
            :| [Alt (DConName "Just") [var "x"] (evar "x")]
            )
          )
        )
  putStrLn "\n\\def -> \\ma -> case ma of Nothing -> def; Just x -> x"
  print $ runTc $ infer bdFromMaybe
 where
  var  = Var
  evar = ESym . SymVar . Var
  econ = ESym . SymCon . DConName
  n    = evar "n"
  x    = evar "x"
  y    = evar "y"
