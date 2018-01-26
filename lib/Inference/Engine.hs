{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Inference.Engine where

import           Control.Lens    hiding (rewrite)
import qualified Data.Map        as Map
import qualified Data.Text       as Text

import           Eval.Monad
import           Inference.Monad
import           Types

import           Praeludium

instance Semigroup Ct where
  a      <> b      = CtConj a b

instance Semigroup GenCt where
  a              <> b              = GenConj a b

instance Monoid Ct where
  mempty = CtTriv
  mappend = (<>)

instance Monoid GenCt where
  mempty = GenSimp mempty
  mappend = (<>)

failWith :: TcErr -> TcM a
failWith e = throwError [e]

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
  GenSimp{}   -> [mempty]
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

tshow :: Show a => a -> Text
tshow = Text.pack . show

fuvEnv :: TcM [UnifVar]
fuvEnv = do
  env <- view bindingTypes
  unsupported

infer :: Exp -> TcM (Mono, GenCt)
infer e = recur (infer' e)

-- | Constraint generation
--
-- [env] |-> e : typ ~> gen
infer' :: Exp -> TcM (Mono, GenCt)
infer' (EPrimOp PrimAdd) = pure (MonoFun i (MonoFun i i), mempty)
  where i = MonoPrim PrimInt
-- FIXME run this by someone who Knows Things
infer' (EPrim v) = do
  logText "EPrim"
  let typ = case v of
        EInt{}  -> PrimInt
        EBool{} -> PrimBool

  pure (MonoPrim typ, mempty)

infer' (ESym sym) = do
  logText "VarCon"
  rhs <- views bindingTypes (Map.lookup sym)
  case rhs of
    Nothing                  -> failWith (ErrText "Unknown symbol")
    Just (Forall as q1 tau1) -> do
      als <- for as $ \sk -> do
        ctr <- fresh
        let SkolVar v = sk
        pure (Skol sk, MonoVar (Unif (UnifVar (v <> tshow ctr))))
      typ <- instMono als tau1
      gen <- instCt als q1
      pure (typ, GenSimp gen)

infer' (EApp e1 e2) = do
  logText "App"
  (tau1, GenSimp c1) <- infer e1
  (tau2, GenSimp c2) <- infer e2
  alpha              <- freshMono
  let cst = c1 <> c2 <> CtEq tau1 (MonoFun tau2 alpha)
  pure (alpha, GenSimp cst)

infer' (ELam x e) = do
  logText "Abs"
  alpha    <- freshMono
  (tau, c) <- local (bindingTypes %~ Map.insert (SymVar x) (poly alpha)) (infer e)
  pure (MonoFun alpha tau, c)

infer' (ELet x e1 e2) = do
  logText "Let"
  (tau1, c1) <- infer e1
  (tau2, c2) <- local (bindingTypes %~ Map.insert (SymVar x) (poly tau1)) (infer e2)
  pure (tau2, c1 <> c2)

infer' (EAnnLet x (Forall [] CtTriv tau1) e1 e2) = do
  logText "LetA"
  (tau, c1) <- infer e1
  (tau2, c2) <- local (bindingTypes %~ Map.insert (SymVar x) (poly tau1)) (infer e2)
  pure (tau2, c1 <> c2 <> GenSimp (CtEq tau tau1))

infer' (EAnnLet x _sigma1@(Forall as q1 tau1) e1 e2) = do
  logText "GLetA"
  assert (q1 /= CtTriv || as /= []) (ErrText "GLetA: both empty")
  (tau, c) <- infer e1
  betas <- do
    fuvtc <- fuvIn tau c
    fuvg <- fuvEnv
    pure (filter (`notElem` fuvg) fuvtc)
  let c1 = GenImplic betas q1 (c <> GenSimp (CtEq tau tau1))
  (tau2, c2) <- local (bindingTypes %~ Map.insert (SymVar x) (poly tau1)) (infer e2)
  pure (tau2, c1 <> c2)

infer' (ECase e alts@(Alt dcon vs _:|_)) = do
  logText "Case"
  (tau, GenSimp c) <- infer e
  beta             <- freshMono
  rhs              <- views bindingTypes (Map.lookup (SymCon dcon))
  Forall _ _ ty    <- unwrap rhs (ErrText "nonexistent data constructor")
  (_, tycon, as)   <- unwrap (toTConName ty) (ErrText "not a data constructor!")
  let num_gamma = length as
  gamma <- replicateM num_gamma freshMono

  let c' = CtEq (MonoConApp tycon gamma) tau <> c
  let go :: Ct -> Alt -> TcM Ct
      go ct_prev (Alt k_i xs_i e_i) = do
        Forall as_i _q_i fn <-
          views bindingTypes (Map.lookup (SymCon k_i))
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
          (bindingTypes %~ Map.union (Map.fromList bds))
          (infer e_i)
        let ct_new = ct_prev <> CtEq beta tau_i
        pure ct_new
  ct <- foldM go c' alts
  pure (beta, GenSimp ct)

unwrap :: Maybe a -> TcErr -> TcM a
unwrap ma err = maybe (failWith err) pure ma

assert :: Bool -> TcErr -> TcM ()
assert cond = unless cond . failWith

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
fuvMono = \case
  MonoVar (Unif v) -> pure [v]
  MonoVar _        -> pure []
  MonoPrim{}       -> pure []
  MonoFun    l r   -> (++) <$> fuvMono l <*> fuvMono r
  MonoConApp _ ms  -> concat <$> traverse fuvMono ms
  MonoList ms      -> concat <$> traverse fuvMono ms

fuvCt :: Ct -> TcM [UnifVar]
fuvCt = \case
  CtTriv     -> pure []
  CtConj l r -> (++) <$> fuvCt l <*> fuvCt r
  CtEq   l r -> (++) <$> fuvMono l <*> fuvMono r

fuvGenCt :: GenCt -> TcM [UnifVar]
fuvGenCt = \case
  GenSimp ct       -> fuvCt ct
  GenConj l r      -> (++) <$> fuvGenCt l <*> fuvGenCt r
  GenImplic uv q c -> do
    fuvq <- fuvCt q
    fuvc <- fuvGenCt c
    pure (uv ++ fuvq ++ fuvc)


-- | fuv(T,C) = fuv(T) U fuv(C), for now
fuvIn :: Mono -> GenCt -> TcM [UnifVar]
fuvIn mono gct = (++) <$> fuvMono mono <*> fuvGenCt gct

wellTyped :: Prog -> TcM ()
wellTyped p = recur (wellTyped' p)

-- | [sch]; [env] |-> prog
wellTyped' :: Prog -> TcM ()
wellTyped' (Prog []      ) = pure ()
wellTyped' (Prog (d:prog)) = go d
 where
  go (DeclAnn f p@(Forall as q tau) e) = do
    logText "BindA"
    (v, q_wanted)     <- infer e
    fuvs              <- fuvIn v q_wanted
    (residual, theta) <- solve q fuvs (q_wanted <> GenSimp (CtEq v tau))
    assert (residual == CtTriv) (ErrText "residual constraints")
    local (bindingTypes %~ Map.insert (SymVar f) p) (wellTyped (Prog prog))
  go (Decl f e) = do
    logText "Bind"
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
    local (bindingTypes %~ Map.insert (SymVar f) ty) (wellTyped (Prog prog))

-- sch is given by the Reader environment.
-- [sch]; given |->solv wanted ~> residual; unifier
solve :: Ct -> [UnifVar] -> GenCt -> TcM (Ct, Subst)
solve q_given als_tch c_wanted = do
  logText "solve"
  let simple = simpleCt c_wanted
  (q_residual, theta) <- simplify q_given als_tch (mconcat simple)
  implics             <- implicationCt <$> instGenCt theta c_wanted
  for_ implics $ \case
    GenImplic als_i q_i c_i -> do
      (q_residual', _theta_i) <- solve (q_given <> q_residual <> q_i)
                                       als_tch
                                       c_i
      assert (q_residual' == CtTriv) (ErrText "solve: residual constraints")
    _ -> pure ()
  pure (q_residual, theta)

data CtFlag = CtWanted | CtGiven

data HTy = HTyVar TyVar | HTyFun HTy HTy | HFam HFam | HConApp TConName [HTy] | Hole (Maybe Tau)
  deriving Show
data HFam = HFamApp FamName [HTy]
  deriving Show
data HCls = HClsApp ClassName [HTy]
  deriving Show

substIntoHoleTy :: Tau -> HTy -> HTy
substIntoHoleTy = undefined

substIntoHoleFam :: Tau -> HFam -> HFam
substIntoHoleFam = undefined

substIntoHoleCls :: Tau -> HCls -> HCls
substIntoHoleCls = undefined

ctEqs :: Ct -> [(Mono,Mono)]
ctEqs = \case
  CtClass{} -> []
  CtTriv -> []
  CtEq m n -> [(m,n)]
  CtConj x y -> ctEqs x ++ ctEqs y

-- | [sch]; q_given; als_tch |->simp q_wanted ~> q_residual; theta
simplify :: Ct -> [UnifVar] -> Ct -> TcM (Ct, Subst)
simplify q_given als_tch q_wanted = recur $ do
  logText "Simples"
  logText ("  " <> tshow q_given)
  logText ("  " <> tshow als_tch)
  logText ("  " <> tshow q_wanted)
  Just (als', phi, qg', qw') <- rewrite als_tch [] q_given q_wanted
  -- _E
  flattened <- instCt (map (\(u,m) -> (Unif u, m)) phi) qw'
  equationals <- for (ctEqs flattened) $ \case
    (b@(MonoVar (Unif beta)), tau) -> do
      fuvs <- fuvMono tau
      guard (beta `elem` als' && beta `notElem` fuvs)
      pure [CtEq b tau]
    (tau, b@(MonoVar (Unif beta))) -> do
      fuvs <- fuvMono tau
      guard (beta `elem` als' && beta `notElem` fuvs)
      pure [CtEq b tau]
    _ -> pure []
  pure (q_residual, theta)
 where
  q_residual = CtTriv
  theta      = []

-- [sch]; als |-> (als, phi, q_g, q_w) -> (als', phi', q_g', q_w')
rewrite :: [UnifVar] -> Unifier -> Ct -> Ct -> TcM (Maybe ([UnifVar], Unifier, Ct, Ct))
-- intw
rewrite als phi qg (CtConj (CtConj qw q1) q2) = do
  q3 <- rewriteInteract CtWanted q1 q2
  pure (Just (als, phi, qg, qw <> q3))
-- intg
rewrite als phi (CtConj (CtConj qg q1) q2) qw = do
  q3 <- rewriteInteract CtGiven q1 q2
  pure (Just (als, phi, qg <> q3, qw))
-- cang
rewrite als phi1 (CtConj qg q1) q_w = do
  Just (betas, phi2, q2) <- rewriteCanon CtGiven q1
  pure (Just (als ++ betas, phi1 ++ phi2, qg <> q2, q_w))
-- canw
rewrite als phi1 qg (CtConj qw q1) = do
  Just (betas, phi2, q2) <- rewriteCanon CtWanted q1
  pure (Just (als ++ betas, phi1 ++ phi2, qg, qw <> q2))
rewrite als phi q_g q_w = pure (Just (als', phi', q_g', q_w'))
  where
    als' = undefined
    phi' = undefined
    q_g' = undefined
    q_w' = undefined

rewriteCanon :: CtFlag -> Ct -> TcM (Maybe ([UnifVar], Unifier, Ct))
rewriteCanon _ (CtEq t1 t2) | t1 == t2 = do
  logText "canon: Refl"
  pure (Just ([], [], CtTriv))
rewriteCanon _ (CtEq (MonoConApp con ts) (MonoConApp con' ts'))
  | con == con' = do
    logText "canon: TDec"
    pure (Just ([], [], mconcat (zipWith CtEq ts ts')))
  | otherwise = do
    logText "canon: FailDec"
    pure Nothing

rewriteSimplify :: Ct -> Ct -> TcM Ct
rewriteSimplify = undefined

rewriteInteract :: CtFlag -> Ct -> Ct -> TcM Ct
rewriteInteract = undefined

unsupported :: TcM a
unsupported = failWith (ErrText "unsupported")

rewriteTopReact :: CtFlag -> Ct -> TcM (Maybe ([UnifVar], Ct))
rewriteTopReact CtWanted (CtClass cls tys) | all noFam tys = do
  logText "DInstW"
  unsupported
rewriteTopReact CtGiven (CtClass cls tys) | all noFam tys = do
  logText "DInstG"
  subst <- for tys $ \ty -> do
    a <- freshUnifVarHint "u"
    pure (a, ty)
  unsupported

noFam :: Mono -> Bool
noFam = \case
  MonoFamApp{} -> False
  _            -> undefined

assert' cond = assert cond . ErrText

freeTyVars :: Mono -> TcM [TyVar]
freeTyVars = \case
  MonoPrim{} -> pure []
  _ -> unsupported

-- | |-can q
checkCanon :: Ct -> TcM ()
checkCanon (CtEq (MonoFamApp _ ms) r) = do
  assert (noFam r) (ErrText "noFam")
  assert (all noFam ms) (ErrText "noFam")
checkCanon (CtClass _ xis) = assert (all noFam xis) (ErrText "noFam")
checkCanon (CtEq v@(MonoVar tv) xi) = do
  lex <- v `lexLt` xi
  assert' lex "lex"
  fxi <- freeTyVars xi
  assert (tv `notElem` fxi) (ErrText "tv in ftv")

lexLt :: Mono -> Mono -> TcM Bool
lexLt (MonoFamApp _F taus) (MonoFamApp _G vs)
  = failWith (ErrText "lex: famApp") -- TODO or False? what if F = G?
lexLt (MonoFamApp _F taus) tau = pure True
lexLt (MonoVar tv1) (MonoVar tv2) = pure (tv1 < tv2)
lexLt (MonoVar _tv) xi | noFam xi = pure True
lexLt _ _ = unsupported

recur :: RecursionDepthM env m => m a -> m a
recur = local (recursionDepth +~ 1)

-- body [v -> e]
substExp :: Var -> Exp -> Exp -> Exp
substExp v e body =
  case body of
    ESym (SymVar v') -> if v == v' then e else body
    EApp x y         -> EApp (substExp v e x) (substExp v e y)
    EPrimOp{}        -> body
    EPrim{}          -> body

whnf :: Exp -> EvalM Exp
whnf e = case e of
  EPrim{} -> pure e
  ELam{} -> pure e
  EPrimOp{} -> pure e
  ESym (SymVar (Var s)) -> do
    env <- view bindings
    case Map.lookup s env of
      Just e  -> pure e
      Nothing -> throwError "unbound"
  EApp f a -> do
    w <- whnf f
    case w of
      ELam v e -> whnf (substExp v a e)
      f'       -> pure (EApp f' a)

-- whnf' :: Exp -> Prog -> Either Text Exp
whnf' e p = runEvalM (fromProg p) (whnf e)

logText :: (MonadWriter [LogItem] m, RecursionDepthM env m) => Text -> m ()
logText t = do
  depth <- view recursionDepth
  tell [LogItem depth (MsgText t)]

nf :: Exp -> EvalM Exp
nf e = do
  logText (tshow e)
  recur (nf' e)

nf' :: Exp -> EvalM Exp
nf' e = case e of
    EPrim{} -> pure e
    EPrimOp{} -> pure e
    ELam{} -> pure e
    ESym (SymVar (Var s)) -> do
      env <- view bindings
      case Map.lookup s env of
        Just e' -> pure e'
        Nothing -> pure e
    EApp (EApp (EPrimOp PrimAdd) v) w -> do
      logText "EAppPrim"
      EPrim (EInt v') <- nf v
      EPrim (EInt w') <- nf w
      pure (EPrim $ EInt $ v' + w')
    EApp f a -> do
      w <- nf f
      case w of
        ELam v e -> nf (substExp v a e)
        f'       -> EApp <$> nf f' <*> nf a

-- nfP :: Exp -> Prog -> Either Text Exp
nfP e p = runEvalM (fromProg p) (nf e)

elam v b = ELam (Var v) b
exp_id = ELam (Var "x") (evar "x")
two = EApp exp_id (EPrim (EInt 2))

fromProg :: Prog -> Map Text Exp
fromProg (Prog ds) = Map.fromList (map toPairs ds)
  where
    toPairs (Decl (Var v) a)      = (v, a)
    toPairs (DeclAnn (Var v) _ a) = (v, a)

--

initEnv :: TcEnv
initEnv = TcEnv bd AxTriv 0
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
        (MonoFun (MonoVar (Skol (SkolVar "t"))) (MonoVar (Skol (SkolVar "t"))))
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

runTc :: Show a => TcM a -> IO ()
runTc ma = do
  traverse_ print w
  print a
  where (a, _, w) = runTcM initEnv initState ma

x2 = Prog [DeclAnn (Var "x") (poly (MonoPrim PrimInt)) (EPrim (EInt 2))]

tests :: IO ()
tests = do
  putStrLn "\n>>> idint n"
  runTc $ infer (EApp (evar "idint") (evar "n"))

  putStrLn "\n>>> id"
  runTc $ infer (evar "id")

  putStrLn "\n>>> \\x -> id x"
  runTc $ infer exp_id

  putStrLn "\n>>> idint"
  runTc $ infer (evar "idint")

  putStrLn "\n>>> \\x -> idint x"
  runTc $ infer (ELam (Var "x") (EApp (evar "idint") (evar "x")))

  putStrLn "\n>>> case w of MkIntWrap x -> x"
  runTc $ infer $ ECase (evar "w")
                        (Alt (DConName "MkIntWrap") [Var "x"] x :| [])

  putStrLn "\n>>> case w of MkIntWrap x -> MkIntWrap x"
  runTc $ infer $ ECase
    (evar "w")
    (  Alt (DConName "MkIntWrap")
           [Var "x"]
           (EApp (ESym (SymCon (DConName "MkIntWrap"))) x)
    :| []
    )

  putStrLn "\n>>> id id"
  runTc $ infer (EApp (evar "id") (evar "id"))

  putStrLn "\n>>> id \\x -> x"
  runTc $ infer (EApp (evar "id") (ELam (var "x") x))

  putStrLn "\n>>> (\\x -> x) (\\x -> x)"
  runTc $ infer (EApp (ELam (var "x") x) (ELam (var "x") x))

  putStrLn "\n>>> (\\x -> x) (\\y -> y)"
  runTc $ infer (EApp (ELam (var "x") x) (ELam (var "y") y))

  putStrLn "\n>>> MkPair"
  runTc $ infer (econ "MkPair")

  putStrLn "\n>>> MkPair n"
  runTc $ infer (EApp (econ "MkPair") (evar "n"))

  putStrLn "\n>>> NonExistentCon"
  runTc $ infer (econ "NonExistentCon")

  putStrLn "\n>>> id (MkPair MkPair MkPair)"
  runTc $ infer
    ( EApp (evar "id")
           (EApp (econ "MkPair") (EApp (econ "MkPair") (econ "MkPair")))
    )
  putStrLn "\n>>> \\def -> \\ma -> case ma of Just x -> x; Nothing -> def"
  runTc $ infer
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
  putStrLn "\n>>> \\def -> \\ma -> case ma of Nothing -> def; Just x -> x"
  runTc $ infer bdFromMaybe

  putStrLn "\n>>> x :: Int = 2"
  runTc $ wellTyped x2

  putStrLn "\n>>> x :: Bool = n"
  runTc $ wellTyped $ Prog
    [DeclAnn (Var "x") (poly (MonoPrim PrimBool)) (ESym (SymVar (Var "n")))]
 where
  var  = Var
  n    = evar "n"
  x    = evar "x"
  y    = evar "y"

evar = ESym . SymVar . Var
econ = ESym . SymCon . DConName
