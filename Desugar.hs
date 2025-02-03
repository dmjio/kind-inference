import KindInference

-- desugaring strips type info?
desugar :: Exp Kind (Type Kind) -> IO (Exp () ())
desugar (Lam _ args e) = do
  as <- mapM desugar args
  e' <- desugar e
  pure $ foldl (\arg z -> Lam () [arg] z) e' as
desugar (Var _ n) = pure (Var () n)
desugar (Lit _ n) = pure (Lit () n)
desugar (PrimOp _ n) = pure (PrimOp () n)
desugar (App _ l r) = App () <$> desugar l <*> desugar r
desugar (InfixOp _ l n r) = do
  l' <- desugar l
  r' <- desugar r
  pure $ foldl (App ()) (Var () n) [l', r']
desugar (As _ n e) = do
  e' <- desugar e
  pure $ Lam () [ Var () n ] e'
desugar (Con _ n pats) = do
  ps <- mapM desugar pats
  pure (Con () n ps)
desugar (Wildcard _) = pure (Wildcard ())
desugar (Fail _) = pure (Fail ())
desugar (Let _ _ _) = undefined -- TODO?
desugar (IfThenElse _ boolStmt trueStmt falseStmt) = do
  b <- desugar boolStmt
  t <- desugar trueStmt
  f <- desugar falseStmt
  pure $ Case (ann b) b
    [ Alt (Con () "True" []) t []
    , Alt (Con () "False" []) f []
    ]
desugar (Case _ e alts) =
  Case () <$> desugar e <*> mapM desugarAlt alts

-- TODO: handle recursive Let
desugar (Do _ stmts) =
  case stmts of
    [SExp e] -> desugar e
    _ -> error "do blocks should be all transformed already, through typeclass specialization"

desugar (TypeAnn _ e) = desugar e

desugar (LeftSection _ e n) = do
  e' <- desugar e
  pure (Lam () [Var () n] (App () e' (Var () n)))

desugar (RightSection _ n e) = do
  e' <- desugar e
  pure (Lam () [Var () n] (App () (Var () n) e'))

desugar (Tuple _ es) = do
  es' <- mapM desugar es
  pure $ foldl (\c e -> App () c e) (Con () tuple []) es'
    where
      tuple = "(" <> replicate (length es - 1) ',' <> ")"

desugar (List _ es) = do
   es' <- mapM desugar es
   pure $ foldl (App () . (Con () "Cons") . pure) (Con () "Nil" []) es'

desugar (PrefixNegation _ e) = do
   e' <- desugar e
   pure (App () (App () (Lit () (LitInt (-1))) (Var () "*")) e')

desugar (Irrefutable _ e) = do
  desugar e -- TODO: hrm?

desugar (ListComp t e stmts) = do
  -- these are all translated away via intensional type analysis
  desugar (Do t (stmts ++ [SExp e]))

desugarAlt :: Alt Kind (Type Kind) -> IO (Alt () ())
desugarAlt (Alt p e decls) =
  Alt
    <$> desugar p
    <*> desugar e
    <*> mapM desugarDecl decls
desugarAlt (AltGd p guards decls) = do
  undefined
  -- TODO
  -- AltGd
  --   <$> desugar p
  --   <*> desugarGuards p

desugarDecl :: Decl Kind (Type Kind) -> IO (Decl () ())
desugarDecl (Decl _ bindings) = Decl () <$> mapM desugarBinding bindings
desugarDecl _ = error "only Decl supported, filter rest out"

desugarBinding :: Binding Kind (Type Kind) -> IO (Binding () ())
desugarBinding (Binding _ n pats e) =
  Binding () n <$> mapM desugar pats <*> desugar e
