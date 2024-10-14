module Main where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State  hiding (state)
import           Data.Function
import           Data.List
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Set             (Set)
import qualified Data.Set             as S
import           Prelude              hiding (maybe)

type Name = String

newtype TyVar = TyVar Name
  deriving (Show, Eq, Ord)

newtype TyCon = TyCon Name
  deriving (Show, Eq, Ord)

newtype MetaVar = MetaVar { unMetaVar :: Int }
  deriving (Show, Eq, Num, Ord)

showMetaVar :: MetaVar -> String
showMetaVar mv = showKind (KindMetaVar mv)

data Decl kind typ
  = Data kind Name [TyVar] [Variant kind]
  | TypeSyn kind Name [TyVar] (Type kind)
  | Class kind Name [TyVar] [Method kind]
  | Instance kind [Pred kind] (Pred kind)
  | Newtype kind Name [TyVar] (Variant kind)
  | KindSignature kind Name Kind
  | Foreign kind Name (Type kind)
  | TypeSignature kind Name [Pred kind] (Type kind)
  | Declaration kind (Binding typ)
  deriving (Show, Eq)

data Binding typ
  = Binding typ Name [Exp typ] (Exp typ)
  deriving (Show, Eq)

class Fun a where
  infixr 9 -->
  (-->) :: a -> a -> a

instance Fun Kind where
  (-->) :: Kind -> Kind -> Kind
  (-->) = KindFun

instance Fun (Type ()) where
  (-->) :: Type () -> Type () -> Type ()
  (-->) = TypeFun ()

instance Fun (Type Kind) where
  (-->) :: Type Kind -> Type Kind -> Type Kind
  (-->) = TypeFun Type

data Exp a
  = Var a Name
  | Lit a Lit
  | App a (Exp a) (Exp a)
  deriving (Show, Eq)

data Lit
  = LitInt Int
  deriving (Show, Eq)

data Pred a = Pred a Name (Type a)
  deriving (Show, Eq)

data Method a = Method Name (Type a)
  deriving (Show, Eq)

class GetName f where
  getName :: f -> Name

instance GetName Name where
  getName = id

instance GetName (Decl a typ) where
  getName (Data _ name _ _)        = name
  getName (TypeSyn _ name _ _)     = name
  getName (Class _ name _ _)       = name
  getName (Newtype _ name _ _)     = name
  getName (KindSignature _ name _) = name
  getName (Instance _ _ p)      = getName p
  getName (Foreign _ name _)       = name
  getName (TypeSignature _ name _ _) = name
  getName (Declaration _ binding) = getName binding

instance GetName (Binding a) where
  getName (Binding _ name _ _) = name

instance GetName (Pred a) where
  getName (Pred _ name _) = name

instance GetName (Type a) where
  getName (TypeVar _ name) = getName name
  getName (TypeCon _ name) = getName name
  getName (TypeMetaVar mv) = getName mv
  getName _ = "<no name>"

instance GetName MetaVar where
  getName = showMetaVar

instance GetName TyVar where
  getName (TyVar n) = n

instance GetName TyCon where
  getName (TyCon n) = n

data Variant a
  = Variant Name [Type a]
  deriving (Show, Eq)

data Type a
  = TypeVar a TyVar
  | TypeCon a TyCon
  | TypeFun a (Type a) (Type a)
  | TypeApp a (Type a) (Type a)
  | TypeMetaVar MetaVar
  deriving (Show, Eq, Ord)

newtype KindVar = MkKindVar { unKindVar :: Name }
  deriving (Show, Eq, Ord)

-- | A representation of a kind.
data Kind
  = Type
  | KindFun Kind Kind
  | KindVar KindVar
  | KindMetaVar MetaVar
  | Constraint
  deriving (Show, Eq, Ord)

data Scheme = Scheme [KindVar] Kind
  deriving (Show, Eq)

showKind :: Kind -> String
showKind (KindFun f x) = showKindVar f <> " -> " <> showKind x
showKind x             = showKindVar x

showKindVar :: Kind -> String
showKindVar (KindVar (MkKindVar v))   = v
showKindVar (KindMetaVar (MetaVar v)) = "{" <> show v <> "}"
showKindVar Type                      = "*"
showKindVar Constraint                = "Constraint"
showKindVar x                         = parens (showKind x)

cataType :: (Type a -> Type a) -> Type a -> Type a
cataType f (TypeFun x l r) = f $ TypeFun x (cataType f l) (cataType f r)
cataType f (TypeApp x l r) = f $ TypeApp x (cataType f l) (cataType f r)
cataType f x = f x

showType :: ShowAnn ann => Type ann -> String
showType t = showType_ (cataType fun t)
  where
    fun (TypeApp a (TypeApp _ (TypeCon _ (TyCon "(->)")) f) x) =
      TypeFun a f x
    fun x = x

showType_ :: ShowAnn ann => Type ann -> String
showType_ (TypeFun _ l r)   = showTypeVar l <> " -> " <> showType_ r
showType_ (TypeApp _ f x) = showType_ f <> " " <> showTypeVar x
showType_ t                 = showTypeVar t

showTypeVar :: ShowAnn ann => Type ann -> String
showTypeVar (TypeVar _ (TyVar v)) = v
showTypeVar (TypeCon _ (TyCon c)) = c
showTypeVar (TypeMetaVar (MetaVar v)) = "{" <> show v <> "}"
showTypeVar x                       = parens (showType_ x)

parens :: String -> String
parens x = "(" <> x <> ")"

showScheme :: Scheme -> String
showScheme (Scheme [] k) = showKind k
showScheme (Scheme vars k) =
  intercalate " "
    [ "forall"
    , intercalate " " [ v | MkKindVar v <- vars ]
    , "."
    , showKind k
    ]

showTypeScheme :: TypeScheme -> String
showTypeScheme (TypeScheme [] k) = showType k
showTypeScheme (TypeScheme vars k) =
  intercalate " "
    [ "forall"
    , intercalate " " [ v | TyVar v <- vars ]
    , "."
    , showType k
    ]


data Constraint
  = Equality Kind Kind
  | TypeEquality (Type Kind) (Type Kind)
  deriving (Eq, Ord)

instance Show Constraint where
  show = showConstraint

showConstraint :: Constraint -> String
showConstraint (Equality k1 k2) =
  intercalate "\n"
  [ showKind k1 <> " = " <> showKind k2
  ]
showConstraint (TypeEquality t1 t2) =
  intercalate "\n"
  [ showType t1 <> " = " <> showType t2
  ]

data InferState
  = InferState
  { env           :: Map Name MetaVar
  , kindEnv       :: Map Name Scheme
  , typeEnv       :: Map Name TypeScheme
  , substitutions :: Map MetaVar Kind
  , typeSubstitutions :: Map MetaVar (Type Kind)
  , var           :: Int
  , constraints   :: [Constraint]
  } deriving (Show, Eq)

type Subst = Map MetaVar Kind
type Infer = ExceptT Error (StateT InferState IO)

data Error
  = UnboundName Name
  | UnificationFailed Kind Kind
  | UnificationFailedType (Type Kind) (Type Kind)
  | OccursCheckFailed MetaVar Kind
  | OccursCheckFailedType MetaVar (Type Kind)

fresh :: Infer MetaVar
fresh = do
  modify $ \s -> s { var = var s + 1 }
  MetaVar <$> gets var

instance Show Error where
  show (UnificationFailed k1 k2) =
    intercalate "\n"
    [ "Unification failed"
    , "Kind: " <> showKind k1
    , "Kind: " <> showKind k2
    ]
  show (UnificationFailedType k1 k2) =
    intercalate "\n"
    [ "Unification failed"
    , "Type: " <> showType k1
    , "Type: " <> showType k2
    ]
  show (UnboundName tyvar) =
    "Unbound Name: " <> show tyvar
  show (OccursCheckFailed mv k) =
    intercalate "\n"
    [ "Occurs check failed"
    , "MetaVar: " <> showKind (KindMetaVar mv)
    , "Kind: " <> showKind k
    ]
  show (OccursCheckFailedType mv k) =
    intercalate "\n"
    [ "Occurs check failed"
    , "MetaVar: " <> showMetaVar mv
    , "Type: " <> showType k
    ]

class ShowAnn a where
  showAnn :: a -> String

instance ShowAnn () where
  showAnn () = ""

instance ShowAnn Kind where
  showAnn k = showScheme (generalize k)

instance ShowAnn (Type Kind) where
  showAnn k = showType k

instance ShowAnn MetaVar where
  showAnn (MetaVar m) = "<" <> show m <> ">"

showDecl :: (ShowAnn typ, ShowAnn kind) => Decl kind typ -> String
showDecl (TypeSyn a name vars typ) =
  intercalate " "
  [ "type"
  , if null (showAnn a) then name else parens (name <> " :: " <> showAnn a)
  , intercalate " " [ v | TyVar v <- vars ]
  , "="
  , showType typ
  ]
showDecl (Data a n vars xs) =
  intercalate " "
  [ "data"
  , if null (showAnn a)
    then n
    else parens (n <> " :: " <> showAnn a)
  , intercalate " " [ x | TyVar x <- vars ]
  , case xs of
      [] -> ""
      y : ys ->
        concat
        [ "\n  = " <> showVariant y
        , concat
          [ "\n  | " <> v
          | v <- fmap showVariant ys
          ]
        ]
  ]
showDecl (Class a n vars methods) =
  intercalate " "
  [ "class"
  , if null (showAnn a) then n else parens (n <> " :: " <> showAnn a)
  , intercalate " " [ x | TyVar x <- vars ]
  , "where"
  , beforeAll "\n  " (showMethod <$> methods)
  ]
showDecl (Instance a ps p) =
  intercalate " "
  [ "instance"
  , case ps of
      [] -> showPred p
      [x] -> showPred x <> " => " <> showPred p
      xs -> parens $ intercalate ", " (showPred <$> xs) <> " => " <> showPred p
  , "::"
  , showAnn a
  , "where"
  ]
showDecl (Newtype a n vars variant) =
  intercalate " "
  [ "newtype"
  , if null (showAnn a)
    then n
    else parens (n <> " :: " <> showAnn a)
  , intercalate " " [ x | TyVar x <- vars ]
  , "="
  , showVariant variant
  ]
showDecl (KindSignature _ name kind) =
  intercalate " "
  [ "type"
  , name
  , "::"
  , showKind kind
  ]
showDecl (TypeSignature a name preds t) =
  intercalate " " $
  [ name
  , "::"
  , case preds of
      [] -> showType t
      [x] -> showPred x <> " => " <> showType t
      xs -> parens (intercalate ", " (showPred <$> xs)) <> " => " <> showType t
  ] ++
  [ ":: " <> showAnn a
  | not $ null (showAnn a)
  ]
showDecl (Foreign a name typ) =
  intercalate " "
  [ "foreign"
  , "import"
  , "unsafe"
  , "ccall"
  , name
  , "::"
  ,  if null (showAnn a)
     then showType typ
     else parens (showType typ <> " :: " <> showAnn a)
  ]
showDecl (Declaration _ binding) = showBinding binding

showBinding :: ShowAnn a => Binding a -> String
showBinding (Binding annType name args body) =
  intercalate " "
  [ name
  , intercalate " " (showExp <$> args) <> " = " <> showExp body <>
      if null (showAnn annType)
        then ""
        else " :: " <> showAnn annType
  ]

showExp :: Exp a -> String
showExp (App _ f x) = showExpVar f <> " -> " <> showExp x
showExp x = showExpVar x

showExpVar :: Exp a -> String
showExpVar (Var _ name) = name
showExpVar (Lit _ lit) = showLit lit
showExpVar x = parens (showExp x)


showLit :: Lit -> String
showLit (LitInt x) = show x

beforeAll :: [a] -> [[a]] -> [a]
beforeAll _ [] = []
beforeAll s xs = s <> intercalate s xs

showListInst :: Decl () typ
showListInst = Instance () [Pred () "Show" (tCon "List" `app` tVar "a")]
  (Pred () "Show" (tVar "a"))

showMethod :: ShowAnn ann => Method ann -> String
showMethod (Method name t) =
  intercalate " "
  [ name
  , "::"
  , showType t
  ]

showPred :: ShowAnn ann => Pred ann -> String
showPred (Pred _ name typ) =
  name <> " " <> showTypeVar typ

showVariant :: ShowAnn ann => Variant ann -> String
showVariant (Variant n []) = n
showVariant (Variant n ts) = intercalate " " (n : fmap showTypeVar ts)

solve :: Infer ()
solve = do
  dbg "Solving..."
  solveConstraints

solveConstraints :: Infer ()
solveConstraints = do
  constraint <- popConstraint
  case constraint of
    Nothing -> do
      dbg "Solving complete..."
    Just (Equality k1 k2) -> do
      mapM_ (uncurry apply) =<< unify k1 k2
      solveConstraints
    Just (TypeEquality t1 t2) -> do
      mapM_ (uncurry applyType) =<< unifyType t1 t2
      solveConstraints
    where
      apply k v = do
        updateSubstitution k v
        updateConstraints k v

      applyType k v = do
        updateSubstitutionType k v
        updateConstraintsType k v

updateConstraints :: MetaVar -> Kind -> Infer ()
updateConstraints m1 k = do
  cs <- fmap replaceConstraint <$> gets constraints
  modify $ \s -> s { constraints = cs }
    where
      replaceConstraint (Equality l r) =
        Equality (cataKind replaceKind l) (cataKind replaceKind r)
          where
            replaceKind (KindMetaVar m2) | m1 == m2 = k
            replaceKind x = x
      replaceConstraint x = x

updateConstraintsType :: MetaVar -> Type Kind -> Infer ()
updateConstraintsType m1 k = do
  cs <- fmap replaceConstraint <$> gets constraints
  modify $ \s -> s { constraints = cs }
    where
      replaceConstraint (TypeEquality l r) =
        TypeEquality (cataType replaceType l) (cataType replaceType r)
          where
            replaceType (TypeMetaVar m2) | m1 == m2 = k
            replaceType x = x
      replaceConstraint x = x

popConstraint :: Infer (Maybe Constraint)
popConstraint = do
  ccs <- gets constraints
  case ccs of
    c : cs -> do
      modify $ \s -> s { constraints = cs }
      pure (Just c)
    [] ->
      pure Nothing

unifyType
  :: Type Kind
  -> Type Kind
  -> Infer (Maybe (MetaVar, Type Kind))
unifyType (TypeVar k1 x) (TypeVar k2 y)
  | x == y = do
      when (k1 /= k2) $ throwError (UnificationFailed k1 k2)
      pure Nothing
unifyType (TypeCon k1 x) (TypeCon k2 y)
  | x == y = do
      when (k1 /= k2) $ throwError (UnificationFailed k1 k2)
      pure Nothing
unifyType (TypeMetaVar x) (TypeMetaVar y) | x == y = pure Nothing
unifyType (TypeFun k1 x1 y1) (TypeFun k2 x2 y2) = do
  when (k1 /= k2) $ throwError (UnificationFailed k1 k2)
  constrainTypes x1 x2
  constrainTypes y1 y2
  pure Nothing
unifyType (TypeMetaVar x) y = metaVarBindType x y
unifyType x (TypeMetaVar y) = metaVarBindType y x
unifyType k1 k2 = do
  dump "Failed"
  throwError (UnificationFailedType k1 k2)

unify :: Kind -> Kind -> Infer (Maybe (MetaVar, Kind))
unify Type Type = pure Nothing
unify Constraint Constraint = pure Nothing
unify (KindVar x) (KindVar y) | x == y = pure Nothing
unify (KindMetaVar x) (KindMetaVar y) | x == y = pure Nothing
unify (KindFun x1 y1) (KindFun x2 y2) = do
  constrainKinds x1 x2
  constrainKinds y1 y2
  pure Nothing
unify (KindMetaVar x) y = metaVarBind x y
unify x (KindMetaVar y) = metaVarBind y x
unify k1 k2 = do
  dump "Failed"
  throwError (UnificationFailed k1 k2)

dump :: String -> Infer ()
dump msg = do
  dbg ""
  dbg msg
  when shouldDebug $ do
    -- dumpSubs
    dumpTypeSubs
    dumpConstraints
    dumpEnv
    dumpTypeEnv
    -- dumpKindEnv

dumpSubs :: Infer ()
dumpSubs = do
  liftIO (putStrLn "\nDumping Substitutions...")
  subs <- gets substitutions
  liftIO $ putStrLn (showSubs subs)
    where
      showSubs :: Subst -> String
      showSubs subst = intercalate "\n" (showSub <$> M.toList subst)

      showSub :: (MetaVar, Kind) -> String
      showSub (k,v) = showMetaVar k <> " : " <> showKind v

dumpTypeSubs :: Infer ()
dumpTypeSubs = do
  liftIO (putStrLn "\nDumping Type Substitutions...")
  subs <- gets typeSubstitutions
  liftIO $ putStrLn (showSubs subs)
    where
      showSubs :: Map MetaVar (Type Kind) -> String
      showSubs subst = intercalate "\n" (showSub <$> M.toList subst)

      showSub :: (MetaVar, (Type Kind)) -> String
      showSub (k,v) = showMetaVar k <> " : " <> showType v

dumpConstraints :: Infer ()
dumpConstraints = do
  cs <- gets constraints
  unless (null cs) $ do
    liftIO (putStrLn "\nDumping Constraints...")
    liftIO $ forM_ cs print

dumpEnv :: Infer ()
dumpEnv = do
  liftIO (putStrLn "\nDumping Env...")
  e <- gets env
  liftIO $ forM_ (M.assocs e) $ \(name,mv) ->
    putStrLn $ name <> " : " <> showMetaVar mv

dumpKindEnv :: Infer ()
dumpKindEnv = do
  liftIO (putStrLn "\nDumping Kind Env...")
  e <- gets kindEnv
  liftIO $ forM_ (M.assocs e) $ \(name, mv) ->
    putStrLn $ name <> " : " <> showScheme mv

dumpTypeEnv :: Infer ()
dumpTypeEnv = do
  liftIO (putStrLn "\nDumping Type Env...")
  e <- gets typeEnv
  liftIO $ forM_ (M.assocs e) $ \(name, mv) ->
    putStrLn $ name <> " : " <> showTypeScheme mv

metaVarBind :: MetaVar -> Kind -> Infer (Maybe (MetaVar, Kind))
metaVarBind mv (KindMetaVar m) | mv == m = pure Nothing
metaVarBind m k = do
  dbg ("Binding... " ++ showMetaVar m ++ " : " ++ showKind k)
  occursCheck m k
  pure (Just (m, k))

metaVarBindType :: MetaVar -> Type Kind -> Infer (Maybe (MetaVar, Type Kind))
metaVarBindType mv (TypeMetaVar m) | mv == m = pure Nothing
metaVarBindType m k = do
  dbg ("Binding... " ++ showMetaVar m ++ " : " ++ showType k)
  occursCheckType m k
  pure (Just (m, k))

updateSubstitution :: MetaVar -> Kind -> Infer ()
updateSubstitution m k = modifySub (M.map replaceInState . M.insert m k)
  where
    replaceInState = cataKind $ \kind ->
      case kind of
        KindMetaVar mv | mv == m -> k
        z                        -> z

updateSubstitutionType :: MetaVar -> Type Kind -> Infer ()
updateSubstitutionType m k = modifyTypeSub (M.map replaceInState . M.insert m k)
  where
    replaceInState = cataType $ \t ->
      case t of
        TypeMetaVar mv | mv == m -> k
        z                        -> z

occursCheck :: MetaVar -> Kind -> Infer ()
occursCheck mv k = do
  when (mv `S.member` metaVars k) $
    throwError (OccursCheckFailed mv k)

occursCheckType :: MetaVar -> Type Kind -> Infer ()
occursCheckType mv t = do
  when (mv `S.member` metaVarsType t) $
    throwError (OccursCheckFailedType mv t)

modifySub :: (Subst -> Subst) -> Infer ()
modifySub f = do
  subs <- gets substitutions
  modify $ \s -> s { substitutions = f subs }

type SubstTyped = Map MetaVar (Type Kind)

modifyTypeSub :: (SubstTyped -> SubstTyped) -> Infer ()
modifyTypeSub f = do
  subs <- gets typeSubstitutions
  modify $ \s -> s { typeSubstitutions = f subs }

getKind :: MetaVar -> Infer Kind
getKind mv =
  M.findWithDefault (KindMetaVar mv) mv <$>
    gets substitutions

getType :: MetaVar -> Infer (Type Kind)
getType mv =
  M.findWithDefault (TypeMetaVar mv) mv <$>
    gets typeSubstitutions

substituteTyped :: Decl Kind MetaVar -> Infer (Decl Kind (Type Kind))
substituteTyped decl = do
  dbg "Substituting Type..."
  substituteDeclTyped decl

substituteDeclTyped
  :: Decl Kind MetaVar
  -> Infer (Decl Kind (Type Kind))
substituteDeclTyped (Declaration kind binding) = do
  b <- substituteBinding binding
  pure (Declaration kind b)
-- TODO: draw rest of the owl here
-- substituteDeclTyped x = pure x

substituteBinding :: Binding MetaVar -> Infer (Binding (Type Kind))
substituteBinding (Binding mv name args body) = do
  typ <- getType mv
  args' <- traverse substituteExp args
  body' <- substituteExp body
  pure (Binding typ name args' body')

substituteExp :: Exp MetaVar -> Infer (Exp (Type Kind))
substituteExp (Var mv name) = do
  typ <- getType mv
  pure (Var typ name)
substituteExp (Lit mv x) = do
  typ <- getType mv
  pure (Lit typ x)
substituteExp (App mv f x) = do
  typ <- getType mv
  fun <- substituteExp f
  arg <- substituteExp x
  pure (App typ fun arg)

substitute
  :: Decl MetaVar ()
  -> Infer (Decl Kind ())
substitute decl = do
  dbg "Substituting Kind..."
  substituteDecl decl

substituteDecl :: Decl MetaVar () -> Infer (Decl Kind ())
substituteDecl (Class mv name vars methods) = do
  substitutedKind <- getKind mv
  typ' <- traverse substituteMethod methods
  pure (Class substitutedKind name vars typ')
substituteDecl (TypeSyn mv name vars typ) = do
  substitutedKind <- getKind mv
  typ' <- substituteType typ
  pure (TypeSyn substitutedKind name vars typ')
substituteDecl (Data mv name vars variants) = do
  substitutedKind <- getKind mv
  substitutedVariants <- mapM substituteVariant variants
  pure (Data substitutedKind name vars substitutedVariants)
substituteDecl (Newtype mv name vars variant) = do
  substitutedKind <- getKind mv
  substitutedVariant <- substituteVariant variant
  pure (Newtype substitutedKind name vars substitutedVariant)
substituteDecl (KindSignature mv name kind) = do
  k <- getKind mv
  pure (KindSignature k name kind)
substituteDecl (Instance mv supers context) = do
  k <- getKind mv
  supers_ <- traverse substitutePred supers
  ctx_ <- substitutePred context
  pure (Instance k supers_ ctx_)
substituteDecl (TypeSignature mv name ctx typ) = do
  k <- getKind mv
  ctx_ <- traverse substitutePred ctx
  t <- substituteType typ
  pure (TypeSignature k name ctx_ t)
substituteDecl (Foreign mv name typ) = do
  k <- getKind mv
  t <- substituteType typ
  pure (Foreign k name t)
substituteDecl (Declaration _ binding) = do
  pure (Declaration Type binding)

substitutePred
  :: Pred MetaVar
  -> Infer (Pred Kind)
substitutePred (Pred mv n typ) = do
  k <- getKind mv
  t <- substituteType typ
  pure (Pred k n t)

substituteVariant
  :: Variant MetaVar
  -> Infer (Variant Kind)
substituteVariant (Variant name types) = do
  substituted <- traverse substituteType types
  pure (Variant name substituted)

substituteMethod :: Method MetaVar -> Infer (Method Kind)
substituteMethod (Method name typ) = do
  t <- substituteType typ
  pure (Method name t)

substituteType :: Type MetaVar -> Infer (Type Kind)
substituteType (TypeCon mv tyCon) = do
  kind <- getKind mv
  pure (TypeCon kind tyCon)
substituteType (TypeApp mv f x) = do
  kind <- getKind mv
  g <- substituteType f
  y <- substituteType x
  pure (TypeApp kind g y)
substituteType (TypeFun mv f x) = do
  kind <- getKind mv
  g <- substituteType f
  y <- substituteType x
  pure (TypeFun kind g y)
substituteType (TypeVar mv t) = do
  kind <- getKind mv
  pure (TypeVar kind t)
substituteType (TypeMetaVar mv) =
  pure (TypeMetaVar mv)

emptyState :: InferState
emptyState = InferState mempty defaultKindEnv defaultTypeEnv mempty mempty 0 []

defaultTypeEnv :: Map String TypeScheme
defaultTypeEnv = M.fromList
  [ ("(+)", TypeScheme [] (tConT "Int" --> tConT "Int" --> tConT "Int"))
  ]

defaultKindEnv :: Map String Scheme
defaultKindEnv = M.fromList
  [ ("Int", Scheme [] Type)
  , ("Double", Scheme [] Type)
  , ("String", Scheme [] Type)
  , ("Bool", Scheme [] Type)
  , ("Either", Scheme [] (Type --> Type --> Type))
  , ("Maybe", Scheme [] (Type --> Type))
  , ("Monad", Scheme [] ((Type --> Type) --> Constraint))
  , ("Eq", Scheme [] (Type --> Constraint))
  , ("IO", Scheme [] (Type --> Type))
  , ("()", Scheme [] Type)
  , ("(->)", Scheme [] (Type --> Type --> Type))
  , ("StateT", Scheme [] (Type --> (Type --> Type) --> Type --> Type))
  , ("Identity", Scheme [] (Type --> Type))
  ]

runInfer :: Infer a -> IO (Either Error a)
runInfer m = evalStateT (runExceptT m) emptyState

dbg :: MonadIO m => String -> m ()
dbg s = when shouldDebug $ liftIO (putStrLn s)

shouldDebug :: Bool
shouldDebug = True

tt :: IO ()
tt = testInferType [ dec constFunc
                   , dec idFunc
                   , dec addOne
                   ]
  where
    idFunc = b "id" [ v "x" ] (v "x")
    constFunc = b "const" [ v "a", v "b" ] (v "a")
    addOne = b "addOne" [ v "x" ] (v "(+)" `appE` v "x" `appE` lint 1)

    appE = App ()
    b = Binding ()
    dec = Declaration Type
    v = Var ()
    lint = Lit () . LitInt

testInferType :: [Decl Kind ()] -> IO ()
testInferType decls = do
  dbg "Declarations..."
  dbg $ intercalate "\n" (showDecl <$> decls)
  result <- inferTypes decls
  case result of
    Left err -> print err
    Right ds -> do
      dbg "\nInferred types..."
      forM_ ds $ \decl -> do
        case decl of
          Declaration _ binding -> do
            let
              scheme = generalizeType (ann binding)
              name = getName decl
            dbg $ name <> " :: " <> showTypeScheme scheme
          _ -> pure ()

inferTypes
  :: [Decl Kind ()]
  -> IO (Either Error [Decl Kind (Type Kind)])
inferTypes decls = runInfer $ do
  addTypeSignatures decls
  addBindings decls
  forM decls $ \d -> do
    (maybeScheme, decl) <- inferType d
    mapM_ (addToTypeEnv decl) maybeScheme
    dump "Done"
    -- decl <$ reset
    pure decl

reset :: Infer ()
reset =
  modify $ \s ->
    s { env = mempty
      , substitutions = mempty
      , var = 0
      }

inferKinds :: [Decl () ()] -> IO (Either Error [Decl Kind ()])
inferKinds decls = runInfer $ do
  addKindSignatures decls
  forM decls $ \d -> do
    (scheme, decl) <- inferKind d
    addToKindEnv decl scheme
    decl <$ reset

addKindSignatures :: [Decl a ()] -> Infer ()
addKindSignatures decls = do
  let sigs = [ (name, generalize k) | KindSignature _ name k <- decls ]
  mapM_ (uncurry addToKindEnv) sigs

addTypeSignatures :: [Decl Kind ()] -> Infer ()
addTypeSignatures decls = do
  let sigs = [ (name, generalizeType typ) | TypeSignature _ name _ typ <- decls ]
  mapM_ (uncurry addToTypeEnv) sigs

addBindings :: [Decl Kind ()] -> Infer ()
addBindings decls =
  forM_ decls $ \decl ->
    case decl of
      Declaration _ (Binding () name _ _) ->
        void (addToEnv name)
      _ ->
        pure ()

addToKindEnv :: GetName a => a -> Scheme -> Infer ()
addToKindEnv k v =
  modify $ \s -> s {
    kindEnv = M.insert (getName k) v (kindEnv s)
  }

addToTypeEnv :: GetName a => a -> TypeScheme -> Infer ()
addToTypeEnv k v =
  modify $ \s -> s {
    typeEnv = M.insert (getName k) v (typeEnv s)
  }

inferKind :: Decl () () -> Infer (Scheme, Decl Kind ())
inferKind decl = do
  dbg "Inferring Kind..."
  elaborated <- elaborateDecl decl
  solve
  d <- substitute elaborated
  pure (generalizeDecl d, d)

populateEnv :: GetName name => [name] -> Infer [MetaVar]
populateEnv = mapM (addToEnv . getName)

inferType :: Decl Kind () -> Infer (Maybe TypeScheme, Decl Kind (Type Kind))
inferType decl = do
  elaborated <- elaborateDeclTyped decl
  solve
  d <- substituteTyped elaborated
  pure (generalizeDeclType d, d)

data TypeScheme = TypeScheme [TyVar] (Type Kind)
  deriving (Show, Eq)

addToEnv :: Name -> Infer MetaVar
addToEnv k = do
  v <- fresh
  modifyEnv (M.insert k v)
  pure v

modifyEnv :: (Map Name MetaVar -> Map Name MetaVar) -> Infer ()
modifyEnv f = modify $ \s -> s { env = f (env s) }

-- TODO: implement renaming, to avoid the situation below
-- foo x = x + 1
-- bar foo = foo + 1
-- -- ^ foo here will overwrite the top level binding in env, needs to be renamed
elaborateDeclTyped :: Decl Kind () -> Infer (Decl Kind MetaVar)
elaborateDeclTyped (Declaration kind binding) = do
  b <- elaborateBinding binding
  pure (Declaration kind b)
-- TODO: Finish elaborating here

elaborateBinding :: Binding () -> Infer (Binding MetaVar)
elaborateBinding (Binding () name args body) = do
  mv <- lookupNamedType name
  let fvs = S.unions (freeVarsExp <$> args)
  mvs <- fmap TypeMetaVar <$> populateEnv (S.toList fvs)
  args' <- traverse elaborateExp args
  body' <- elaborateExp body
  constrainType mv (foldr tFun (TypeMetaVar (ann body')) mvs)
  pure (Binding mv name args' body')

tFun :: Type Kind -> Type Kind -> Type Kind
tFun = TypeFun Type

elaborateExp :: Exp () -> Infer (Exp MetaVar)
elaborateExp (Var () name) = do
  mv <- lookupNamedType name
  pure (Var mv name)
elaborateExp (Lit () x) = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "Int"))
  pure (Lit mv x)
elaborateExp (App () f x) = do
  fun <- elaborateExp f
  arg <- elaborateExp x
  mv <- fresh
  constrainType (ann fun)
    (TypeMetaVar (ann arg) --> TypeMetaVar mv)
  pure (App mv fun arg)

elaborateDecl :: Decl () () -> Infer (Decl MetaVar ())
elaborateDecl decl = do
  dbg "Elaborating..."
  elaborate decl =<< addToEnv (getName decl)

handleKindSignature
  :: Name
  -> MetaVar
  -> Infer ()
handleKindSignature name mv = do
  result <- lookupKindEnv name
  forM_ result (constrain mv . KindMetaVar)

elaborate :: Decl () () -> MetaVar -> Infer (Decl MetaVar ())
elaborate (TypeSyn () name vars typ) mv = do
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv vars
  t <- elaborateType typ
  constrain mv (foldr KindFun (KindMetaVar (ann t)) mvs)
  pure (TypeSyn mv name vars t)
elaborate (Data () name vars variants) mv = do
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv vars
  vs <- traverse elaborateVariant variants
  constrain mv (foldr KindFun Type mvs)
  pure (Data mv name vars vs)
elaborate (Newtype () name vars variant) mv = do
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv vars
  v <- elaborateVariant variant
  constrain mv (foldr KindFun Type mvs)
  pure (Newtype mv name vars v)
elaborate (Class () name vars methods) mv = do
  handleKindSignature name mv
  void $ populateEnv (getFreeVars vars methods)
  methods_ <- traverse elaborateMethod methods
  mvs <- fmap KindMetaVar <$> traverse lookupName vars
  constrain mv (foldr KindFun Constraint mvs)
  pure (Class mv name vars methods_)
elaborate (KindSignature () name kind) mv = do
  constrain mv kind
  pure (KindSignature mv name kind)
elaborate (Instance () supers ctx) mv = do
  addContextToEnv supers
  supers_ <- traverse elaboratePred supers
  forM_ supers_ $ \m -> constrain (ann m) Constraint
  ctx_ <- elaboratePred ctx
  constrain (ann ctx_) Constraint
  constrain (ann ctx_) (KindMetaVar mv)
  pure (Instance mv supers_ ctx_)
elaborate (TypeSignature () name ctx typ) mv = do
  addContextToEnv ctx
  ctx_ <- traverse elaboratePred ctx
  forM_ ctx_ $ \m -> constrain (ann m) Constraint
  t <- elaborateType typ
  constrain (ann t) Type
  constrain mv (KindMetaVar (ann t))
  pure (TypeSignature mv name ctx_ t)
elaborate (Foreign () name typ) mv = do
  t <- elaborateType typ
  constrain (ann t) Type
  constrain (ann t) (KindMetaVar mv)
  pure (Foreign mv name t)
elaborate (Declaration () binding) mv = do
  constrain mv Type
  pure (Declaration mv binding)

addContextToEnv :: [Pred ()] -> Infer ()
addContextToEnv ctx = do
  let fvs = S.unions [ freeVars typ | Pred () _ typ <- ctx ]
  void (populateEnv (S.toList fvs))

elaboratePred :: Pred () -> Infer (Pred MetaVar)
elaboratePred (Pred () name typ) = do
  mv <- fresh
  class_ <- lookupName name
  type_ <- elaborateType typ
  constrain class_  (KindMetaVar (ann type_) --> Constraint)
  pure (Pred mv name type_)

getFreeVars :: [TyVar] -> [Method a] -> [TyVar]
getFreeVars vars methods = S.toList fvs
  where
    fvs =
      S.unions
      [ S.unions [ freeVars t | Method _ t <- methods ]
      , S.fromList vars
      ]

elaborateMethod :: Method () -> Infer (Method MetaVar)
elaborateMethod (Method name typ) = do
  t <- elaborateType typ
  pure (Method name t)

elaborateVariant :: Variant () -> Infer (Variant MetaVar)
elaborateVariant (Variant name types) = do
  ts <- traverse elaborateType types
  forM_ ts (\t -> constrain (ann t) Type)
  pure (Variant name ts)

elaborateType :: Type () -> Infer (Type MetaVar)
elaborateType (TypeVar () tyVar) = do
  mv <- lookupName tyVar
  pure (TypeVar mv tyVar)
elaborateType (TypeCon () tyCon) = do
  mv <- lookupName tyCon
  pure (TypeCon mv tyCon)
elaborateType (TypeApp () l r) = do
  fun <- elaborateType l
  arg <- elaborateType r
  mv <- fresh
  constrain
    (ann fun)
    (KindMetaVar (ann arg) --> KindMetaVar mv)
  pure (TypeApp mv fun arg)
elaborateType (TypeFun () l r) = do
  fun <- elaborateType (funTy `app` l)
  arg <- elaborateType r
  mv <- fresh
  constrain
    (ann fun)
    (KindMetaVar (ann arg) --> KindMetaVar mv)
  pure (TypeApp mv fun arg)
elaborateType (TypeMetaVar mv) =
  pure (TypeMetaVar mv)

funTy :: Type ()
funTy = tCon "(->)"

lookupKindEnv :: Name -> Infer (Maybe MetaVar)
lookupKindEnv name = do
  kindEnv <- gets kindEnv
  case M.lookup name kindEnv of
    Just scheme -> do
      mv <- fresh
      kind <- instantiate name scheme
      constrain mv kind
      pure (Just mv)
    _ -> pure Nothing

lookupName :: GetName name => name -> Infer MetaVar
lookupName named = do
  let name = getName named
  kindEnv <- gets kindEnv
  case M.lookup name kindEnv of
    Just scheme -> do
      mv <- fresh
      kind <- instantiate name scheme
      constrain mv kind
      pure mv
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> throwError (UnboundName name)
        Just v -> pure v

lookupNamedType :: GetName name => name -> Infer MetaVar
lookupNamedType named = do
  let name = getName named
  typEnv <- gets typeEnv
  case M.lookup name typEnv of
    Just scheme -> do
      mv <- fresh
      kind <- instantiateType name scheme
      constrainType mv kind
      pure mv
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> throwError (UnboundName name)
        Just v -> pure v

instantiate :: Name -> Scheme -> Infer Kind
instantiate name (Scheme vars kind) = do
  dbg $ "Instantiating Type: " <> name <> " :: " <> showKind kind
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (cataKind (replaceKind mapping) kind)
    where
      replaceKind mapping (KindVar v) =
         case M.lookup v mapping of
           Nothing -> KindVar v
           Just mv -> KindMetaVar mv
      replaceKind _ k = k

instantiateType :: Name -> TypeScheme -> Infer (Type Kind)
instantiateType name (TypeScheme vars typ) = do
  dbg $ "Instantiating Type: " <> name <> " :: " <> showType typ
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (cataType (replaceType mapping) typ)
    where
      replaceType mapping (TypeVar kind v) =
         case M.lookup v mapping of
           Nothing -> TypeVar kind v
           Just mv -> TypeMetaVar mv
      replaceType _ k = k

cataKind :: (Kind -> Kind) -> Kind -> Kind
cataKind f (KindFun k1 k2) =
  f $ KindFun (cataKind f k1) (cataKind f k2)
cataKind f (KindVar v) =
  f (KindVar v)
cataKind f (KindMetaVar v) =
  f (KindMetaVar v)
cataKind f Type =
  f Type
cataKind f Constraint =
  f Constraint

class Ann a where
  ann :: a ann -> ann

instance Ann Exp where
  ann (Var x _) = x
  ann (Lit x _) = x
  ann (App x _ _) = x

instance Ann Type where
  ann (TypeVar x _)   = x
  ann (TypeCon x _)   = x
  ann (TypeApp x _ _) = x
  ann (TypeFun x _ _) = x
  ann (TypeMetaVar _) = error "Called 'ann' on a MetaVar"

instance Ann Binding where
  ann (Binding t _ _ _) = t

annKind :: Decl kind typ -> kind
annKind (Data x _ _ _)    = x
annKind (TypeSyn x _ _ _) = x
annKind (Class x _ _ _)   = x
annKind (Newtype x _ _ _) = x
annKind (KindSignature x _ _) = x
annKind (TypeSignature x _ _ _) = x
annKind (Instance x _ _) = x
annKind (Foreign x _ _) = x
annKind (Declaration x _) = x

instance Ann Pred where
  ann (Pred x _ _)    = x

constrainType :: MetaVar -> Type Kind -> Infer ()
constrainType m t = constrainTypes (TypeMetaVar m) t

constrainTypes :: Type Kind -> Type Kind -> Infer ()
constrainTypes t1 t2 = do
  dbg ("Constraining... " <> showType t1 <> " = " <> showType t2)
  modify $ \e ->
    e { constraints = TypeEquality t1 t2 : constraints e
      }

constrain :: MetaVar -> Kind -> Infer ()
constrain m k = constrainKinds (KindMetaVar m) k

constrainKinds :: Kind -> Kind -> Infer ()
constrainKinds k1 k2 = do
  dbg ("Constraining... " <> showKind k1 <> " = " <> showKind k2)
  modify $ \e ->
    e { constraints = Equality k1 k2 : constraints e
      }

metaVars :: Kind -> Set MetaVar
metaVars (KindFun k1 k2) = metaVars k1 `S.union` metaVars k2
metaVars (KindMetaVar t) = S.singleton t
metaVars _ = mempty

metaVarsType :: Type Kind -> Set MetaVar
metaVarsType (TypeApp _ t1 t2) = metaVarsType t1 `S.union` metaVarsType t2
metaVarsType (TypeFun _ t1 t2) = metaVarsType t1 `S.union` metaVarsType t2
metaVarsType (TypeMetaVar t)   = S.singleton t
metaVarsType _ = mempty

freeVars :: Type a -> Set TyVar
freeVars (TypeVar _ tyVar) = S.singleton tyVar
freeVars (TypeFun _ x y) = freeVars x `S.union` freeVars y
freeVars (TypeApp _ x y) = freeVars x `S.union` freeVars y
freeVars _ = mempty

freeVarsExp :: Exp a -> Set Name
freeVarsExp (Var _ x) = S.singleton x
freeVarsExp (App _ f x) = freeVarsExp f `S.union` freeVarsExp x
freeVarsExp (Lit _ _) = mempty

generalizeDeclType :: Decl Kind (Type Kind) -> Maybe TypeScheme
generalizeDeclType (Declaration _ (Binding t _ _ _)) = Just (generalizeType t)
generalizeDeclType _ = Nothing

generalizeBinding :: Binding (Type Kind) -> TypeScheme
generalizeBinding = generalizeType . ann

generalizeType :: Type Kind -> TypeScheme
generalizeType typ = TypeScheme vars (cataType quantify typ)
  where
    metavars = S.toList (metaVarsType typ)
    mapping  = zip (sort metavars) [0..]
    subs     = M.fromList mapping
    vars     = sort [ TyVar (showT v) | v <- snd <$> mapping ]

    quantify (TypeMetaVar m) = TypeVar Type (TyVar (showT (subs M.! m)))
    quantify k               = k

    showT :: Int -> String
    showT k = combos !! k

    combos =
      concat
      [ pure <$> ['a'..'z']
      , (\k v -> k : show v) <$> ['a' .. 'z'] <*> [ 1 .. 99 :: Int ]
      ]

generalizeDecl :: Decl Kind () -> Scheme
generalizeDecl (Data k _ _ _)    = generalize k
generalizeDecl (TypeSyn k _ _ _) = generalize k
generalizeDecl (Class k _ _ _)   = generalize k
generalizeDecl (Newtype k _ _ _) = generalize k
generalizeDecl (KindSignature _ _ k) = generalize k
generalizeDecl (TypeSignature k _ _ _) = generalize k
generalizeDecl (Instance k _ _) = generalize k
generalizeDecl (Foreign k _ _) = generalize k
generalizeDecl (Declaration k _) = generalize k

generalize :: Kind -> Scheme
generalize kind = Scheme vars (cataKind quantify kind)
  where
    metavars = S.toList (metaVars kind)
    mapping = zip (sort metavars) [ 0 :: Int .. ]
    subs = M.fromList mapping
    vars = sort [ MkKindVar (showKind_ v)| v <- snd <$> mapping ]

    quantify (KindMetaVar m) = KindVar (MkKindVar (showKind_ (subs M.! m)))
    quantify k               = k

    showKind_ 0 = "k"
    showKind_ n = "k" <> show n

testInfer :: [Decl () ()] -> IO ()
testInfer decs = do
  dbg "Declarations..."
  dbg $ intercalate "\n" (showDecl <$> decs)
  result <- inferKinds decs
  case result of
    Left err -> print err
    Right decls -> do
      dbg "Inferred..."
      forM_ decls $ \decl -> do
        let
          scheme = generalize (annKind decl)
          name = getName decl
        dbg $ showDecl decl
        dbg $ name <> " :: " <> showScheme scheme

main :: IO ()
main = testInfer
  [ tree
  , lol
  , maybe
  , person
  , statet
  , state
  , thisthat
  , proxy
  , cofree
  , functor
  ]

int :: Decl () ()
int = Data () "Int" [] [ Variant "Int" [] ]

lol :: Decl () ()
lol = Data () "LOL" [ TyVar "a", TyVar "b" ]
  [ Variant "LOL" [ app (app (tCon "Either") (tVar "a")) (tVar "b") ]
  ]

maybe :: Decl () ()
maybe = Data () "Maybe" [ TyVar "a" ]
  [ Variant "Just" [ tVar "a" ]
  , Variant "Nothing" []
  ]

person :: Decl () ()
person = Data () "Person" []
  [ Variant "Person" [ tCon "String", tCon "Int" ]
  ]

statet :: Decl () ()
statet = TypeSyn () "Foo" [] (tCon "StateT")

proxy :: Decl () ()
proxy = Newtype () "Proxy" [ TyVar "k" ] (Variant "Proxy" [])

tree :: Decl () ()
tree = Data () "Tree" [ TyVar "a" ]
  [ Variant "Node" [ tVar "a", app (tCon "Tree") (tVar "a")
                   , app (tCon "Tree") (tVar "a")
                   ]
  ]

treefail :: Decl () ()
treefail = Data () "Tree" [ TyVar "a" ]
  [ Variant "Node" [ tVar "a", tCon "Tree", tCon "Tree" ]
  ]

state :: Decl () ()
state = TypeSyn () "State" [ TyVar "s", TyVar "a" ]
  (tCon "StateT" `app` tVar "s" `app` tCon "Identity" `app` tVar "a")

thisthat :: Decl () ()
thisthat = Data () "ThisThat" [ TyVar "l", TyVar "r" ]
  [ Variant "This" [ tVar "l" ]
  , Variant "That" [ tVar "r" ]
  ]

tConT :: String -> Type Kind
tConT n = TypeCon Type (TyCon n)

tCon :: String -> Type ()
tCon n = TypeCon () (TyCon n)

tVar :: String -> Type ()
tVar n = TypeVar () (TyVar n)

app :: Type () -> Type () -> Type ()
app x y = TypeApp () x y

fmap_ :: Type ()
fmap_ = (tVar "a" --> tVar "b")
    --> (tVar "f" `app` tVar "a")
    --> (tVar "f" `app` tVar "b")

fmapSyn :: Decl () typ
fmapSyn = TypeSyn () "Fmap" [TyVar "f", TyVar "a", TyVar "b" ] fmap_

-- type Fmap f a b = (a -> b) -> f a -> f b
-- Fmap :: (* -> *) -> * -> * -> *

cofree :: Decl () ()
cofree = Data () "Cofree" [ TyVar "f", TyVar "a" ]
  [ Variant "Cofree"
    [ tVar "a"
    , tVar "f" `app` (tCon "Cofree" `app` tVar "f" `app` tVar "a")
    ]
  ]

recfail :: Decl () typ
recfail = Data () "Rec" [ TyVar "f", TyVar "a" ]
  [ Variant "Rec"
    [ tVar "f"
    , app (tVar "f") (tVar "a")
    ]
  ]

-- tests that inference fails if a kind signature doesn't match
okFailTest :: IO ()
okFailTest
  = testInfer
  [ KindSignature () "OK" (Type --> Type)
  , TypeSyn () "OK" [] (tCon "Int")
  ]

okTest :: IO ()
okTest
  = testInfer
  [ KindSignature () "OK" Type
  , TypeSyn () "OK" [] (tCon "Int")
  ]

instTest :: IO ()
instTest
  = testInfer
  [ functor
  , Instance () [] (Pred () "Functor" (tCon "Maybe"))
  ]

instTestFail :: IO ()
instTestFail
  = testInfer
  [ functor
  , Instance () [] (Pred () "Functor" (tCon "Int"))
  ]

functor :: Decl () ()
functor = (Class () "Functor" [ TyVar "f" ] [Method "fmap" fmap_])

foreignTest :: IO ()
foreignTest
  = testInfer
  [ Foreign () "sin" (tCon "IO" `app` tCon "()")
  ]

-- f :: (Monad m, Eq (m a)) => a -> m a -> Bool
typeSigTest :: IO ()
typeSigTest = testInfer [ typeSig ]

typeSig :: Decl () typ
typeSig =
  TypeSignature
    ()
    "f"
    [ Pred () "Monad" (tVar "m")
    , Pred () "Eq" (tVar "m" `app` tVar "a")
    ]
    (tVar "a" --> (tVar "m" `app` tVar "a") --> tCon "Bool")
