module Main where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State  hiding (state)
import           Control.Monad.Writer
import           Data.Function
import           Data.List
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Set             (Set)
import qualified Data.Set             as S
import           Prelude              hiding (maybe)

type Name = String

newtype TyVar = TyVar { getTyVar :: Name }
  deriving (Show, Eq, Ord)

newtype TyCon = TyCon { unTyCon :: Name }
  deriving (Show, Eq)

newtype MetaVar = MetaVar { unMetaVar :: Int }
  deriving (Show, Eq, Num, Ord)

showMetaVar :: MetaVar -> String
showMetaVar mv = showKind (KindMetaVar mv)

data Decl a
  = Decl a Name [TyVar] [Variant a]
  | TypeSyn a Name [TyVar] (Type a)
  | Class a Name [TyVar] [Method a]
  | Instance a [Pred a] (Pred a)
  | Newtype a Name [TyVar] (Variant a)
  | KindSignature a Name Kind
  deriving (Show, Eq)

data Pred a = Pred a Name (Type a)
  deriving (Show, Eq)

data Method a = Method Name (Type a)
  deriving (Show, Eq)

class GetName f where
  getName :: f -> Name

instance GetName Name where
  getName = id

instance GetName (Decl a) where
  getName (Decl _ name _ _)        = name
  getName (TypeSyn _ name _ _)     = name
  getName (Class _ name _ _)       = name
  getName (Newtype _ name _ _)     = name
  getName (KindSignature _ name _) = name
  getName (Instance _ _ pred)      = getName pred

instance GetName (Pred a) where
  getName (Pred _ name _) = name

instance GetName (Type a) where
  getName (TypeVar _ name) = getName name
  getName (TypeCon _ name) = getName name

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
  deriving (Show, Eq)

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

showType :: Type ann -> String
showType t = showType_ (cataType funTy t)
  where
    funTy (TypeApp ann (TypeApp _ (TypeCon _ (TyCon "(->)")) f) x) =
      TypeFun ann f x
    funTy t = t

showType_ :: Type ann -> String
showType_ (TypeFun _ l r)   = showTypeVar l <> " -> " <> showType_ r
showType_ (TypeApp ann f x) = showType_ f <> " " <> showTypeVar x
showType_ t                 = showTypeVar t

showTypeVar (TypeVar ann (TyVar v)) = v
showTypeVar (TypeCon ann (TyCon c)) = c
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

data Constraint = Equality Kind Kind
  deriving (Eq, Ord)

instance Show Constraint where
  show = showConstraint

showConstraint :: Constraint -> String
showConstraint (Equality k1 k2) =
  intercalate "\n"
  [ showKind k1 <> " = " <> showKind k2
  ]

data InferState
  = InferState
  { env           :: Map Name MetaVar
  , kindEnv       :: Map Name Scheme
  , substitutions :: Map MetaVar Kind
  , var           :: Int
  , constraints   :: [Constraint]
  } deriving (Show, Eq)

type Subst = Map MetaVar Kind
type Infer = ExceptT Error (StateT InferState IO)

data Error
  = UnboundVar TyVar
  | UnboundName TyCon
  | UnificationFailed Kind Kind
  | OccursCheckFailed MetaVar Kind

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
  show (UnboundName con) =
    "Unbound Name: " <> show con
  show (UnboundVar tyvar) =
    "Unbound Var: " <> show tyvar
  show (OccursCheckFailed mv k) =
    intercalate "\n"
    [ "Occurs check failed"
    , "MetaVar: " <> showKind (KindMetaVar mv)
    , "Kind: " <> showKind k
    ]

class ShowAnn a where
  showAnn :: a -> String

instance ShowAnn () where
  showAnn () = ""

instance ShowAnn Kind where
  showAnn k = showScheme (generalize k)

instance ShowAnn MetaVar where
  showAnn (MetaVar m) = "<" <> show m <> ">"

showDecl :: ShowAnn ann => Decl ann -> String
showDecl (TypeSyn ann name vars typ) =
  intercalate " "
  [ "type"
  , if null (showAnn ann) then name else "(" <> name <> " :: " <> showAnn ann <> ")"
  , intercalate " " [ v | TyVar v <- vars ]
  , "="
  , showType typ
  ]
showDecl (Decl ann n vars xs) =
  intercalate " "
  [ "data"
  , if null (showAnn ann) then n else "( " <> n <> " :: " <> showAnn ann <> ")"
  , intercalate " " [ x | TyVar x <- vars ]
  , case xs of
      [] -> ""
      x : xs ->
        concat
        [ "\n  = " <> showVariant x
        , concat
          [ "\n  | " <> v
          | v <- fmap showVariant xs
          ]
        ]
  ]
showDecl (Class ann n vars methods) =
  intercalate " "
  [ "class"
  , if null (showAnn ann) then n else "( " <> n <> " :: " <> showAnn ann <> ")"
  , intercalate " " [ x | TyVar x <- vars ]
  , "where"
  , beforeAll "\n  " (showMethod <$> methods)
  ]
showDecl (Instance ann preds pred) =
  intercalate " "
  [ "instance"
  , case preds of
      [] -> showPred pred
      [x] -> intercalate ", " (showPred <$> preds) <> " => " <> showPred pred
      xs -> parens $ intercalate ", " (showPred <$> preds) <> " => " <> showPred pred
  , "::"
  , showAnn ann
  , "where"
  ]
showDecl (Newtype ann n vars variant) =
  intercalate " "
  [ "newtype"
  , if null (showAnn ann) then n else "( " <> n <> " :: " <> showAnn ann <> ")"
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

beforeAll :: [a] -> [[a]] -> [a]
beforeAll s xs = s <> intercalate s xs

showListInst = Instance () [Pred () "Show" (tCon "List" `app` tVar "a")]
  (Pred () "Show" (tVar "a"))

showMethod (Method name t) =
  intercalate " "
  [ name
  , "::"
  , showType t
  ]

showPred (Pred _ name typ) =
  name <> " " <> showTypeVar typ

showVariant :: Variant ann -> String
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
    where
      apply k v = do
        updateSubstitution k v
        updateConstraints k v

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

popConstraint :: Infer (Maybe Constraint)
popConstraint = do
  ccs <- gets constraints
  case ccs of
    c : cs -> do
      modify $ \s -> s { constraints = cs }
      pure (Just c)
    [] ->
      pure Nothing

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
    dumpSubs
    dumpConstraints
    dumpEnv
    dumpKindEnv

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

dumpConstraints :: Infer ()
dumpConstraints = do
  liftIO (putStrLn "\nDumping Constraints...")
  cs <- gets constraints
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

metaVarBind :: MetaVar -> Kind -> Infer (Maybe (MetaVar, Kind))
metaVarBind mv (KindMetaVar m) | mv == m = pure Nothing
metaVarBind m k = do
  dbg ("metaVarBind " ++ showMetaVar m ++ " (" ++ showKind k ++ ")")
  occursCheck m k
  pure (Just (m, k))

updateSubstitution :: MetaVar -> Kind -> Infer ()
updateSubstitution m k = modifySub (M.map replaceInState . M.insert m k)
  where
    replaceInState = cataKind $ \kind ->
      case kind of
        KindMetaVar mv | mv == m -> k
        z                        -> z

occursCheck :: MetaVar -> Kind -> Infer ()
occursCheck mv k = do
  when (mv `S.member` metaVars k) $
    throwError (OccursCheckFailed mv k)

modifySub :: (Subst -> Subst) -> Infer ()
modifySub f = do
  subs <- gets substitutions
  modify $ \s -> s { substitutions = f subs }

getKind :: MetaVar -> Infer Kind
getKind mv =
  M.findWithDefault (KindMetaVar mv) mv <$>
    gets substitutions

substitute
  :: Decl MetaVar
  -> Infer (Decl Kind)
substitute decl = do
  dbg "Substituting..."
  substituteDecl decl

substituteDecl :: Decl MetaVar -> Infer (Decl Kind)
substituteDecl (Class mv name vars methods) = do
  substitutedKind <- getKind mv
  typ' <- traverse substituteMethod methods
  pure (Class substitutedKind name vars typ')
substituteDecl (TypeSyn mv name vars typ) = do
  substitutedKind <- getKind mv
  typ' <- substituteType typ
  pure (TypeSyn substitutedKind name vars typ')
substituteDecl (Decl mv name vars variants) = do
  substitutedKind <- getKind mv
  substitutedVariants <- mapM substituteVariant variants
  pure (Decl substitutedKind name vars substitutedVariants)
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

substitutePred (Pred mv n typ) = do
  k <- getKind mv
  t <- substituteType typ
  pure (Pred k n t)

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

emptyState :: InferState
emptyState = InferState mempty defaultKindEnv mempty 0 []

defaultKindEnv :: Map String Scheme
defaultKindEnv = M.fromList
  [ ("Int", Scheme [] Type)
  , ("String", Scheme [] Type)
  , ("Either", Scheme [] (Type --> Type --> Type))
  , ("Maybe", Scheme [] (Type --> Type))
  , ("(->)", Scheme [] (Type --> Type --> Type))
  , ("StateT", Scheme [] (Type --> (Type --> Type) --> Type --> Type))
  , ("Identity", Scheme [] (Type --> Type))
  ]

infixr 9 -->
(-->) :: Kind -> Kind -> Kind
(-->) = KindFun

runInfer :: Infer a -> IO (Either Error a)
runInfer m = evalStateT (runExceptT m) emptyState

dbg :: MonadIO m => String -> m ()
dbg s = when shouldDebug $ liftIO (putStrLn s)

shouldDebug :: Bool
shouldDebug = True

inferDecls :: [Decl ()] -> IO (Either Error [Decl Kind])
inferDecls decls = runInfer $ do
  addKindSignatures decls
  forM decls $ \d -> do
    (scheme, decl) <- infer d
    addToKindEnv decl scheme
    decl <$ reset

addKindSignatures :: [Decl a] -> Infer ()
addKindSignatures decls = do
  let sigs = [ (name, generalize k) | KindSignature _ name k <- decls ]
  mapM_ (uncurry addToKindEnv) sigs

reset :: Infer ()
reset =
  modify $ \s ->
    s { env = mempty
      , substitutions = mempty
      , var = 0
      }

addToKindEnv :: GetName a => a -> Scheme -> Infer ()
addToKindEnv k v =
  modify $ \s -> s {
    kindEnv = M.insert (getName k) v (kindEnv s)
  }

infer :: Decl () -> Infer (Scheme, (Decl Kind))
infer decl = do
  dbg "Inferring..."
  elaborated <- elaborateDecl decl
  solve
  d <- substitute elaborated
  dump "Succeeded..."
  pure (generalizeDecl d, d)

populateEnv :: GetName name => [name] -> Infer [MetaVar]
populateEnv = mapM (addToEnv . getName)

addToEnv :: Name -> Infer MetaVar
addToEnv k = do
  v <- fresh
  modifyEnv (M.insert k v)
  pure v

modifyEnv :: (Map Name MetaVar -> Map Name MetaVar) -> Infer ()
modifyEnv f = modify $ \s -> s { env = f (env s) }

elaborateDecl :: Decl () -> Infer (Decl MetaVar)
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

elaborate :: Decl () -> MetaVar -> Infer (Decl MetaVar)
elaborate (TypeSyn () name vars typ) mv = do
  handleKindSignature name mv
  metaVars <- fmap KindMetaVar <$> populateEnv vars
  t <- elaborateType typ
  constrain mv (foldr KindFun (KindMetaVar (ann t)) metaVars)
  pure (TypeSyn mv name vars t)
elaborate (Decl () name vars variants) mv = do
  handleKindSignature name mv
  metaVars <- fmap KindMetaVar <$> populateEnv vars
  variants <- traverse elaborateVariant variants
  constrain mv (foldr KindFun Type metaVars)
  pure (Decl mv name vars variants)
elaborate (Newtype () name vars variant) mv = do
  handleKindSignature name mv
  metaVars <- fmap KindMetaVar <$> populateEnv vars
  variant_ <- elaborateVariant variant
  constrain mv (foldr KindFun Type metaVars)
  pure (Newtype mv name vars variant_)
elaborate (Class () name vars methods) mv = do
  handleKindSignature name mv
  void $ populateEnv (getFreeVars vars methods)
  methods_ <- traverse elaborateMethod methods
  mvs <- fmap KindMetaVar <$> traverse lookupTyVar vars
  constrain mv (foldr KindFun Constraint mvs)
  pure (Class mv name vars methods_)
elaborate (KindSignature () name kind) mv = do
  constrain mv kind
  pure (KindSignature mv name kind)
elaborate (Instance () supers ctx) mv = do
  supers_ <- traverse elaboratePred supers
  forM supers_ $ \m -> constrain (ann m) Constraint
  ctx_ <- elaboratePred ctx
  constrain (ann ctx_) Constraint
  constrain (ann ctx_) (KindMetaVar mv)
  pure (Instance mv supers_ ctx_)

elaboratePred :: Pred () -> Infer (Pred MetaVar)
elaboratePred (Pred () name typ) = do
  mv <- fresh
  class_ <- lookupTyCon (TyCon name)
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
  mv <- lookupTyVar tyVar
  pure (TypeVar mv tyVar)
elaborateType (TypeCon () tyCon) = do
  mv <- lookupTyCon tyCon
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

lookupTyCon :: TyCon -> Infer MetaVar
lookupTyCon con@(TyCon name) = do
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
        Nothing -> throwError (UnboundName con)
        Just v -> pure v

lookupTyVar :: TyVar -> Infer MetaVar
lookupTyVar var@(TyVar name) = do
  env <- gets env
  case M.lookup name env of
    Nothing -> throwError (UnboundVar var)
    Just v  -> pure v

instantiate :: Name -> Scheme -> Infer Kind
instantiate name (Scheme vars kind) = do
  dbg $ "Instantiating: " <> name <> " :: " <> showKind kind
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (cataKind (replaceKind mapping) kind)
    where
      replaceKind mapping (KindVar v) =
         case M.lookup v mapping of
           Nothing -> KindVar v
           Just mv -> KindMetaVar mv
      replaceKind _ k = k

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

instance Ann Type where
  ann (TypeVar x _)   = x
  ann (TypeCon x _)   = x
  ann (TypeApp x _ _) = x
  ann (TypeFun x _ _) = x

instance Ann Decl where
  ann (Decl x _ _ _)    = x
  ann (TypeSyn x _ _ _) = x
  ann (Class x _ _ _)   = x
  ann (Newtype x _ _ _) = x
  ann (KindSignature x _ _) = x
  ann (Instance x _ _) = x

instance Ann Pred where
  ann (Pred x _ _)    = x

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

freeVars :: Type a -> Set TyVar
freeVars (TypeVar _ tyVar) = S.singleton tyVar
freeVars (TypeFun _ x y) = freeVars x `S.union` freeVars y
freeVars (TypeApp _ x y) = freeVars x `S.union` freeVars y
freeVars _ = mempty

generalizeDecl :: Decl Kind -> Scheme
generalizeDecl (Decl k _ _ _)    = generalize k
generalizeDecl (TypeSyn k _ _ _) = generalize k
generalizeDecl (Class k _ _ _)   = generalize k
generalizeDecl (Newtype k _ _ _) = generalize k
generalizeDecl (KindSignature _ _ k) = generalize k
generalizeDecl (Instance k _ _) = generalize k

generalize :: Kind -> Scheme
generalize kind = Scheme vars (cataKind quantify kind)
  where
    metavars = S.toList (metaVars kind)
    mapping = zip (sort metavars) [0..]
    subs = M.fromList mapping
    vars = sort [ MkKindVar (showKind v)| v <- snd <$> mapping ]

    quantify (KindMetaVar m) = KindVar (MkKindVar (showKind (subs M.! m)))
    quantify k               = k

    showKind 0 = "k"
    showKind n = "k" <> show n

testInfer :: [Decl ()] -> IO ()
testInfer decs = do
  dbg "Declarations..."
  dbg $ intercalate "\n" (showDecl <$> decs)
  result <- inferDecls decs
  case result of
    Left err -> print err
    Right decls -> do
      dbg "Inferred..."
      forM_ decls $ \decl -> do
        let
          scheme = generalize (ann decl)
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

int :: Decl ()
int = Decl () "Int" [] [ Variant "Int" [] ]

lol :: Decl ()
lol = Decl () "LOL" [ TyVar "a", TyVar "b" ]
  [ Variant "LOL" [ app (app (tCon "Either") (tVar "a")) (tVar "b") ]
  ]

maybe :: Decl ()
maybe = Decl () "Maybe" [ TyVar "a" ]
  [ Variant "Just" [ tVar "a" ]
  , Variant "Nothing" []
  ]

person :: Decl ()
person = Decl () "Person" []
  [ Variant "Person" [ tCon "String", tCon "Int" ]
  ]

statet :: Decl ()
statet = TypeSyn () "Foo" [] (tCon "StateT")

proxy :: Decl ()
proxy = Newtype () "Proxy" [ TyVar "k" ] (Variant "Proxy" [])

tree :: Decl ()
tree = Decl () "Tree" [ TyVar "a" ]
  [ Variant "Node" [ tVar "a", app (tCon "Tree") (tVar "a")
                   , app (tCon "Tree") (tVar "a")
                   ]
  ]

treefail :: Decl ()
treefail = Decl () "Tree" [ TyVar "a" ]
  [ Variant "Node" [ tVar "a", tCon "Tree", tCon "Tree" ]
  ]

state :: Decl ()
state = TypeSyn () "State" [ TyVar "s", TyVar "a" ]
  (tCon "StateT" `app` tVar "s" `app` tCon "Identity" `app` tVar "a")

thisthat :: Decl ()
thisthat = Decl () "ThisThat" [ TyVar "l", TyVar "r" ]
  [ Variant "This" [ tVar "l" ]
  , Variant "That" [ tVar "r" ]
  ]

tCon :: String -> Type ()
tCon n = TypeCon () (TyCon n)

tVar :: String -> Type ()
tVar n = TypeVar () (TyVar n)

app :: Type () -> Type () -> Type ()
app x y = TypeApp () x y

(--->) = TypeFun ()
infixr 9 --->

fmap_ :: Type ()
fmap_ = (tVar "a" ---> tVar "b")
    ---> (tVar "f" `app` tVar "a")
    ---> (tVar "f" `app` tVar "b")

fmapSyn = TypeSyn () "Fmap" [TyVar "f", TyVar "a", TyVar "b" ] fmap_

-- type Fmap f a b = (a -> b) -> f a -> f b
-- Fmap :: (* -> *) -> * -> * -> *

cofree :: Decl ()
cofree = Decl () "Cofree" [ TyVar "f", TyVar "a" ]
  [ Variant "Cofree"
    [ tVar "a"
    , tVar "f" `app` (tCon "Cofree" `app` tVar "f" `app` tVar "a")
    ]
  ]

recfail = Decl () "Rec" [ TyVar "f", TyVar "a" ]
  [ Variant "Rec"
    [ tVar "f"
    , app (tVar "f") (tVar "a")
    ]
  ]

-- tests that inference fails if a kind signature doesn't match
okFailTest
  = testInfer
  [ KindSignature () "OK" (Type --> Type)
  , TypeSyn () "OK" [] (tCon "Int")
  ]

okTest
  = testInfer
  [ KindSignature () "OK" Type
  , TypeSyn () "OK" [] (tCon "Int")
  ]

instTest
  = testInfer
  [ functor
  , Instance () [] (Pred () "Functor" (tCon "Maybe"))
  ]

instTestFail
  = testInfer
  [ functor
  , Instance () [] (Pred () "Functor" (tCon "Int"))
  ]

functor :: Decl ()
functor = (Class () "Functor" [ TyVar "f" ] [Method "fmap" fmap_])
