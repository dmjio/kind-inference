{-# LANGUAGE KindSignatures #-}
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

newtype TyVar = TyVar { getTyVar :: String }
  deriving (Show, Eq)

newtype TyCon = TyCon { unTyCon :: String }
  deriving (Show, Eq)

newtype MetaVar = MetaVar { unMetaVar :: Int }
  deriving (Show, Eq, Num, Ord)

showMetaVar :: MetaVar -> String
showMetaVar mv = showKind (KindMetaVar mv)

data Decl a
  = Decl a Name [TyVar] [Variant a]
  | TypeSyn a Name [TyVar] (Type a)
  deriving (Show, Eq)

class GetName f where
  getName :: f -> Name

instance GetName (Decl a) where
  getName (Decl _ name _ _) = name
  getName (TypeSyn _ name _ _) = name

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
  | TypeApp a (Type a) (Type a)
  deriving (Show, Eq)

newtype KindVar = MkKindVar { unKindVar :: String }
  deriving (Show, Eq, Ord)

-- | A representation of a kind.
data Kind
  = Type
  | KindFun Kind Kind
  | KindVar KindVar
  | KindMetaVar MetaVar
  deriving (Show, Eq, Ord)

data Scheme = Scheme [KindVar] Kind
  deriving (Show, Eq)

showKind :: Kind -> String
showKind (KindFun f x) = showKind f <> " -> " <> showKindVar x
showKind x = showKindVar x

showKindVar :: Kind -> String
showKindVar (KindVar (MkKindVar v)) = v
showKindVar (KindMetaVar (MetaVar v)) = "{" <> show v <> "}"
showKindVar Type = "*"
showKindVar x = "(" <> showKind x <> ")"

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
  | SubstitutionFailure MetaVar

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
  show (SubstitutionFailure mv) =
    "Substitution fail: " <> showKind (KindMetaVar mv)
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
showDecl (Decl ann n vars (x:xs)) =
  intercalate " "
  [ "data"
  , if null (showAnn ann) then n else "( " <> n <> " :: " <> showAnn ann <> ")"
  , intercalate " " [ x | TyVar x <- vars ]
  , "\n  = " <> showVariant x
  , concat
    [ "\n  | " <> v
    | v <- fmap showVariant xs
    ]
  ]

showVariant :: Variant ann -> String
showVariant (Variant n []) = n
showVariant (Variant n tvs)
  = intercalate " " (n : fmap showType tvs)

showType :: Type ann -> String
showType (TypeApp ann f x) = "(" <> showType f <> " " <> showTypeVar x <> ")"
showType t = showTypeVar t

showTypeVar (TypeVar ann (TyVar v)) = v
showTypeVar (TypeCon ann (TyCon c)) = c
showTypeVar x = showType x

solveConstraints :: Infer ()
solveConstraints = do
  dbg "Solving..."
  fix $ \loop -> do
    cs <- gets constraints
    case cs of
      [] -> pure ()
      Equality k1 k2 : es -> do
        subs <- unify k1 k2
        extend subs
        modify $ \s -> s { constraints = es }
        loop

unify :: Kind -> Kind -> Infer Subst
unify Type Type = pure mempty
unify (KindVar x) (KindVar y) | x == y = pure mempty
unify (KindMetaVar x) (KindMetaVar y) | x == y = pure mempty
unify (KindFun x1 y1) (KindFun x2 y2) = do
  constrainKinds x1 x2
  constrainKinds y1 y2
  pure mempty
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

showSub :: (MetaVar,Kind) -> String
showSub (k,v) = showMetaVar k <> " : " <> showKind v

showSubs :: Subst -> String
showSubs subst = intercalate "\n" (showSub <$> M.toList subst)

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

metaVarBind :: MetaVar -> Kind -> Infer Subst
metaVarBind m k1 = do
  subs <- gets substitutions
  case (M.lookup m subs, k1) of
    (Just k2, _) ->
      unify k1 k2
    (Nothing, KindMetaVar mv) ->
      case M.lookup mv subs of
        Just found ->
          unify (KindMetaVar m) found
        Nothing -> do
          replaceSubs m k1
          pure (M.singleton m k1)
    (Nothing, _) -> do
      occursCheck m k1
      replaceSubs m k1
      pure (M.singleton m k1)

replaceSubs :: MetaVar -> Kind -> Infer ()
replaceSubs m k = modify $ \s -> s {
    substitutions = M.map (replaceInState m k) (substitutions s)
  } where
      replaceInState :: MetaVar -> Kind -> Kind -> Kind
      replaceInState mv x = cataKind $ \k ->
        case k of
          KindMetaVar mv' | mv' == mv -> x
          z -> z

occursCheck :: MetaVar -> Kind -> Infer ()
occursCheck mv k = do
  when (mv `S.member` metaVars k) $
    throwError (OccursCheckFailed mv k)

extend :: Subst -> Infer ()
extend k = do
  s <- gets substitutions
  modify $ \x -> x { substitutions = s `M.union` k }

getKind :: MetaVar -> Infer Kind
getKind mv =
  M.findWithDefault (KindMetaVar mv) mv <$>
    gets substitutions

substitute :: Decl MetaVar -> Infer (Decl Kind)
substitute (TypeSyn mv name vars typ) = do
  dbg "Substituting..."
  substitutedKind <- getKind mv
  typ' <- substituteType typ
  pure (TypeSyn substitutedKind name vars typ')
substitute (Decl mv name vars variants) = do
  dbg "Substituting..."
  substitutedKind <- getKind mv
  substitutedVariants <- mapM substituteVariant variants
  pure (Decl substitutedKind name vars substitutedVariants)
    where
      substituteVariant (Variant name types) = do
        substituted <- traverse substituteType types
        pure (Variant name substituted)

substituteType :: Type MetaVar -> Infer (Type Kind)
substituteType (TypeCon mv tyCon) = do
  kind <- getKind mv
  pure (TypeCon kind tyCon)
substituteType (TypeApp mv f x) = do
  TypeApp
    <$> getKind mv
    <*> substituteType f
    <*> substituteType x
substituteType (TypeVar mv t) = do
  kind <- getKind mv
  pure (TypeVar kind t)

emptyState :: InferState
emptyState = InferState mempty defaultKindEnv mempty 0 []

defaultKindEnv
  = M.fromList
    [ ("Int", Scheme [] Type)
    , ("String", Scheme [] Type)
    , ("Either", Scheme [] (Type --> Type --> Type))
    , ("(->)", Scheme [] (Type --> Type --> Type))
    , ("StateT", Scheme [] (Type --> (Type --> Type) --> Type --> Type))
    , ("Identity", Scheme [] (Type --> Type))
    ]

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
  forM decls $ \d -> do
    (scheme, decl) <- infer d
    addToKindEnv scheme decl
    decl <$ reset

reset :: Infer ()
reset =
  modify $ \s ->
    s { env = mempty
      , substitutions = mempty
      , var = 0
      }

addToKindEnv :: Scheme -> Decl a -> Infer ()
addToKindEnv scheme d =
  modify $ \s -> s {
    kindEnv = M.insert (getName d) scheme (kindEnv s)
  }

infer :: Decl () -> Infer (Scheme, (Decl Kind))
infer decl = do
  dbg "Inferring..."
  elaborated <- elaborateDecl decl
  solveConstraints
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
    where
      modifyEnv f =
        modify $ \s -> s {
          env = f (env s)
        }

elaborateDecl :: Decl () -> Infer (Decl MetaVar)
elaborateDecl decl = do
  dbg "Elaborating..."
  elaborate decl =<< addToEnv (getName decl)

elaborate :: Decl () -> MetaVar -> Infer (Decl MetaVar)
elaborate (TypeSyn () name vars typ) mv = do
  metaVars <- fmap KindMetaVar <$> populateEnv vars
  t <- elaborateType typ
  constrain mv (foldr KindFun (KindMetaVar (ann t)) metaVars)
  pure (TypeSyn mv name vars t)
elaborate (Decl () name vars variants) mv = do
  metaVars <- fmap KindMetaVar <$> populateEnv vars
  variants <- traverse elaborateVariant variants
  constrain mv (foldr KindFun Type metaVars)
  pure (Decl mv name vars variants)

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
    (KindFun (KindMetaVar (ann arg)) (KindMetaVar mv))
  pure (TypeApp mv fun arg)

lookupTyCon :: TyCon -> Infer MetaVar
lookupTyCon con@(TyCon name) = do
  kindEnv <- gets kindEnv
  case M.lookup name kindEnv of
    Just scheme -> do
      mv <- fresh
      kind <- instantiate scheme
      dbg $ "Instantiating: " <> name <> " :: " <> showKind kind
      constrain mv kind
      pure mv
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> throwError (UnboundName con)
        Just v -> do
          mv <- fresh
          constrain v (KindMetaVar mv)
          pure v

lookupTyVar :: TyVar -> Infer MetaVar
lookupTyVar var@(TyVar name) = do
  env <- gets env
  case M.lookup name env of
    Nothing -> throwError (UnboundVar var)
    Just v -> pure v

instantiate :: Scheme -> Infer Kind
instantiate (Scheme vars kind) = do
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (replace mapping kind)
    where
      replace :: Map KindVar MetaVar -> Kind -> Kind
      replace mapping = cataKind replaceKind
        where
          replaceKind :: Kind -> Kind
          replaceKind (KindVar v) =
            case M.lookup v mapping of
              Nothing -> KindVar v
              Just mv -> KindMetaVar mv
          replaceKind kind = kind

cataKind :: (Kind -> Kind) -> Kind -> Kind
cataKind f Type =
  f Type
cataKind f (KindFun k1 k2) =
  f $ KindFun (cataKind f k1) (cataKind f k2)
cataKind f (KindVar v) =
  f (KindVar v)
cataKind f (KindMetaVar v) =
  f (KindMetaVar v)

class Ann a where
  ann :: a ann -> ann

instance Ann Type where
  ann (TypeVar x _) = x
  ann (TypeCon x _) = x
  ann (TypeApp x _ _) = x

instance Ann Decl where
  ann (Decl x _ _ _) = x
  ann (TypeSyn x _ _ _) = x

constrain :: MetaVar -> Kind -> Infer ()
constrain m k = do
  modify $ \e ->
    e { constraints = Equality (KindMetaVar m) k : constraints e
      }

constrainKinds :: Kind -> Kind -> Infer ()
constrainKinds k1 k2 = do
  modify $ \e ->
    e { constraints = Equality k1 k2 : constraints e
      }

metaVars :: Kind -> Set MetaVar
metaVars (KindFun k1 k2) =
  metaVars k1 `S.union` metaVars k2
metaVars (KindMetaVar t) = S.singleton t
metaVars _ = mempty

generalizeDecl :: Decl Kind -> Scheme
generalizeDecl (Decl k _ _ _) = generalize k
generalizeDecl (TypeSyn k _ _ _) = generalize k

generalize :: Kind -> Scheme
generalize kind = Scheme vars (cataKind quantify kind)
  where
    metavars = S.toList (metaVars kind)
    mapping = zip (sort metavars) [0..]
    subs = M.fromList mapping
    vars = [ MkKindVar (showKind v)| v <- snd <$> mapping ]

    quantify (KindMetaVar m) = KindVar (MkKindVar (showKind (subs M.! m)))
    quantify k = k

    showKind 0 = "k"
    showKind n = "k" <> show n

testInfer :: [Decl ()] -> IO ()
testInfer decs = do
  dbg "Declarations..."
  mapM_ (putStrLn . showDecl) decs
  result <- inferDecls decs
  case result of
    Left err -> print err
    Right decls -> do
      putStrLn "Inferred..."
      forM_ decls $ \decl -> do
        let
          scheme = generalize (ann decl)
          name = getName decl
        putStrLn ""
        putStrLn $ showDecl decl
        putStrLn $ name <> " :: " <> showScheme scheme

main :: IO ()
main =
  testInfer
  [ tree
  , lol
  , maybe
  , person
  , statet
  , state
  , thisthat
  , proxy
  ]

-- ==== test fixtures
int :: Decl ()
int = Decl () "Int" [] [ Variant "Int" [] ]

-- data LOL = LOL (Either a b)
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
proxy = Decl () "Proxy" [ TyVar "k" ] [Variant "Proxy" []]

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
  (app (app (app (tCon "StateT") (tVar "s")) (tCon "Identity")) (tVar "a"))

thisthat :: Decl ()
thisthat = Decl () "ThisThat" [ TyVar "l", TyVar "r" ]
  [ Variant "This" [ tVar "l" ]
  , Variant "That" [ tVar "r" ]
  ]

cofree :: Decl ()
cofree = Decl () "Cofree" [ TyVar "a", TyVar "k" ]
  [ Variant "Cofree"
    [ tVar "k"
    , app
      (tVar "a")
      (app
        (app (tCon "Cofree") (tVar "a"))
        (tVar "k"))
    ]
  ]

--

tCon :: String -> Type ()
tCon n = TypeCon () (TyCon n)

tVar :: String -> Type ()
tVar n = TypeVar () (TyVar n)

app :: Type () -> Type () -> Type ()
app x y = TypeApp () x y

