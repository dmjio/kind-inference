{-# LANGUAGE NoMonomorphismRestriction #-}
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
  = Data kind Name [Type kind] [Variant kind typ]
  | TypeSyn kind Name [Type kind] (Type kind)
  | Class kind Name [Type kind] [Method kind]
  | Instance [Pred kind] (Pred kind)
  | Newtype kind Name [Type kind] (Variant kind typ)
  | KindSignature Name Kind
  | Foreign Name (Type kind)
  | TypeSig Name [Pred kind] (Type kind)
  | Fixity Fixity (Maybe Int) [Name]
  | Declaration typ [Binding kind typ]
  deriving (Show, Eq)

data Fixity
  = Infix
  | Infixl
  | Infixr
  deriving (Show, Eq)

data Binding kind typ
  = Binding typ Name [Pat kind typ] (Exp kind typ)
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

data Exp kind typ
  = Var typ Name
  | Lit typ Lit
  | App typ (Exp kind typ) (Exp kind typ)
  | Lam typ [Exp kind typ] (Exp kind typ)
  -- Patterns
  | As typ Name (Pat kind typ)
  | Con typ Name [Pat kind typ]
  | Wildcard typ
  -- Others
  | TypeAnn (Type kind) (Exp kind typ)
  deriving (Show, Eq)

type Pat typ kind = Exp typ kind

data Lit
  = LitInt Int
  | LitChar Char
  | LitString String
  | LitDouble Double
  | LitBool Bool
  deriving (Show, Eq)

data Pred a = Pred Name (Type a)
  deriving (Show, Eq, Ord)

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
  getName (KindSignature name _)   = name
  getName (Instance _ p)           = getName p
  getName (Foreign name _)         = name
  getName (TypeSig name _ _) = name
  getName (Fixity _ _ names)       = intercalate "," names
  getName (Declaration _ [])       = error "no bindings"
  getName (Declaration _ (b:_))    = getName b

instance GetName (Binding kind a) where
  getName (Binding _ name _ _) = name

instance GetName (Pred a) where
  getName (Pred name _) = name

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

data Variant kind typ
  = Variant Name [Type kind] typ
  deriving (Show, Eq)

data Type k
  = TypeVar k TyVar
  | TypeCon k TyCon
  | TypeFun k (Type k) (Type k)
  | TypeApp k (Type k) (Type k)
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
  | KindScheme Scheme
  deriving (Show, Eq, Ord)

data Scheme = Scheme [Name] Kind
  deriving (Show, Eq, Ord)

showKind :: Kind -> String
showKind (KindFun f x) = showKindVar f <> " -> " <> showKind x
showKind x             = showKindVar x

showKindVar :: Kind -> String
showKindVar (KindVar (MkKindVar v))   = v
showKindVar (KindMetaVar (MetaVar v)) = "{" <> show v <> "}"
showKindVar Type                      = "*"
showKindVar Constraint                = "Constraint"
showKindVar (KindScheme scheme)       = showScheme scheme
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
showTypeVar (TypeVar k (TyVar v))
  | null (showAnn k) = v
  | otherwise = parens (v <> " :: " <> showAnn k)
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
    , intercalate " " vars
    , "."
    , showKind k
    ]

showTypeScheme :: TypeScheme -> String
showTypeScheme (TypeScheme [] k) = showType k
showTypeScheme (TypeScheme vars k) =
  intercalate " "
    [ "forall"
    , intercalate " " vars
    , "."
    , showType k
    ]

data Constraint
  = Equality Kind Kind
  | TypeEquality (Type Kind) (Type Kind)
  | ClassConstraint (Pred Kind)
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
showConstraint (ClassConstraint p) =
  intercalate "\n"
  [ showPred p
  ]

data InferState
  = InferState
  { env               :: Map Name MetaVar
  , kindEnv           :: Map Name Scheme
  , typeEnv           :: Map Name TypeScheme
  , substitutions     :: Map MetaVar Kind
  , typeSubstitutions :: Map MetaVar (Type Kind)
  , var               :: Int
  , constraints       :: [Constraint]
  } deriving (Show, Eq)

type Subst = Map MetaVar Kind
type Infer = ExceptT Error (StateT InferState IO)

data Error
  = UnboundName Name
  | UnificationFailed Kind Kind
  | UnificationFailedType (Type Kind) (Type Kind)
  | OccursCheckFailed MetaVar Kind
  | OccursCheckFailedType MetaVar (Type Kind)
  | Doesn'tOccurInInstanceHead Name (Pred ()) (Pred ())

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
    [ "Unification type failed"
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
  show (Doesn'tOccurInInstanceHead name superPred@(Pred superName _) p) =
    intercalate "\n"
    [ intercalate " "
      [ "Variable"
      , name
      , "in superclass"
      , superName
      , "doesn't appear in instance context"
      , showPred p
      ]
    , "Variable: " <> name
    , "Head: " <> showPred superPred
    , "Context: " <> showPred p
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
  , if null (showAnn a)
    then name
    else parens (name <> " :: " <> showAnn a)
  , if null vars
      then "="
      else intercalate " " (showTypeVar <$> vars) <> " ="
  , showType typ
  ]
showDecl (Data a n vars xs) =
  intercalate " "
  [ "data"
  , if null (showAnn a)
    then n
    else parens (n <> " :: " <> showAnn a)
  , intercalate " " (showTypeVar <$> vars)
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
  , intercalate " " (showTypeVar <$> vars)
  , "where"
  , beforeAll "\n  " (showMethod <$> methods)
  ]
showDecl (Instance ps p) =
  intercalate " "
  [ "instance"
  , case ps of
      [] -> showPred p
      [x] -> showPred x <> " => " <> showPred p
      xs -> parens $ intercalate ", " (showPred <$> xs) <> " => " <> showPred p
  , "where"
  ]
showDecl (Newtype a n vars variant) =
  intercalate " "
  [ "newtype"
  , if null (showAnn a)
    then n
    else parens (n <> " :: " <> showAnn a)
  , if null vars
      then "="
      else intercalate " " (showTypeVar <$> vars) <> " ="
  , showVariant variant
  ]
showDecl (KindSignature name kind) =
  intercalate " "
  [ "type"
  , name
  , "::"
  , showKind kind
  ]
showDecl (TypeSig name preds t) =
  intercalate " " $
  [ name
  , "::"
  , case preds of
      [] -> showType t
      [x] -> showPred x <> " => " <> showType t
      xs -> parens (intercalate ", " (showPred <$> xs)) <> " => " <> showType t
  ]

showDecl (Foreign name typ) =
  intercalate " "
  [ "foreign"
  , "import"
  , "unsafe"
  , "ccall"
  , name
  , "::"
  , showType typ
  ]
showDecl (Declaration _ bindings) =
  intercalate "\n" (showBinding <$> bindings)
showDecl (Fixity fixity precedence names) =
  intercalate " "
  [ showFixity fixity <>
      case precedence of
        Nothing -> ""
        Just x -> " " <> show x
  , intercalate ", " names
  ]

showFixity :: Fixity -> String
showFixity Infix  = "infix"
showFixity Infixl = "infixl"
showFixity Infixr = "infixr"

showBinding :: (ShowAnn typ, ShowAnn kind) => Binding kind typ -> String
showBinding (Binding _ name args body) =
  intercalate " "
  [ name
  , if null args
       then "= " <> showExp body
       else intercalate " " (showExp <$> args) <> " = " <> showExp body
  ]

showExp :: ShowAnn kind => Exp kind typ -> String
showExp (App _ f x) = showExpVar f <> " " <> showExp x
showExp x = showExpVar x

showExpVar :: ShowAnn kind => Exp kind typ -> String
showExpVar (Var _ name) = name
showExpVar (Lit _ lit) = showLit lit
showExpVar (Wildcard _) = "_"
showExpVar (TypeAnn t e) = parens (showExp e <> " :: " <> showType t)
showExpVar (Lam _ args body) =
  parens $ '\\' : intercalate " "
    [ intercalate " " (showExpVar <$> args)
    , "->"
    , showExpVar body
    ]
showExpVar (As _ name e) =
  concat
    [ name
    , "@"
    , showExpVar e
    ]
showExpVar (Con _ name args) =
  case args of
    [] -> name
    _ -> parens $
     intercalate " "
      [ name
      , intercalate " " (showExpVar <$> args)
      ]
showExpVar x = parens (showExp x)

showLit :: Lit -> String
showLit (LitInt x) = show x
showLit (LitChar x) = "'" <> [x] <> "'"
showLit (LitString x) = "\"" <> x <> "\""
showLit (LitDouble x) = show x
showLit (LitBool x) = show x

beforeAll :: [a] -> [[a]] -> [a]
beforeAll _ [] = []
beforeAll s xs = s <> intercalate s xs

showListInst :: Decl () typ
showListInst = Instance [Pred "Show" (tCon "List" `app` tVar "a")]
  (Pred "Show" (tVar "a"))

showMethod :: ShowAnn ann => Method ann -> String
showMethod (Method name t) =
  intercalate " "
  [ name
  , "::"
  , showType t
  ]

showPred :: ShowAnn ann => Pred ann -> String
showPred (Pred name typ) =
  intercalate " "
  [ name
  , showType typ
  ]

showVariant
  :: (ShowAnn typ, ShowAnn ann)
  => Variant ann typ
  -> String
showVariant (Variant n [] t) =
  concat $ n :
  [ " :: " <> showAnn t
  | not $ null (showAnn t)
  ]
showVariant (Variant n ts t) =
  mconcat $
  [ intercalate " " (n : fmap showTypeVar ts)
  ] ++
  [ " :: " <> showAnn t
  | not $ null (showAnn t)
  ]

solve :: Infer ()
solve = do
  dbg "Solving..."
  sortConstraints
  solveConstraints

sortConstraints :: Infer ()
sortConstraints = do
  dbg "Sorting constraints..."
  cs <- gets constraints
  let isClassConstraint ClassConstraint{} = True
      isClassConstraint _ = False
  setConstraints (sortBy (compare `on` isClassConstraint) cs)

setConstraints :: [Constraint] -> Infer ()
setConstraints xs = modify $ \s -> s { constraints = xs }

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
    Just (ClassConstraint p) -> do
      classConstraint p
      solveConstraints
    where
      apply k v = do
        updateSubstitution k v
        updateConstraints k v

      applyType k v = do
        updateSubstitutionType k v
        updateConstraintsType k v

      classConstraint p =
        dbg ("Solving class constraint for type: " <> show p)

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

kindCheck :: Kind -> Kind -> Infer ()
kindCheck k1 k2 =
  when (k1 /= k2) $ bail (UnificationFailed k1 k2)

bail :: Error -> Infer a
bail e = do
  dump "bailing out"
  liftIO (print e)
  throwError e

unifyType
  :: Type Kind
  -> Type Kind
  -> Infer (Maybe (MetaVar, Type Kind))
unifyType (TypeVar k1 x) (TypeVar k2 y)
  | x == y = do
      kindCheck k1 k2
      pure Nothing
unifyType (TypeCon k1 x) (TypeCon k2 y)
  | x == y = do
      kindCheck k1 k2
      pure Nothing
unifyType (TypeMetaVar x) (TypeMetaVar y) | x == y = pure Nothing
unifyType (TypeApp k1 x1 y1) (TypeApp k2 x2 y2) = do
  kindCheck k1 k2
  constrainTypes x1 x2
  constrainTypes y1 y2
  pure Nothing
unifyType (TypeFun k1 x1 y1) (TypeFun k2 x2 y2) = do
  kindCheck k1 k2
  constrainTypes x1 x2
  constrainTypes y1 y2
  pure Nothing
unifyType (TypeMetaVar x) y = metaVarBindType x y
unifyType x (TypeMetaVar y) = metaVarBindType y x
unifyType t1 t2 =
  bail (UnificationFailedType t1 t2)

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
  bail (UnificationFailed k1 k2)

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

class Substitution k where
  metaVars :: k -> Set MetaVar
  freeVars :: k -> Set Name

instance Substitution (Pred a) where
  freeVars (Pred _ typ) = freeVars typ
  metaVars (Pred _ typ) = metaVars typ

instance Substitution a => Substitution [a] where
  freeVars = S.unions . fmap freeVars
  metaVars = S.unions . fmap metaVars

instance Substitution (Exp kind a) where
  metaVars _ = mempty

  freeVars (Var _ x)         = S.singleton x
  freeVars (App _ f x)       = freeVars f `S.union` freeVars x
  freeVars (Lam _ args body) = freeVars body `S.difference` freeVars args
  freeVars (Lit _ _)       = mempty
  freeVars (Wildcard _)    = mempty
  freeVars (TypeAnn _ e)   = freeVars e

  -- NOTE: since this is used when elaborating binding args
  -- we only return the name
  freeVars (As _ name _)   = S.singleton name

  freeVars (Con _ _ args)   = freeVars args

instance Substitution Kind where
  metaVars (KindMetaVar mv) = S.singleton mv
  metaVars (KindFun k1 k2)  = metaVars k1 `S.union` metaVars k2
  metaVars _ = mempty

  freeVars (KindVar (MkKindVar k)) = S.singleton k
  freeVars (KindFun k1 k2)         = freeVars k1 `S.union` freeVars k2
  freeVars _ = mempty

instance Substitution (Type a) where
  metaVars (TypeApp _ t1 t2) = metaVars t1 `S.union` metaVars t2
  metaVars (TypeFun _ t1 t2) = metaVars t1 `S.union` metaVars t2
  metaVars (TypeMetaVar t)   = S.singleton t
  metaVars _ = mempty

  freeVars (TypeVar _ (TyVar tyVar)) = S.singleton tyVar
  freeVars (TypeFun _ x y) = freeVars x `S.union` freeVars y
  freeVars (TypeApp _ x y) = freeVars x `S.union` freeVars y
  freeVars _ = mempty

occursCheck :: MetaVar -> Kind -> Infer ()
occursCheck mv k = do
  when (mv `S.member` metaVars k) $
    bail (OccursCheckFailed mv k)

occursCheckType :: MetaVar -> Type Kind -> Infer ()
occursCheckType mv t =
  when (mv `S.member` metaVars t) $
    bail (OccursCheckFailedType mv t)

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
getKind mv = do
  result <- M.findWithDefault (KindMetaVar mv) mv <$> gets substitutions
  case generalize result of
    scheme ->
      pure (KindScheme scheme)

getType :: MetaVar -> Infer (Type Kind)
getType mv =
  M.findWithDefault (TypeMetaVar mv) mv <$>
    gets typeSubstitutions

substituteTyped :: Decl Kind MetaVar -> Infer (Decl Kind (Type Kind))
substituteTyped decl = do
  dbg "Substituting Type..."
  substituteDeclTyped decl

substituteVariantTyped
  :: Variant Kind MetaVar
  -> Infer (Variant Kind (Type Kind))
substituteVariantTyped (Variant k typs typ)  = do
  t <- getType typ
  pure (Variant k typs t)

substituteDeclTyped
  :: Decl Kind MetaVar
  -> Infer (Decl Kind (Type Kind))
substituteDeclTyped (Data k n args vars) = do
  vs <- traverse substituteVariantTyped vars
  pure (Data k n args vs)
substituteDeclTyped (TypeSyn kind n args body) =
  pure (TypeSyn kind n args body)
substituteDeclTyped (Class kind name args body) =
  pure (Class kind name args body)
substituteDeclTyped (Instance supers ctx) =
  pure (Instance supers ctx)
substituteDeclTyped (Newtype kind name args var) = do
  v <- substituteVariantTyped var
  pure (Newtype kind name args v)
substituteDeclTyped (KindSignature name sig) =
  pure (KindSignature name sig)
substituteDeclTyped (Foreign name typ) =
  pure (Foreign name typ)
substituteDeclTyped (TypeSig name args body) =
  pure (TypeSig name args body)
substituteDeclTyped (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)
substituteDeclTyped (Declaration typ bindings) = do
  t <- getType typ
  bs <- traverse substituteBindingType bindings
  pure (Declaration t bs)

substituteBindingType
  :: Binding Kind MetaVar -> Infer (Binding Kind (Type Kind))
substituteBindingType (Binding mv name args body) = do
  typ <- getType mv
  args' <- traverse substituteExpType args
  body' <- substituteExpType body
  pure (Binding typ name args' body')

substituteExpType :: Exp Kind MetaVar -> Infer (Exp Kind (Type Kind))
substituteExpType (Var mv name) = do
  typ <- getType mv
  pure (Var typ name)
substituteExpType (Con mv name args) = do
  typ <- getType mv
  args' <- traverse substituteExpType args
  pure (Con typ name args')
substituteExpType (Lit mv x) = do
  typ <- getType mv
  pure (Lit typ x)
substituteExpType (App mv f x) = do
  typ <- getType mv
  fun <- substituteExpType f
  arg <- substituteExpType x
  pure (App typ fun arg)
substituteExpType (Lam mv args body) = do
  typ <- getType mv
  args' <- traverse substituteExpType args
  body' <- substituteExpType body
  pure (Lam typ args' body')
substituteExpType (As mv name e) = do
  typ <- getType mv
  body <- substituteExpType e
  pure (As typ name body)
substituteExpType (Wildcard mv) = do
  typ <- getType mv
  pure (Wildcard typ)
substituteExpType (TypeAnn t e) = do
  e' <- substituteExpType e
  pure (TypeAnn t e')

substitute
  :: Decl MetaVar ()
  -> Infer (Decl Kind ())
substitute decl = do
  dbg "Substituting Kind..."
  substituteDecl decl

substituteDecl :: Decl MetaVar () -> Infer (Decl Kind ())
substituteDecl (Class mv name vars methods) = do
  substitutedKind <- getKind mv
  vs <- traverse substituteType vars
  typ' <- traverse substituteMethod methods
  pure (Class substitutedKind name vs typ')
substituteDecl (TypeSyn mv name vars typ) = do
  substitutedKind <- getKind mv
  vs <- traverse substituteType vars
  typ' <- substituteType typ
  pure (TypeSyn substitutedKind name vs typ')
substituteDecl (Data mv name vars variants) = do
  vs <- traverse substituteType vars
  substitutedKind <- getKind mv
  substitutedVariants <- mapM substituteVariant variants
  pure (Data substitutedKind name vs substitutedVariants)
substituteDecl (Newtype mv name vars variant) = do
  vs <- traverse substituteType vars
  substitutedKind <- getKind mv
  substitutedVariant <- substituteVariant variant
  pure (Newtype substitutedKind name vs substitutedVariant)
substituteDecl (KindSignature name kind) =
  pure (KindSignature name kind)
substituteDecl (Instance supers context) = do
  supers_ <- traverse substitutePred supers
  ctx_ <- substitutePred context
  pure (Instance supers_ ctx_)
substituteDecl (TypeSig name ctx typ) = do
  ctx_ <- traverse substitutePred ctx
  t <- substituteType typ
  pure (TypeSig name ctx_ t)
substituteDecl (Foreign name typ) = do
  t <- substituteType typ
  pure (Foreign name t)
substituteDecl (Declaration typ bindings) = do
  b <- traverse substituteBinding bindings
  pure (Declaration typ b)
substituteDecl (Fixity fixity precedence names) = do
  pure (Fixity fixity precedence names)

substituteBinding :: Binding MetaVar () -> Infer (Binding Kind ())
substituteBinding (Binding t name pats ex) = do
  ps <- traverse substituteExp pats
  e <- substituteExp ex
  pure (Binding t name ps e)

substituteExp :: Exp MetaVar () -> Infer (Exp Kind ())
substituteExp (Var () n) =
  pure (Var () n)
substituteExp (Lit () n) =
  pure (Lit () n)
substituteExp (App typ e1 e2) = do
  e1' <- substituteExp e1
  e2' <- substituteExp e2
  pure (App typ e1' e2')
substituteExp (Lam () args e) = do
  args' <- traverse substituteExp args
  ex <- substituteExp e
  pure (Lam () args' ex)
substituteExp (As () n e) = do
  ex <- substituteExp e
  pure (As () n ex)
substituteExp (Con () n args) = do
  args' <- traverse substituteExp args
  pure (Con () n args')
substituteExp (Wildcard ()) = do
  pure (Wildcard ())
substituteExp (TypeAnn t e) = do
  t' <- substituteType t
  ex <- substituteExp e
  pure (TypeAnn t' ex)

substitutePred
  :: Pred MetaVar
  -> Infer (Pred Kind)
substitutePred (Pred n typ) = do
  t <- substituteType typ
  pure (Pred n t)

substituteVariant
  :: Variant MetaVar ()
  -> Infer (Variant Kind ())
substituteVariant (Variant name types t) = do
  substituted <- traverse substituteType types
  pure (Variant name substituted t)

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
  , ("Num", Scheme [] (Type --> Constraint))
  , ("Eq", Scheme [] (Type --> Constraint))
  , ("IO", Scheme [] (Type --> Type))
  , ("()", Scheme [] Type)
  , ("(->)", Scheme [] (Type --> Type --> Type))
  , ("StateT", Scheme [] (Type --> (Type --> Type) --> Type --> Type))
  , ("Identity", Scheme [] (Type --> Type))
  , ("[]", Scheme [] (Type --> Type))
  ]

runInfer :: Infer a -> IO (Either Error a)
runInfer m = evalStateT (runExceptT m) emptyState

dbg :: MonadIO m => String -> m ()
dbg s = when shouldDebug $ liftIO (putStrLn s)

shouldDebug :: Bool
shouldDebug = True

classT :: IO ()
classT = testInferType
  [ Declaration () [ Binding () "ten" [] $ Lit () (LitInt 10) ]
  ]

-- | Constructor patterns
-- TODO: fix me, type schemes aren't getting generalized properly
-- -- Unification type failed
-- -- Type: String
-- -- Type: (a :: *)
isJustWildTypeAnn :: IO ()
isJustWildTypeAnn = testInferType
  [ maybeDT
  , Declaration ()
      [ Binding () "isJust"
          [ Con () "Nothing" []
          ] $ Lit () (LitBool False)
      , Binding () "isJust"
          [ Con () "Just" [ TypeAnn tString (Wildcard ()) ]
          ] $ Lit () (LitBool True)
      ]
  ]

constDecStr :: IO ()
constDecStr = testInferType
  [ Declaration ()
      [ Binding () "const"
          [ Var () "x"
          , TypeAnn tString (Wildcard ())
          ]
          (Var () "x")
      ]
  ]

tString :: Type Kind
tString = TypeCon Type (TyCon "String")

tt :: IO ()
tt = testInferType
  [ dec constFunc
  , dec idFunc
  , dec addOne
  , dec constChar
  , dec idStr
  , dec someDouble
  , dec lamConst
  , dec dollar
  , dec lamInt
  , dec asEx
  ]
  where
    idFunc     = b "id" [ v "x" ] (v "x")
    constFunc  = b "const" [ v "a", v "b" ] (v "a")
    addOne     = b "addOne" [ v "x" ] (v "(+)" `appE` v "x" `appE` lint 1)
    constChar  = b "constChar" [ ] (v "const" `appE` char 'a')
    idStr      = b "idStr" [ ] (v "id" `appE` str "lol")
    someDouble = b "double" [ ] (double 3.14)
    lamConst   = b "lamConst" [ ] (lam [ v "x" ] (lam [ v "y" ] (v "x")))
    dollar     = b "($)" [ v "f", v "x" ] (v "f" `appE` v "x")
    lamInt     = b "lamInt" [] (lam [ v "x" ] (v "x") `appE` lint 100)
    asEx       = b "asExp" [as "foo" (lint 1)] (v "foo")

    appE   = App ()
    b      = Binding ()
    dec    = Declaration () . pure
    v      = Var ()
    lint   = Lit () . LitInt
    char   = Lit () . LitChar
    str    = Lit () . LitString
    double = Lit () . LitDouble
    lam    = Lam ()
    as     = As ()

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
          Declaration typ bindings -> do
            let
              scheme = generalizeType typ
              name = getName decl
            dbg $ name <> " :: " <> showTypeScheme scheme
            forM_ bindings $ \b ->
              putStrLn (showBinding b)
            putStrLn ""
          _ -> pure ()

-- TODO: instead of this, return [TypeScheme] from `inferType`
-- so you can add all the variants to the typeEnv
addConstructors
  :: [Decl Kind () ]
  -> Infer ()
addConstructors decls = mapM_ go decls
  where
    go (Data kind name args variants) = do
      let tcon = mkTypeCon kind name args
      forM_ variants $ \(Variant varName varArgs _) -> do
        let t = foldr (-->) tcon varArgs
        addToTypeEnv varName (generalizeType t)
    go (Newtype kind name args (Variant varName varArgs _)) = do
      let tcon = mkTypeCon kind name args
          t = foldr (-->) tcon varArgs
      dbg $ "Adding constructor: " <> varName <> " :: " <> showType t
      addToTypeEnv name (generalizeType t)
    go _ = pure ()

inferTypes
  :: [Decl Kind ()]
  -> IO (Either Error [Decl Kind (Type Kind)])
inferTypes decls = runInfer $ do
  addTypeSigs decls
  addBindings decls
  addConstructors decls
  forM decls $ \d -> do
    dbg ("Inferring type for decl: " <> showDecl d)
    (maybeScheme, decl) <- inferType d
    mapM_ (addToTypeEnv decl) maybeScheme
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
  let sigs = [ (name, generalize k) | KindSignature name k <- decls ]
  mapM_ (uncurry addToKindEnv) sigs

addTypeSigs :: [Decl Kind ()] -> Infer ()
addTypeSigs decls = do
  let sigs = [ (name, generalizeType typ)
             | TypeSig name _ typ <- decls
             ]
  mapM_ (uncurry addToTypeEnv) sigs

addBindings :: [Decl Kind ()] -> Infer ()
addBindings decls =
  forM_ decls $ \decl ->
    case decl of
      Declaration _ (Binding () name _ _ : _) ->
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
  pure (generalize (annKind d), d)

populateEnv :: GetName name => [name] -> Infer [MetaVar]
populateEnv = mapM (addToEnv . getName)

inferType :: Decl Kind () -> Infer (Maybe TypeScheme, Decl Kind (Type Kind))
inferType decl = do
  elaborated <- elaborateDeclTyped decl
  solve
  d <- substituteTyped elaborated
  pure (generalizeDeclType d, d)

data TypeScheme = TypeScheme [Name] (Type Kind)
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
elaborateVariantType
  :: Type Kind
  -> Variant Kind ()
  -> Infer (Variant Kind MetaVar)
elaborateVariantType t (Variant name typs ()) = do
  mv <- fresh
  constrainTypes
    (TypeMetaVar mv)
    (foldr (-->) t typs)
  pure (Variant name typs mv)

mkTypeCon :: Kind -> Name -> [Type Kind] -> Type Kind
mkTypeCon k n = foldl (TypeApp Type) (TypeCon k (TyCon n))

elaborateDeclTyped :: Decl Kind () -> Infer (Decl Kind MetaVar)
elaborateDeclTyped (Declaration () bindings) = do
  mv <- fresh
  bs <- traverse elaborateBindingType bindings
  forM_ bs $ \b ->
    constrainType mv (TypeMetaVar (ann b))
  pure (Declaration mv bs)
elaborateDeclTyped (Data kind name args vars) = do
  let con = mkTypeCon kind name args
  vs <- traverse (elaborateVariantType con) vars
  pure (Data kind name args vs)
elaborateDeclTyped (TypeSyn kind n args body) =
  pure (TypeSyn kind n args body)
elaborateDeclTyped (Class kind name args body) =
  pure (Class kind name args body)
elaborateDeclTyped (Instance supers ctx) =
  pure (Instance supers ctx)
elaborateDeclTyped (Newtype kind name args var) = do
  let con = mkTypeCon kind name args
  v <- elaborateVariantType con var
  pure (Newtype kind name args v)
elaborateDeclTyped (KindSignature name sig) =
  pure (KindSignature name sig)
elaborateDeclTyped (Foreign name typ) =
  pure (Foreign name typ)
elaborateDeclTyped (TypeSig name args body) =
  pure (TypeSig name args body)
elaborateDeclTyped (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)

elaborateBindingType :: Binding Kind () -> Infer (Binding Kind MetaVar)
elaborateBindingType (Binding () name args body) = do
  -- TODO: check for naming conflicts here? or do it in the renamer pass
  -- e.g. foo x@(Just x) = undefined
  mv <- lookupNamedType name
  let fvs = S.unions (freeVars <$> args)
  _ <- fmap TypeMetaVar <$> populateEnv (S.toList fvs)
  args' <- traverse elaborateExpType args
  body' <- elaborateExpType body
  constrainType mv $
    foldr tFun (TypeMetaVar (ann body'))
    (TypeMetaVar . ann <$> args')
  pure (Binding mv name args' body')

elaborateExp
  :: Exp () ()
  -> Infer (Exp MetaVar ())
elaborateExp (Var () n) = do
  pure (Var () n)
elaborateExp (Lit () n) = do
  pure (Lit () n)
elaborateExp (App () e1 e2) = do
  e1' <- elaborateExp e1
  e2' <- elaborateExp e2
  pure (App () e1' e2')
elaborateExp (Lam () args e) = do
  as <- traverse elaborateExp args
  e' <- elaborateExp e
  pure (Lam () as e')
elaborateExp (As () n e) = do
  e' <- elaborateExp e
  pure (As () n e')
elaborateExp (Con () n args) = do
  as <- traverse elaborateExp args
  pure (Con () n as)
elaborateExp (Wildcard ()) = do
  pure (Wildcard ())
elaborateExp (TypeAnn t e) = do
  t' <- elaborateType t
  e' <- elaborateExp e
  pure (TypeAnn t' e')

tFun :: Type Kind -> Type Kind -> Type Kind
tFun = TypeFun Type

elaborateExpType :: Exp Kind () -> Infer (Exp Kind MetaVar)
elaborateExpType (Var () name) = do
  mv <- lookupNamedType name
  pure (Var mv name)
elaborateExpType (Lit () lit) = do
  mv <- elaborateLit lit
  pure (Lit mv lit)
elaborateExpType (Wildcard ()) = do
  mv <- fresh
  pure (Wildcard mv)
elaborateExpType (App () f x) = do
  fun <- elaborateExpType f
  arg <- elaborateExpType x
  mv <- fresh
  constrainType (ann fun)
    (TypeMetaVar (ann arg) --> TypeMetaVar mv)
  pure (App mv fun arg)
elaborateExpType (Lam () args body) = do
  void $ populateEnv $ S.toList (freeVars args)
  args' <- traverse elaborateExpType args
  body' <- elaborateExpType body
  mv <- fresh
  constrainType mv $
    foldr (-->)
      (TypeMetaVar (ann body'))
      (fmap (TypeMetaVar . ann) args')
  pure (Lam mv args' body')
elaborateExpType (As () name pat) = do
  mv <- lookupNamedType name
  pat' <- elaborateExpType pat
  constrainType mv (TypeMetaVar (ann pat'))
  pure (As mv name pat')
elaborateExpType (Con () name args) = do
  _ <- populateEnv $ S.toList (freeVars args)
  mv <- fresh
  con <- lookupNamedType name
  args' <- traverse elaborateExpType args
  constrainType con
    (foldr tFun
       (TypeMetaVar mv)
       (TypeMetaVar . ann <$> args'))
  pure (Con mv name args')
elaborateExpType (TypeAnn t e) = do
  e' <- elaborateExpType e
  constrainTypes t (TypeMetaVar (ann e'))
  pure (TypeAnn t e')

elaborateLit :: Lit -> Infer MetaVar
elaborateLit LitInt{} = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "Int"))
  pure mv
elaborateLit LitChar{} = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "Char"))
  pure mv
elaborateLit LitString{} = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "String"))
  pure mv
elaborateLit LitDouble{} = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "Double"))
  pure mv
elaborateLit LitBool{} = do
  mv <- fresh
  constrainType mv (TypeCon Type (TyCon "Bool"))
  pure mv

elaborateDecl :: Decl () () -> Infer (Decl MetaVar ())
elaborateDecl decl = do
  dbg "Elaborating..."
  elaborate decl

handleKindSignature
  :: Name
  -> MetaVar
  -> Infer ()
handleKindSignature name mv = do
  result <- lookupKindEnv name
  forM_ result (constrain mv . KindMetaVar)

elaborate :: Decl () () -> Infer (Decl MetaVar ())
elaborate (TypeSyn () name vars typ) = do
  mv <- addToEnv name
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv vars
  vs <- traverse elaborateType vars
  t <- elaborateType typ
  constrain mv (foldr KindFun (KindMetaVar (ann t)) mvs)
  pure (TypeSyn mv name vs t)
elaborate (Data () name vars variants) = do
  mv <- addToEnv name
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv (getName <$> vars)
  vars' <- traverse elaborateType vars
  vs <- traverse elaborateVariant variants
  constrain mv (foldr KindFun Type mvs)
  pure (Data mv name vars' vs)
elaborate (Newtype () name vars variant) = do
  mv <- addToEnv name
  handleKindSignature name mv
  mvs <- fmap KindMetaVar <$> populateEnv (getName <$> vars)
  vars' <- traverse elaborateType vars
  v <- elaborateVariant variant
  constrain mv (foldr KindFun Type mvs)
  pure (Newtype mv name vars' v)
elaborate (Class () name vars methods) = do
  mv <- addToEnv name
  handleKindSignature name mv
  void $ populateEnv (getFreeVars vars methods)
  vs <- traverse elaborateType vars
  methods_ <- traverse elaborateMethod methods
  mvs <- fmap KindMetaVar <$> traverse lookupName vars
  constrain mv (foldr KindFun Constraint mvs)
  pure (Class mv name vs methods_)
elaborate (KindSignature name kind) = do
  mv <- addToEnv name
  constrain mv kind
  pure (KindSignature name kind)
elaborate (Instance supers ctx) = do
  checkInstanceHead supers ctx
  addContextToEnv supers
  supers_ <- traverse elaboratePred supers
  ctx_ <- elaboratePred ctx
  pure (Instance supers_ ctx_)
elaborate (TypeSig name ctx typ) = do
  mv <- addToEnv name
  addContextToEnv ctx
  ctx_ <- traverse elaboratePred ctx
  t <- elaborateType typ
  constrain (ann t) Type
  constrain mv (KindMetaVar (ann t))
  pure (TypeSig name ctx_ t)
elaborate (Foreign name typ) = do
  t <- elaborateType typ
  constrain (ann t) Type
  pure (Foreign name t)
elaborate (Declaration () bindings) = do
  bs <- traverse elaborateBinding bindings
  pure (Declaration () bs)
elaborate (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)

elaborateBinding
  :: Binding () ()
  -> Infer (Binding MetaVar ())
elaborateBinding (Binding () name pats e) = do
  ps <- traverse elaborateExp pats
  ex <- elaborateExp e
  pure (Binding () name ps ex)

checkInstanceHead :: [Pred ()] -> Pred () -> Infer ()
checkInstanceHead supers ctx =
  forM_ supers $ \superPred ->
    forM_ (freeVars ctx `S.difference` freeVars superPred) $ \x ->
      bail (Doesn'tOccurInInstanceHead x superPred ctx)

addContextToEnv :: [Pred ()] -> Infer ()
addContextToEnv ctx = do
  let fvs = S.unions [ freeVars typ | Pred _ typ <- ctx ]
  void (populateEnv (S.toList fvs))

elaboratePred :: Pred () -> Infer (Pred MetaVar)
elaboratePred (Pred name typ) = do
  class_ <- lookupName name
  type_ <- elaborateType typ
  constrain class_ (KindMetaVar (ann type_) --> Constraint)
  pure (Pred name type_)

getFreeVars :: GetName name => [name] -> [Method a] -> [Name]
getFreeVars vars methods = S.toList fvs
  where
    fvs =
      S.unions
      [ S.unions [ freeVars t | Method _ t <- methods ]
      , S.fromList (getName <$> vars)
      ]

elaborateMethod :: Method () -> Infer (Method MetaVar)
elaborateMethod (Method name typ) = do
  t <- elaborateType typ
  pure (Method name t)

elaborateVariant :: Variant () () -> Infer (Variant MetaVar ())
elaborateVariant (Variant name types typ) = do
  ts <- traverse elaborateType types
  forM_ ts (\t -> constrain (ann t) Type)
  pure (Variant name ts typ)

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
  result <- lookupKindEnv name
  case result of
    Just mv -> pure mv
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> bail (UnboundName name)
        Just v -> pure v

lookupNamedType :: GetName name => name -> Infer MetaVar
lookupNamedType named = do
  let name = getName named
  typEnv <- gets typeEnv
  case M.lookup name typEnv of
    Just scheme -> do
      mv <- fresh
      typ <- instantiateType name scheme
      constrainType mv typ
      pure mv
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> bail (UnboundName name)
        Just v -> pure v

instantiate :: Name -> Scheme -> Infer Kind
instantiate name (Scheme vars kind) = do
  dbg $ "Instantiating Type: " <> name <> " :: " <> showKind kind
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (cataKind (replaceKind mapping) kind)
    where
      replaceKind :: Map Name MetaVar -> Kind -> Kind
      replaceKind mapping (KindVar (MkKindVar v)) =
         case M.lookup v mapping of
           Nothing -> KindVar (MkKindVar v)
           Just mv -> KindMetaVar mv
      replaceKind _ k = k

instantiateType :: Name -> TypeScheme -> Infer (Type Kind)
instantiateType name (TypeScheme vars typ) = do
  dbg $ "Instantiating Type: " <> name <> " :: " <> showType typ
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  pure (cataType (replaceType mapping) typ)
    where
      replaceType mapping (TypeVar kind (TyVar v)) =
         case M.lookup v mapping of
           Nothing -> TypeVar kind (TyVar v)
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
cataKind f (KindScheme (Scheme xs k)) =
  f (KindScheme (Scheme xs (cataKind f k)))

class Ann a where
  ann :: a ann -> ann

instance Ann (Exp typ) where
  ann (Var x _)     = x
  ann (Lit x _)     = x
  ann (App x _ _)   = x
  ann (Lam x _ _)   = x
  ann (As x _ _)    = x
  ann (Con x _ _)   = x
  ann (Wildcard x)  = x
  ann (TypeAnn _ x) = ann x

instance Ann Type where
  ann (TypeVar x _)   = x
  ann (TypeCon x _)   = x
  ann (TypeApp x _ _) = x
  ann (TypeFun x _ _) = x
  ann (TypeMetaVar _) = error "Called 'ann' on a MetaVar"

instance Ann (Binding typ) where
  ann (Binding t _ _ _) = t

annKind :: Decl Kind typ -> Kind
annKind (Data x _ _ _)          = x
annKind (TypeSyn x _ _ _)       = x
annKind (Class x _ _ _)         = x
annKind (Newtype x _ _ _)       = x
annKind (KindSignature _ k)     = k
annKind (TypeSig _ _ _)   = Type
annKind (Instance _ _)          = Constraint
annKind (Foreign _ _)           = Type
annKind (Declaration _ _)       = Type
annKind (Fixity _ _ _)          = error "no kind for fixity declaration"

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

generalizeDeclType :: Decl Kind (Type Kind) -> Maybe TypeScheme
generalizeDeclType (Declaration t _) = Just (generalizeType t)
generalizeDeclType _ = Nothing

generalizeBinding :: Binding Kind (Type Kind) -> TypeScheme
generalizeBinding = generalizeType . ann

generalizeType :: Type Kind -> TypeScheme
generalizeType typ = TypeScheme vars (cataType quantify typ)
  where
    metavars = S.toList (metaVars typ)
    mapping  = zip (sort metavars) [0..]
    subs     = M.fromList mapping
    vars     = sort [ showT v | v <- snd <$> mapping ]

    quantify (TypeMetaVar m) = TypeVar Type (TyVar (showT (subs M.! m)))
    quantify k               = k

    showT :: Int -> String
    showT k = combos !! k

    combos =
      concat
      [ pure <$> ['a'..'z']
      , (\k v -> k : show v) <$> ['a' .. 'z'] <*> [ 1 .. 99 :: Int ]
      ]

generalize :: Kind -> Scheme
generalize kind = Scheme vars (cataKind quantify kind)
  where
    metavars = S.toList (metaVars kind)
    mapping = zip (sort metavars) [ 0 :: Int .. ]
    subs = M.fromList mapping
    vars = sort [ showKind_ v | v <- snd <$> mapping ]

    quantify (KindMetaVar m) = KindVar (MkKindVar (showKind_ (subs M.! m)))
    quantify k               = k

    showKind_ 0 = "k"
    showKind_ n = "k" <> show n

kk :: String
kk = showDecl @() @() $ Fixity Infixr (Just 1) [ "---->" ]

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
        x <- runInfer (inferType decl)
        case x of
          Left e -> print e
          Right (ms, inferred) -> do
            forM_ ms (putStrLn . showTypeScheme)
            putStrLn (showDecl inferred)

main :: IO ()
main = testInfer
  [ tree
  , lol
  , maybeD
  , person
  , statet
  , state
  , thisthat
  , proxy
  , cofree
  , functor
  , typeSig
  ]

int :: Decl () ()
int = Data () "Int" [] [ Variant "Int" [] () ]

lol :: Decl () ()
lol = Data () "LOL" [ tVar "a", tVar "b" ]
  [ Variant "LOL"
    [ app (app (tCon "Either") (tVar "a")) (tVar "b") ]
    ()
  ]

maybeD :: Decl () ()
maybeD = Data () "Maybe" [ tVar "a" ]
  [ Variant "Just" [ tVar "a" ] ()
  , Variant "Nothing" [] ()
  ]

maybeDT :: Decl Kind ()
maybeDT = Data (Type --> Type) "Maybe" [ TypeVar Type (TyVar "a") ]
  [ Variant "Just" [ TypeVar Type (TyVar "a") ] ()
  , Variant "Nothing" [] ()
  ]

person :: Decl () ()
person = Data () "Person" []
  [ Variant "Person" [ tCon "String", tCon "Int" ] ()
  ]

statet :: Decl () ()
statet = TypeSyn () "Foo" [] (tCon "StateT")

proxy :: Decl () ()
proxy = Newtype () "Proxy" [ tVar "k" ] (Variant "Proxy" [] ())

tree :: Decl () ()
tree = Data () "Tree" [ tVar "a" ]
  [ Variant "Node" [ tVar "a", app (tCon "Tree") (tVar "a")
                   , app (tCon "Tree") (tVar "a")
                   ] ()
  ]

treefail :: Decl () ()
treefail = Data () "Tree" [ tVar "a" ]
  [ Variant "Node" [ tVar "a", tCon "Tree", tCon "Tree" ] ()
  ]

state :: Decl () ()
state = TypeSyn () "State" [ tVar "s", tVar "a" ]
  (tCon "StateT" `app` tVar "s" `app` tCon "Identity" `app` tVar "a")

thisthat :: Decl () ()
thisthat = Data () "ThisThat" [ tVar "l", tVar "r" ]
  [ Variant "This" [ tVar "l" ] ()
  , Variant "That" [ tVar "r" ] ()
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
fmapSyn = TypeSyn () "Fmap" [tVar "f", tVar "a", tVar "b" ] fmap_

-- type Fmap f a b = (a -> b) -> f a -> f b
-- Fmap :: (* -> *) -> * -> * -> *

data Cofree f a = Cofree a (f (Cofree f a))

cofree :: Decl () ()
cofree = Data () "Cofree" [ tVar "f", tVar "a" ]
  [ Variant "Cofree"
    [ tVar "a"
    , tVar "f" `app` (tCon "Cofree" `app` tVar "f" `app` tVar "a")
    ] ()
  ]

recfail :: Decl () ()
recfail = Data () "Rec" [ tVar "f", tVar "a" ]
  [ Variant "Rec"
    [ tVar "f"
    , app (tVar "f") (tVar "a")
    ] ()
  ]

-- tests that inference fails if a kind signature doesn't match
okFailTest :: IO ()
okFailTest
  = testInfer
  [ KindSignature "OK" (Type --> Type)
  , TypeSyn () "OK" [] (tCon "Int")
  ]

okTest :: IO ()
okTest
  = testInfer
  [ KindSignature "OK" Type
  , TypeSyn () "OK" [] (tCon "Int")
  ]

instTestFunctorMaybe :: IO ()
instTestFunctorMaybe
  = testInfer
  [ functor
  , Instance
      []
      (Pred "Functor" (tCon "Maybe"))
  ]

oops :: IO ()
oops
  = testInfer
  [ functor
  , Instance
      [ Pred "Eq" (tVar "b") ]
      (Pred "Functor" (tCon "Maybe"))
  ]

instTestNumEither :: IO ()
instTestNumEither
  = testInfer
  [ functor
  , Instance
      [ Pred "Num" (tVar "a") ]
      (Pred "Functor" (tCon "Either" `app` tCon "a"))
  ]

data List a = Nil | List a (List a)

instTestFail :: IO ()
instTestFail
  = testInfer
  [ functor
  , Instance [] (Pred "Functor" (tCon "Int"))
  ]

functor :: Decl () ()
functor = Class () "Functor" [ tVar "f" ] [Method "fmap" fmap_]

foreignTest :: IO ()
foreignTest
  = testInfer
  [ Foreign "sin" (tCon "IO" `app` tCon "()")
  ]

typeSigTest :: IO ()
typeSigTest = testInfer [ typeSig ]

typeSig :: Decl () typ
typeSig =
  TypeSig
    "f"
    [ Pred "Monad" (tVar "m")
    , Pred "Eq" (tVar "m" `app` tVar "a")
    ]
    (tVar "a" --> (tVar "m" `app` tVar "a") --> tCon "Bool")
