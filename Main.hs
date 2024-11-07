{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State  hiding (state)
import           Data.Function
import           Data.List
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Maybe
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
  = Data kind Name [Type kind] [ConDecl kind typ]
  | TypeSyn kind Name [Type kind] (Type kind)
  | Class kind [Pred kind] (Pred kind) [Decl kind typ]
  | Instance [Pred kind] (Pred kind) [Decl kind typ]
  | Newtype kind Name [Type kind] (ConDecl kind typ)
  | KindSig Name Kind
  | Foreign Name (Type kind)
  | TypeSig Name [Pred kind] (Type kind)
  | Fixity Fixity (Maybe Int) [Name]
  | Decl typ [Binding kind typ]
  deriving (Show, Eq)

data Instance
  = Inst
  { instanceConstraints :: [Pred (Type Kind)]
  , instanceHead :: Pred (Type Kind)
  } deriving (Eq, Show)

data Fixity
  = Infix
  | Infixl
  | Infixr
  deriving (Show, Eq)

data Binding kind typ
  = Binding typ Name [Pat kind typ] (Exp kind typ)
  deriving (Show, Eq)

class Fun a where
  infixr 4 -->
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
  | PrimOp typ Name
  | App typ (Exp kind typ) (Exp kind typ)
  | Lam typ [Exp kind typ] (Exp kind typ)
  | InfixOp typ (Exp kind typ) Name (Exp kind typ)
  -- Patterns
  | As typ Name (Pat kind typ)
  | Con typ Name [Pat kind typ]
  | Wildcard typ
  | Fail typ -- Pattern-match fail constructor
  -- Control
  | Let typ [Decl kind typ] (Exp kind typ)
  | IfThenElse typ (Exp kind typ) (Exp kind typ) (Exp kind typ)
  | Case typ (Exp kind typ) [Alt kind typ]
  | Do typ [Stmt kind typ]
  -- Others
  | TypeAnn (Type kind) (Exp kind typ)
  | LeftSection typ (Exp kind typ) Name
  | RightSection typ Name (Exp kind typ)
  | Tuple typ [Exp kind typ]
  | List typ [Exp kind typ]
  | ListComp typ (Exp kind typ) [Stmt kind typ]
  | Sequence typ (Exp kind typ) (Maybe (Exp kind typ)) (Maybe (Exp kind typ))
  | PrefixNegation typ (Exp kind typ)
  | LabeledUpdate typ (Exp kind typ) [(Name, Exp kind typ)]
  | Irrefutable typ (Exp kind typ)
  deriving (Show, Eq)

data Stmt kind typ
  = SBind (Pat kind typ) (Exp kind typ)
  | SExp (Exp kind typ)
  | SLet [Decl kind typ]
  deriving (Show, Eq)

data Alt kind typ
  = Alt (Pat kind typ) (Exp kind typ) [Decl kind typ]
  | AltGd (Pat kind typ) [Guards kind typ] [Decl kind typ]
  deriving (Show, Eq)

data Guards kind typ
  = Guards [Stmt kind typ] (Exp kind typ)
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

class GetName f where
  getName :: f -> Name

instance GetName Name where
  getName = id

instance GetName (Decl a typ) where
  getName (Data _ name _ _)    = name
  getName (TypeSyn _ name _ _) = name
  getName (Class _ _ name _)   = getName name
  getName (Newtype _ name _ _) = name
  getName (KindSig name _)     = name
  getName (Instance _ p _)     = getName p
  getName (Foreign name _)     = name
  getName (TypeSig name _ _)   = name
  getName (Fixity _ _ names)   = intercalate "," names
  getName (Decl _ [])          = error "no bindings"
  getName (Decl _ (b:_))       = getName b

instance GetName (Binding kind a) where
  getName (Binding _ name _ _) = name

instance GetName (Pred a) where
  getName (Pred name _) = name

instance GetName (Type a) where
  getName (TypeVar _ name) = getName name
  getName (TypeCon _ name) = getName name
  getName (TypeMetaVar _ mv) = getName mv
  getName _ = "<no name>"

instance GetName MetaVar where
  getName = showMetaVar

instance GetName TyVar where
  getName (TyVar n) = n

instance GetName TyCon where
  getName (TyCon n) = n

data ConDecl kind typ
  = ConDecl Name [Type kind] typ
  | ConDeclRec Name [(Name, Type kind)] typ
  deriving (Show, Eq)

data Type k
  = TypeVar k TyVar
  | TypeCon k TyCon
  | TypeFun k (Type k) (Type k)
  | TypeApp k (Type k) (Type k)
  | TypeMetaVar Kind MetaVar
  deriving (Eq, Ord)

instance (ShowAnn k) => Show (Type k) where
  show = showType

newtype KindVar = MkKindVar { unKindVar :: Name }
  deriving (Show, Eq, Ord)

-- | A representation of a kind.
data Kind
  = Type
  | KindFun Kind Kind
  | KindVar KindVar
  | KindMetaVar MetaVar
  | Constraint
  deriving (Eq, Ord)

instance Show Kind where
  show = showKind

class HasKind t where
  hasKind :: t -> Kind

instance HasKind Kind where
  hasKind = id

instance HasKind (Type Kind) where
  hasKind (TypeCon k _) = k
  hasKind (TypeVar k _) = k
  hasKind (TypeApp k _ _) =
    case hasKind k of
      KindFun _ k2 -> k2
      _ -> k
  hasKind (TypeFun k _ _) =
    case hasKind k of
      KindFun _ k2 -> k2
      _ -> k
  hasKind (TypeMetaVar k _) = k

data Scheme a = Scheme [Name] a
  deriving (Eq, Ord)

instance Show a => Show (Scheme a) where
  show = showScheme

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
showType_ (TypeApp _ f x)   = showType_ f <> " " <> showTypeVar x
showType_ t                 = showTypeVar t

showTypeVar :: ShowAnn ann => Type ann -> String
showTypeVar (TypeVar k (TyVar v))
  | null (showAnn k) = v
  | otherwise = parens (v <> " :: " <> showAnn k)
showTypeVar (TypeCon _ (TyCon c)) = c
showTypeVar (TypeMetaVar _ (MetaVar v)) = "{" <> show v <> "}"
showTypeVar x                       = parens (showType_ x)

parens :: String -> String
parens x = "(" <> x <> ")"

brackets :: String -> String
brackets x = "[" <> x <> "]"

braces :: String -> String
braces x = "{" <> x <> "}"

showScheme :: Show a => Scheme a -> String
showScheme (Scheme [] k) = show k
showScheme (Scheme vars k) =
  intercalate " "
    [ "forall"
    , intercalate " " vars
    , "."
    , show k
    ]

data Constraint a
  = Equality a a
  | ClassConstraint (Pred Kind)
  deriving (Eq, Ord)

instance Show a => Show (Constraint a) where
  show (Equality t1 t2) =
    intercalate "\n"
    [ show t1 <> " = " <> show t2
    ]
  show (ClassConstraint p) =
    intercalate "\n"
    [ showPred p
    ]

data InferState a
  = InferState
  { env               :: Map Name MetaVar
  , schemeEnv         :: Map Name (Scheme a)
  , classes           :: Map ClassName [SuperClass]
  , instances         :: Map ClassName [Instance]
  , substitutions     :: Map MetaVar a
  , var               :: Int
  , constraints       :: [Constraint a]
  } deriving (Show, Eq)

type ClassName = String
type SuperClass = String

type Subst a = Map MetaVar a
type Infer a = ExceptT (Error a) (StateT  (InferState a) IO)

data Error a
  = UnboundName Name
  | UnificationFailed a a
  | OccursCheckFailed MetaVar a
  | Doesn'tOccurInInstanceHead Name (Pred ()) (Pred ())
  | CouldntFindSubstitution Name MetaVar
  | LastDoStmtMustBeExp

fresh :: Infer a MetaVar
fresh = do
  modify $ \s -> s { var = var s + 1 }
  MetaVar <$> gets var

instance (Show a, Generalize a) => Show (Error a) where
  show (UnificationFailed k1 k2) =
    intercalate "\n"
    [ "Unification type failed"
    , "Type: " <> show (generalize k1)
    , "Type: " <> show (generalize k2)
    ]
  show (UnboundName tyvar) =
    "Unbound Name: " <> show tyvar
  show (OccursCheckFailed mv k) =
    intercalate "\n"
    [ "Occurs check failed"
    , "MetaVar: " <> showMetaVar mv
    , "Type: " <> show k
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
  show (CouldntFindSubstitution name mv) =
    intercalate "\n"
    [ "Couldn't find " <> name <> " in substitution " <> show mv
    ]
  show LastDoStmtMustBeExp =
    intercalate "\n"
    [ "The last statement in a 'do block' must be an expression"
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
        [ "\n  = " <> showConDecl y
        , concat
          [ "\n  | " <> v
          | v <- fmap showConDecl ys
          ]
        ]
  ]
showDecl (Class a supers p decls) =
  intercalate " "
  [ "class" <>
      if null supers
      then ""
      else beforeAll " "
        [ parens (intercalate "," (showPred <$> supers))
        , "=>"
        ]
  , if null (showAnn a)
    then showPred p
    else parens (showPred p <> " :: " <> showAnn a)
  , "where"
  , beforeAll "\n  " (showDecl <$> decls)
  ]
showDecl (Instance ps p decl) =
  intercalate " "
  [ "instance"
  , case ps of
      [] -> showPred p
      [x] -> showPred x <> " => " <> showPred p
      xs -> parens $ intercalate ", " (showPred <$> xs) <> " => " <> showPred p
  , "where"
  ] ++ beforeAll "\n  " (showDecl <$> decl)
showDecl (Newtype a n vars variant) =
  intercalate " "
  [ "newtype"
  , if null (showAnn a)
    then n
    else parens (n <> " :: " <> showAnn a)
  , if null vars
      then "="
      else intercalate " " (showTypeVar <$> vars) <> " ="
  , showConDecl variant
  ]
showDecl (KindSig name kind) =
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
showDecl (Decl _ bindings) =
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

showExp :: (ShowAnn typ, ShowAnn kind) => Exp kind typ -> String
showExp (App _ f x) = showExpVar f <> " " <> showExp x
showExp x = showExpVar x

showAlt
  :: (ShowAnn kin, ShowAnn typ)
  => Alt kin typ
  -> String
showAlt (Alt l r decls) =
  intercalate " "
  [ showExp l
  , "->"
  , showExp r
  , "where"
  , beforeAll "\n  " (showDecl <$> decls)
  ]
showAlt (AltGd l gds decls) =
  intercalate " "
  [ showExp l
  , beforeAll "\n  | " (showGuards <$> gds)
  , if not (null decls)
      then
        intercalate " "
          [ "where"
          , beforeAll "\n  " (showDecl <$> decls)
          ]
    else ""
  ]

showGuards
  :: (ShowAnn kind, ShowAnn typ)
  => Guards kind typ
  -> String
showGuards (Guards stmts e) =
  intercalate " "
  [ intercalate "," (showStmt <$> stmts)
  , "->"
  , showExp e
  ]

showStmt :: (ShowAnn kind, ShowAnn typ) => Stmt kind typ -> String
showStmt (SBind p e) =
  intercalate " "
  [ showExp p
  , "<-"
  , showExp e
  ]
showStmt (SExp e) =
  showExp e
showStmt (SLet decls) =
  intercalate " "
  [ "let"
  , beforeAll "\n    " (showDecl <$> decls)
  ]

showExpVar :: (ShowAnn kind, ShowAnn typ) => Exp kind typ -> String
showExpVar (Do _ stmts) =
  intercalate " "
    [ "do"
    , beforeAll "\n  "
      [ showStmt s
      | s <- stmts
      ]
    ]
showExpVar (InfixOp _ l n r) = do
  let unparen ('(':c:")") = [c]
      unparen x = x
  showExp l <> " " <> unparen n <> " " <> showExp r
showExpVar (Irrefutable _ e) =
  "~" <> showExp e
showExpVar (ListComp _ e stmts) =
  brackets $ intercalate " "
    [ showExp e
    , "|"
    , intercalate ","
      [ showStmt s
      | s <- stmts
      ]
    ]

showExpVar (Sequence _ e step end) =
  brackets $
    showExp e <>
      case step of
        Nothing -> ".."
        Just s -> "," <> showExp s <> ".." <>
          case end of
            Nothing -> ""
            Just x -> showExp x
showExpVar (LeftSection _ e n) =
  parens (showExp e <> n)
showExpVar (RightSection _ n e) =
  parens (n <> showExp e)
showExpVar (Tuple _ exps) =
  parens (intercalate "," (showExp <$> exps))
showExpVar (List _ exps) =
  brackets (intercalate "," (showExp  <$> exps))
showExpVar (Var _ name) = name
showExpVar (Lit _ lit) = showLit lit
showExpVar (Wildcard _) = "_"
showExpVar (Fail _) = ""
showExpVar (Case _ e alts) =
  intercalate " "
  [ "case"
  , showExp e
  , "of"
  , "{"
  , beforeAll "\n " (showAlt <$> alts)
  , "\n}"
  ]
showExpVar (Let _ decls e) =
  intercalate " "
  [ "let {"
  , intercalate "; "
    [ showDecl decl
    | decl <- decls
    ]
  , "} in " <> showExp e
  ]

showExpVar (IfThenElse t c e1 e2) =
  intercalate " "
  [ "if"
  , showExp c
  , "then"
  , showExp e1
  , "else"
  , showExp e2 <>
      if not $ null (showAnn t)
      then " :: " <> showAnn t
      else ""
  ]
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
showExpVar (PrefixNegation _ e) =
  parens ("-" <> showExp e)
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
  (Pred "Show" (tVar "a")) []

showPred :: ShowAnn ann => Pred ann -> String
showPred (Pred name typ) =
  intercalate " "
  [ name
  , showType typ
  ]

showRecField :: ShowAnn ann => (Name, Type ann) -> String
showRecField (n,t) =
  intercalate " "
  [ n
  , "::"
  , showType t
  ]

showConDecl
  :: (ShowAnn typ, ShowAnn ann)
  => ConDecl ann typ
  -> String
showConDecl (ConDeclRec n fields t) =
  intercalate " "
  [ n
  , braces (intercalate "," (showRecField <$> fields))
  ] <> showAnn t
showConDecl (ConDecl n [] t) =
  concat $ n :
  [ " :: " <> showAnn t
  | not $ null (showAnn t)
  ]
showConDecl (ConDecl n ts t) =
  mconcat $
  [ intercalate " " (n : fmap showTypeVar ts)
  ] ++
  [ " :: " <> showAnn t
  | not $ null (showAnn t)
  ]

solve :: (Unify a, Apply a) => Infer a ()
solve = do
  dbg "Solving..."
  sortConstraints
  solveConstraints

sortConstraints :: Infer a ()
sortConstraints = do
  dbg "Sorting constraints..."
  cs <- gets constraints
  let isClassConstraint ClassConstraint{} = True
      isClassConstraint _ = False
  let (eqs, ccs) = span isClassConstraint cs
  setConstraints (reverse eqs <> reverse ccs)

setConstraints :: [Constraint a] -> Infer a ()
setConstraints xs = modify $ \s -> s { constraints = xs }

solveConstraints :: (Unify a, Apply a) => Infer a ()
solveConstraints = do
  constraint <- popConstraint
  case constraint of
    Nothing -> do
      dbg "Solving complete..."
    Just (Equality x1 x2) -> do
      mapM_ (uncurry apply) =<< unify x1 x2
      solveConstraints
    Just (ClassConstraint p) -> do
      classConstraint p
      solveConstraints
    where
      classConstraint p =
        dbg ("Solving class constraint for type: " <> show p)

class Apply a where
  apply :: MetaVar -> a -> Infer a ()

instance Apply (Type Kind) where
  apply k v = do
    updateSubstitutionType k v
    updateConstraintsType k v

instance Apply Kind where
  apply k v = do
    updateSubstitution k v
    updateConstraintsKind k v

updateConstraintsKind :: MetaVar -> Kind -> Infer Kind ()
updateConstraintsKind m1 k = do
  cs <- fmap replaceConstraint <$> gets constraints
  modify $ \s -> s { constraints = cs }
    where
      replaceConstraint (Equality l r) =
        Equality (cata replaceKind l) (cata replaceKind r)
          where
            replaceKind (KindMetaVar m2) | m1 == m2 = k
            replaceKind x = x
      replaceConstraint x = x

updateConstraintsType :: MetaVar -> Type Kind -> Infer (Type Kind) ()
updateConstraintsType m1 k = do
  cs <- fmap replaceConstraint <$> gets constraints
  modify $ \s -> s { constraints = cs }
    where
      replaceConstraint (Equality l r) =
        Equality (cata replaceType l) (cata replaceType r)
          where
            replaceType (TypeMetaVar _ m2) | m1 == m2 = k
            replaceType x = x
      replaceConstraint x = x

popConstraint :: Infer a (Maybe (Constraint a))
popConstraint = do
  ccs <- gets constraints
  case ccs of
    c : cs -> do
      modify $ \s -> s { constraints = cs }
      pure (Just c)
    [] ->
      pure Nothing

kindCheck :: Show a => HasKind a => a -> a -> Infer a ()
kindCheck k1 k2 =
  when (hasKind k1 /= hasKind k2) $
    bail (UnificationFailed k1 k2)

bail :: Show a => Error a -> Infer a b
bail e = do
  dump "bailing out"
  -- liftIO (print e)
  throwError e

type Sub a = (MetaVar, a)

class Cata a where
  cata :: (a -> a) -> a -> a

instance Cata (Type Kind) where
  cata = cataType

instance Cata Kind where
  cata = cataKind

class Unify a where
  unify :: a -> a -> Infer a (Maybe (Sub a))

instance Unify (Type Kind) where
  unify = unifyType

instance Unify Kind where
  unify = unifyKind

unifyType
  :: Type Kind
  -> Type Kind
  -> Infer (Type Kind) (Maybe (Sub (Type Kind)))
unifyType t1@(TypeVar _ x) t2@(TypeVar _ y)
  | x == y = do
      kindCheck t1 t2
      pure Nothing
unifyType t1@(TypeCon _ x) t2@(TypeCon _ y)
  | x == y = do
      kindCheck t1 t2
      pure Nothing
unifyType t1@(TypeMetaVar _ x) t2@(TypeMetaVar _ y)
  | x == y = do
      kindCheck t1 t2
      pure Nothing
unifyType t1@(TypeApp _ x1 y1) t2@(TypeApp _ x2 y2) = do
  kindCheck t1 t2
  constrainTypes x1 x2
  constrainTypes y1 y2
  pure Nothing
unifyType t1@(TypeFun _ x1 y1) t2@(TypeFun _ x2 y2) = do
  kindCheck t1 t2
  constrainTypes x1 x2
  constrainTypes y1 y2
  pure Nothing
unifyType (TypeMetaVar k x) y = metaVarBindType k x y
unifyType x (TypeMetaVar k y) = metaVarBindType k y x
unifyType t1 t2 =
  bail (UnificationFailed t1 t2)

unifyKind :: Kind -> Kind -> Infer Kind (Maybe (MetaVar, Kind))
unifyKind Type Type = pure Nothing
unifyKind Constraint Constraint = pure Nothing
unifyKind (KindVar x) (KindVar y) | x == y = pure Nothing
unifyKind (KindMetaVar x) (KindMetaVar y) | x == y = pure Nothing
unifyKind (KindFun x1 y1) (KindFun x2 y2) = do
  constrainKinds x1 x2
  constrainKinds y1 y2
  pure Nothing
unifyKind (KindMetaVar x) y = metaVarBind x y
unifyKind x (KindMetaVar y) = metaVarBind y x
unifyKind k1 k2 = do
  bail (UnificationFailed k1 k2)

dump :: Show a => String -> Infer a ()
dump msg = do
  dbg ""
  dbg msg
  when shouldDebug $ do
    dumpSubs
    dumpConstraints
    dumpEnv
    dumpSchemeEnv

dumpSubs :: Show a => Infer a ()
dumpSubs = do
  liftIO (putStrLn "\nDumping Substitutions...")
  subs <- gets substitutions
  liftIO $ putStrLn (showSubs subs)
    where
      showSubs :: Show a => Subst a -> String
      showSubs subst = intercalate "\n" (showSub <$> M.toList subst)

      showSub :: Show a => (MetaVar, a) -> String
      showSub (k,v) = showMetaVar k <> " : " <> show v

-- dumpTypeSubs :: Infer a ()
-- dumpTypeSubs = do
--   liftIO (putStrLn "\nDumping Type Substitutions...")
--   subs <- gets typeSubstitutions
--   liftIO $ putStrLn (showSubs subs)
--     where
--       showSubs :: Map MetaVar (Type Kind) -> String
--       showSubs subst = intercalate "\n" (showSub <$> M.toList subst)

--       showSub :: (MetaVar, (Type Kind)) -> String
--       showSub (k,v) = showMetaVar k <> " : " <> showType v

dumpConstraints :: Show a => Infer a ()
dumpConstraints = do
  cs <- gets constraints
  unless (null cs) $ do
    liftIO (putStrLn "\nDumping Constraints...")
    liftIO $ forM_ cs print

dumpEnv :: Infer a ()
dumpEnv = do
  liftIO (putStrLn "\nDumping Env...")
  e <- gets env
  liftIO $ forM_ (M.assocs e) $ \(name,mv) ->
    putStrLn $ name <> " : " <> showMetaVar mv

dumpSchemeEnv :: Show a => Infer a ()
dumpSchemeEnv = do
  liftIO (putStrLn "\nDumping Scheme Env...")
  e <- gets schemeEnv
  liftIO $ forM_ (M.assocs e) $ \(name, mv) ->
    putStrLn $ name <> " : " <> showScheme mv

metaVarBind :: MetaVar -> Kind -> Infer Kind (Maybe (MetaVar, Kind))
metaVarBind mv (KindMetaVar m) | mv == m = pure Nothing
metaVarBind m k = do
  dbg ("Binding... " ++ showMetaVar m ++ " : " ++ showKind k)
  occursCheck m k
  pure (Just (m, k))

metaVarBindType
  :: Kind
  -> MetaVar
  -> Type Kind
  -> Infer (Type Kind) (Maybe (MetaVar, Type Kind))
metaVarBindType k1 mv (TypeMetaVar k2 m)
  | hasKind k1 /= hasKind k2 =
      throwError (UnificationFailed (TypeMetaVar k1 mv) (TypeMetaVar k2 m))
  | mv == m = pure Nothing
metaVarBindType _ m k = do
  dbg ("Binding... " ++ showMetaVar m ++ " : " ++ showType k)
  occursCheck m k
  pure (Just (m, k))

updateSubstitution :: MetaVar -> Kind -> Infer Kind ()
updateSubstitution m k = modifySub (M.map replaceInState . M.insert m k)
  where
    replaceInState = cata $ \kind ->
      case kind of
        KindMetaVar mv | mv == m -> k
        z                        -> z

updateSubstitutionType :: MetaVar -> Type Kind -> Infer (Type Kind) ()
updateSubstitutionType m k = modifySub (M.map replaceInState . M.insert m k)
  where
    replaceInState = cata $ \t ->
        case t of
          TypeMetaVar _ mv | mv == m -> k
          z                          -> z

class MetaVars a where
  metaVars :: a -> Set MetaVar

instance MetaVars Kind where
  metaVars (KindMetaVar mv) = S.singleton mv
  metaVars (KindFun k1 k2)  = metaVars k1 `S.union` metaVars k2
  metaVars _ = mempty

instance MetaVars (Type Kind) where
  metaVars (TypeApp _ t1 t2) = metaVars t1 `S.union` metaVars t2
  metaVars (TypeFun _ t1 t2) = metaVars t1 `S.union` metaVars t2
  metaVars (TypeMetaVar _ t) = S.singleton t
  metaVars _ = mempty

class Substitution k where
  freeVars :: k -> Set Name

instance Substitution (Pred a) where
  freeVars (Pred _ typ) = freeVars typ

instance Substitution a => Substitution [a] where
  freeVars = S.unions . fmap freeVars

instance Substitution t => Substitution (ConDecl kind t) where
  freeVars (ConDeclRec _ fields typ) =
    freeVars (snd <$> fields) `S.union`
      freeVars typ

  freeVars (ConDecl _ typs typ) =
    freeVars typs `S.union`
      freeVars typ

instance Substitution () where
  freeVars = mempty

instance Substitution t => Substitution (Decl kind t) where
  freeVars (Data _ _ ts vs) =
    freeVars ts `S.union` freeVars vs

  freeVars (TypeSyn _ _ ts t) =
    freeVars ts `S.union` freeVars t

  freeVars (Class _ _ ts ds) =
    freeVars ts `S.union` freeVars ds

  freeVars (Instance s c ds) =
    freeVars s
      `S.union` freeVars c
      `S.union` freeVars ds

  freeVars (Newtype _ _ t v) =
    freeVars t `S.union` freeVars v

  freeVars (KindSig _ k) =
    freeVars k

  freeVars (TypeSig _ preds typ) =
    freeVars typ `S.union` freeVars preds

  freeVars (Decl _ bindings) =
    freeVars bindings

  freeVars _ = mempty

instance Substitution typ => Substitution (Binding kind typ) where
  freeVars (Binding _ _ args _) =
    freeVars args

instance Substitution a => Substitution (Stmt kind a) where
  freeVars (SBind pat _) =
    freeVars pat
  freeVars (SExp _) =
    mempty
  freeVars (SLet decls) =
    freeVars decls

instance Substitution a => Substitution (Maybe a) where
  freeVars Nothing = mempty
  freeVars (Just x) = freeVars x

instance Substitution a => Substitution (Exp kind a) where
  freeVars (PrimOp _ n) = S.singleton n
  freeVars (InfixOp _ l _ r) = freeVars l <> freeVars r
  freeVars (Irrefutable _ e) = freeVars e
  freeVars (LabeledUpdate _ e kvs) =
    freeVars e <> freeVars (map snd kvs) <> S.fromList (map fst kvs)
  freeVars (PrefixNegation _ e) =
    freeVars e
  freeVars (Sequence _ e s f) =
    freeVars e <> freeVars s <> freeVars f
  freeVars (ListComp _ e stmts) = freeVars e <> freeVars stmts
  freeVars (List _ es)        = freeVars es
  freeVars (Tuple _ es)       = freeVars es
  freeVars (Do _ stmts)       = freeVars stmts
  freeVars (LeftSection _ e _)  = freeVars e
  freeVars (RightSection _ _ e) = freeVars e

  freeVars (Let _ decs e)    =
    freeVars e `S.difference` S.fromList (getName <$> decs)

  freeVars (Case _ e alts)    =
    freeVars e `S.difference` freeVars alts

  freeVars (Var _ x)         = S.singleton x
  freeVars (App _ f x)       = freeVars f `S.union` freeVars x
  freeVars (Lam _ args body) = freeVars body `S.difference` freeVars args
  freeVars (Lit _ _)       = mempty
  freeVars (Wildcard _)    = mempty
  freeVars (Fail _)        = mempty
  freeVars (TypeAnn _ e)   = freeVars e
  freeVars (IfThenElse _ cond e1 e2)   =
    freeVars cond <> freeVars e1 <> freeVars e2

  -- NOTE: since this is used when elaborating binding args
  -- we only return the name. TODO: make patterns its own data type
  freeVars (As _ name _)   = S.singleton name

  freeVars (Con _ _ args)   = freeVars args

instance Substitution typ => Substitution (Alt kind typ) where
  freeVars (Alt p e _)   = freeVars e `S.difference` freeVars p
  freeVars (AltGd p _ _) = freeVars p

instance Substitution Kind where
  freeVars (KindVar (MkKindVar k)) = S.singleton k
  freeVars (KindFun k1 k2)         = freeVars k1 `S.union` freeVars k2
  freeVars _ = mempty

instance Substitution (Type a) where
  freeVars (TypeVar _ (TyVar tyVar)) = S.singleton tyVar
  freeVars (TypeFun _ x y) = freeVars x `S.union` freeVars y
  freeVars (TypeApp _ x y) = freeVars x `S.union` freeVars y
  freeVars _ = mempty

occursCheck
  :: (MetaVars a, Substitution a, Show a)
  => MetaVar
  -> a
  -> Infer a ()
occursCheck mv k = do
  when (mv `S.member` metaVars k) $
    bail (OccursCheckFailed mv k)

-- occursCheckType :: MetaVar -> Type Kind -> Infer a ()
-- occursCheckType mv t =
--   when (mv `S.member` metaVars t) $
--     bail (OccursCheckFailedType mv t)

modifySub :: (Subst a -> Subst a) -> Infer a ()
modifySub f = do
  subs <- gets substitutions
  modify $ \s -> s { substitutions = f subs }

modifySchemeEnv
  :: (Map Name (Scheme a) -> Map Name (Scheme a)) -> Infer a ()
modifySchemeEnv f = do
  e <- gets schemeEnv
  modify $ \s -> s { schemeEnv = f e }

type SubstTyped = Map MetaVar (Type Kind)

-- modifyTypeSub :: (SubstTyped -> SubstTyped) -> Infer a ()
-- modifyTypeSub f = do
--   subs <- gets typeSubstitutions
--   modify $ \s -> s { typeSubstitutions = f subs }

getKind :: MetaVar -> Infer Kind Kind
getKind mv = do
  M.findWithDefault (KindMetaVar mv) mv <$> gets substitutions
  -- case generalize result of
  --   scheme ->
  --     pure (KindScheme scheme)

getType :: MetaVar -> Infer (Type Kind) (Type Kind)
getType mv =
  M.findWithDefault (TypeMetaVar Type mv) mv <$>
    gets substitutions

substituteTyped :: Decl Kind MetaVar -> Infer (Type Kind) (Decl Kind (Type Kind))
substituteTyped decl = do
  dbg "Substituting Type..."
  substituteDeclType decl

substituteConDeclTyped
  :: ConDecl Kind MetaVar
  -> Infer (Type Kind) (ConDecl Kind (Type Kind))
substituteConDeclTyped (ConDecl k typs typ)  = do
  t <- getType typ
  pure (ConDecl k typs t)
substituteConDeclTyped (ConDeclRec n fields ty)  = do
  t <- getType ty
  pure (ConDeclRec n fields t)
substituteDeclType
  :: Decl Kind MetaVar
  -> Infer (Type Kind) (Decl Kind (Type Kind))
substituteDeclType (Data k n args vars) = do
  vs <- traverse substituteConDeclTyped vars
  pure (Data k n args vs)
substituteDeclType (TypeSyn kind n args body) =
  pure (TypeSyn kind n args body)
substituteDeclType (Class kind name args decls) = do
  ds <- traverse substituteDeclType decls
  pure (Class kind name args ds)
substituteDeclType (Instance supers ctx decls) = do
  ds <- traverse substituteDeclType decls
  pure (Instance supers ctx ds)
substituteDeclType (Newtype kind name args var) = do
  v <- substituteConDeclTyped var
  pure (Newtype kind name args v)
substituteDeclType (KindSig name sig) =
  pure (KindSig name sig)
substituteDeclType (Foreign name typ) =
  pure (Foreign name typ)
substituteDeclType (TypeSig name args body) =
  pure (TypeSig name args body)
substituteDeclType (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)
substituteDeclType (Decl typ bindings) = do
  t <- getType typ
  bs <- traverse substituteBindingType bindings
  pure (Decl t bs)

substituteBindingType
  :: Binding Kind MetaVar
  -> Infer (Type Kind) (Binding Kind (Type Kind))
substituteBindingType (Binding mv name args body) = do
  typ <- getType mv
  args' <- traverse substituteExpType args
  body' <- substituteExpType body
  pure (Binding typ name args' body')

substituteGuardsType
  :: Guards Kind MetaVar
  -> Infer (Type Kind) (Guards Kind (Type Kind))
substituteGuardsType (Guards stmts e) = do
  stmts_ <- traverse substituteStmtType stmts
  e_ <- substituteExpType e
  pure (Guards stmts_ e_)

substituteAltType
  :: Alt Kind MetaVar
  -> Infer (Type Kind) (Alt Kind (Type Kind))
substituteAltType (Alt l r ds) = do
  l_ <- substituteExpType l
  r_ <- substituteExpType r
  ds_ <- traverse substituteDeclType ds
  pure (Alt l_ r_ ds_)

substituteAltType (AltGd l gds ds) = do
  l_ <- substituteExpType l
  gds_ <- traverse substituteGuardsType gds
  ds_ <- traverse substituteDeclType ds
  pure (AltGd l_ gds_ ds_)

substituteExpType
  :: Exp Kind MetaVar
  -> Infer (Type Kind) (Exp Kind (Type Kind))
substituteExpType (LabeledUpdate mv e kvs) = do
  typ <- getType mv
  kvs_ <- forM kvs $ \(k,v) -> do
    v_ <- substituteExpType v
    pure (k,v_)
  e_ <- substituteExpType e
  pure (LabeledUpdate typ e_ kvs_)
substituteExpType (Irrefutable mv e) = do
  typ <- getType mv
  e_ <- substituteExpType e
  pure (Irrefutable typ e_)
substituteExpType (PrefixNegation mv e) = do
  typ <- getType mv
  e_ <- substituteExpType e
  pure (PrefixNegation typ e_)
substituteExpType (List mv es) = do
  typ <- getType mv
  es_ <- traverse substituteExpType es
  pure (List typ es_)
substituteExpType (ListComp mv e stmts) = do
  typ <- getType mv
  e_ <- substituteExpType e
  stmts_ <- traverse substituteStmtType stmts
  pure (ListComp typ e_ stmts_)
substituteExpType (Tuple mv es) = do
  typ <- getType mv
  es_ <- traverse substituteExpType es
  pure (Tuple typ es_)
substituteExpType (LeftSection mv e name) = do
  typ <- getType mv
  e_ <- substituteExpType e
  pure (LeftSection typ e_ name)
substituteExpType (RightSection mv name e) = do
  typ <- getType mv
  e_ <- substituteExpType e
  pure (RightSection typ name e_)
substituteExpType (Var mv name) = do
  typ <- getType mv
  pure (Var typ name)
substituteExpType (PrimOp mv name) = do
  typ <- getType mv
  pure (PrimOp typ name)
substituteExpType (Case mv e alts) = do
  typ <- getType mv
  e_ <- substituteExpType e
  alts_ <- traverse substituteAltType alts
  pure (Case typ e_ alts_)
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
substituteExpType (InfixOp mv e1 n e2) = do
  typ <- getType mv
  e1_ <- substituteExpType e1
  e2_ <- substituteExpType e2
  pure (InfixOp typ e1_ n e2_)
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
substituteExpType (Fail mv) = do
  typ <- getType mv
  pure (Fail typ)
substituteExpType (TypeAnn t e) = do
  e' <- substituteExpType e
  pure (TypeAnn t e')
substituteExpType (IfThenElse mv cond e1 e2) = do
  typ <- getType mv
  cond' <- substituteExpType cond
  e1' <- substituteExpType e1
  e2' <- substituteExpType e2
  pure (IfThenElse typ cond' e1' e2')
substituteExpType (Let t decs e) = do
  typ <- getType t
  decs' <- traverse substituteDeclType decs
  e' <- substituteExpType e
  pure (Let typ decs' e')
substituteExpType (Do mv stmts) = do
  typ <- getType mv
  stmts_ <- traverse substituteStmtType stmts
  pure (Do typ stmts_)
substituteExpType (Sequence mv e s f) = do
  typ <- getType mv
  e_ <- substituteExpType e
  s_ <- traverse substituteExpType s
  f_ <- traverse substituteExpType f
  pure (Sequence typ e_ s_ f_)

substituteStmtType
  :: Stmt Kind MetaVar
  -> Infer (Type Kind) (Stmt Kind (Type Kind))
substituteStmtType (SBind p e) = do
  p_ <- substituteExpType p
  e_ <- substituteExpType e
  pure (SBind p_ e_)
substituteStmtType (SExp e) = do
  e_ <- substituteExpType e
  pure (SExp e_)
substituteStmtType (SLet decls) = do
  decls_ <- traverse substituteDeclType decls
  pure (SLet decls_)

substitute
  :: Decl MetaVar ()
  -> Infer Kind (Decl Kind ())
substitute decl = do
  dbg "Substituting Kind..."
  substituteDecl decl

substituteDecl :: Decl MetaVar () -> Infer Kind (Decl Kind ())
substituteDecl (Class mv supers p decls) = do
  substitutedKind <- getKind mv
  supers_ <- traverse substitutePred supers
  p_ <- substitutePred p
  decls_ <- traverse substituteDecl decls
  pure (Class substitutedKind supers_ p_ decls_)
substituteDecl (TypeSyn mv name vars typ) = do
  substitutedKind <- getKind mv
  vs <- traverse substituteType vars
  typ' <- substituteType typ
  pure (TypeSyn substitutedKind name vs typ')
substituteDecl (Data mv name vars variants) = do
  vs <- traverse substituteType vars
  substitutedKind <- getKind mv
  substitutedConDecls <- mapM substituteConDecl variants
  pure (Data substitutedKind name vs substitutedConDecls)
substituteDecl (Newtype mv name vars variant) = do
  vs <- traverse substituteType vars
  substitutedKind <- getKind mv
  substitutedConDecl <- substituteConDecl variant
  pure (Newtype substitutedKind name vs substitutedConDecl)
substituteDecl (KindSig name kind) =
  pure (KindSig name kind)
substituteDecl (Instance supers context decls) = do
  ds <- traverse substituteDecl decls
  supers_ <- traverse substitutePred supers
  ctx_ <- substitutePred context
  pure (Instance supers_ ctx_ ds)
substituteDecl (TypeSig name ctx typ) = do
  ctx_ <- traverse substitutePred ctx
  t <- substituteType typ
  pure (TypeSig name ctx_ t)
substituteDecl (Foreign name typ) = do
  t <- substituteType typ
  pure (Foreign name t)
substituteDecl (Decl typ bindings) = do
  b <- traverse substituteBinding bindings
  pure (Decl typ b)
substituteDecl (Fixity fixity precedence names) = do
  pure (Fixity fixity precedence names)

substituteBinding :: Binding MetaVar () -> Infer Kind (Binding Kind ())
substituteBinding (Binding t name pats ex) = do
  ps <- traverse substituteExp pats
  e <- substituteExp ex
  pure (Binding t name ps e)

substituteAlt :: Alt MetaVar () -> Infer Kind (Alt Kind ())
substituteAlt (Alt l r ds) =
  Alt
    <$> substituteExp l
    <*> substituteExp r
    <*> traverse substituteDecl ds
substituteAlt (AltGd p gds ds) =
  AltGd
    <$> substituteExp p
    <*> traverse substituteGuards gds
    <*> traverse substituteDecl ds

substituteGuards
  :: Guards MetaVar ()
  -> Infer Kind (Guards Kind ())
substituteGuards (Guards stmts e) = do
  stmts_ <- traverse substituteStmt stmts
  e_ <- substituteExp e
  pure (Guards stmts_ e_)

substituteStmt :: Stmt MetaVar () -> Infer Kind (Stmt Kind ())
substituteStmt (SBind p e) =
  SBind <$> substituteExp p <*> substituteExp e
substituteStmt (SExp e) =
  SExp <$> substituteExp e
substituteStmt (SLet decls) =
  SLet <$> traverse substituteDecl decls

substituteExp
  :: Exp MetaVar ()
  -> Infer Kind (Exp Kind ())
substituteExp (Var () n) =
  pure (Var () n)
substituteExp (PrimOp () n) =
  pure (PrimOp () n)
substituteExp (InfixOp () e1 n e2) = do
  e1_ <- substituteExp e1
  e2_ <- substituteExp e2
  pure (InfixOp () e1_ n e2_)
substituteExp (Lit () n) =
  pure (Lit () n)
substituteExp (Tuple () es) = do
  es_ <- traverse substituteExp es
  pure (Tuple () es_)
substituteExp (List () es) = do
  es_ <- traverse substituteExp es
  pure (List () es_)
substituteExp (App typ e1 e2) = do
  e1' <- substituteExp e1
  e2' <- substituteExp e2
  pure (App typ e1' e2')
substituteExp (Case () e alts) = do
  e_ <- substituteExp e
  alts_ <- traverse substituteAlt alts
  pure (Case () e_ alts_)
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
substituteExp (Fail ()) =
  pure (Fail ())
substituteExp (TypeAnn t e) = do
  t' <- substituteType t
  ex <- substituteExp e
  pure (TypeAnn t' ex)
substituteExp (IfThenElse () cond e1 e2) = do
  cond' <- substituteExp cond
  e1' <- substituteExp e1
  e2' <- substituteExp e2
  pure (IfThenElse () cond' e1' e2')
substituteExp (Let () decs e) = do
  decs' <- traverse substituteDecl decs
  e' <- substituteExp e
  pure (Let () decs' e')
substituteExp (Do () stmts) = do
  stmts_ <- traverse substituteExpStmt stmts
  pure (Do () stmts_)
substituteExp (LeftSection () e n) = do
  e_ <- substituteExp e
  pure (LeftSection () e_ n)
substituteExp (RightSection () n e) = do
  e_ <- substituteExp e
  pure (RightSection () n e_)
substituteExp (ListComp () e stmts) = do
  e_ <- substituteExp e
  stmts_ <- traverse substituteStmt stmts
  pure (ListComp () e_ stmts_)
substituteExp (Sequence () e s f) = do
  e_ <- substituteExp e
  s_ <- traverse substituteExp s
  f_ <- traverse substituteExp f
  pure (Sequence () e_ s_ f_)
substituteExp (PrefixNegation () e) = do
  e_ <- substituteExp e
  pure (PrefixNegation () e_)
substituteExp (LabeledUpdate () e kvs) = do
  kvs_ <- forM kvs $ \(k,v) -> do
    v_ <- substituteExp v
    pure (k,v_)
  e_ <- substituteExp e
  pure (LabeledUpdate () e_ kvs_)
substituteExp (Irrefutable () e) = do
  e_ <- substituteExp e
  pure (Irrefutable () e_)

substituteExpStmt
  :: Stmt MetaVar ()
  -> Infer Kind (Stmt Kind ())
substituteExpStmt (SBind p e) = do
  p_ <- substituteExp p
  e_ <- substituteExp e
  pure (SBind p_ e_)
substituteExpStmt (SExp e) = do
  e_ <- substituteExp e
  pure (SExp e_)
substituteExpStmt (SLet decls) = do
  decls_ <- traverse substituteDecl decls
  pure (SLet decls_)

substitutePred
  :: Pred MetaVar
  -> Infer Kind (Pred Kind)
substitutePred (Pred n typ) = do
  t <- substituteType typ
  pure (Pred n t)

substituteConDecl
  :: ConDecl MetaVar ()
  -> Infer Kind (ConDecl Kind ())
substituteConDecl (ConDecl name types t) = do
  substituted <- traverse substituteType types
  pure (ConDecl name substituted t)
substituteConDecl (ConDeclRec name fields t) = do
  fields_ <-
    forM fields $ \(n,t1) -> do
      t2 <- substituteType t1
      pure (n,t2)
  pure (ConDeclRec name fields_ t)

substituteType
  :: Type MetaVar
  -> Infer Kind (Type Kind)
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
substituteType (TypeMetaVar k mv) =
  pure (TypeMetaVar k mv)

emptyStateKind :: InferState Kind
emptyStateKind =
  InferState mempty defaultKindEnv
    mempty mempty mempty 0 []

emptyStateType :: InferState (Type Kind)
emptyStateType =
  InferState mempty
    defaultTypeEnv mempty
      mempty mempty 0 []

defaultTypeEnv :: Map String (Scheme (Type Kind))
defaultTypeEnv = M.fromList
  [ ("(+)", Scheme [] (tConT "Int" --> tConT "Int" --> tConT "Int"))
  , ("(,)", Scheme [ "a", "b" ]
            (tVarT "a" --> tVarT "b" -->
              (TypeApp Type
                 (TypeApp Type
                    (TypeCon (Type --> Type --> Type) (TyCon "(,)"))
                    (TypeVar Type (TyVar "a")))
                 (TypeVar Type (TyVar "b")))))
  , ("[]", Scheme [ "a" ]
              (TypeApp Type
                  (TypeCon (Type --> Type) (TyCon "[]"))
                  (TypeVar Type (TyVar "a"))))
  , ("even", Scheme [] (tConT "Int" --> tConT "Bool"))
  ]

defaultKindEnv :: Map String (Scheme Kind)
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
  , ("(,)", Scheme [] (Type --> Type --> Type))
  , ("(,,)", Scheme [] (Type --> Type --> Type --> Type))
  , ("(->)", Scheme [] (Type --> Type --> Type))
  , ("StateT", Scheme [] (Type --> (Type --> Type) --> Type --> Type))
  , ("Identity", Scheme [] (Type --> Type))
  , ("[]", Scheme [] (Type --> Type))
  ]

runInferKind :: Infer Kind a -> IO (Either (Error Kind) a)
runInferKind = runInferWith emptyStateKind

runInferWith :: InferState k -> Infer k a -> IO (Either (Error k) a)
runInferWith s m = evalStateT (runExceptT m) s

dbg :: MonadIO m => String -> m ()
dbg s = when shouldDebug $ liftIO (putStrLn s)

shouldDebug :: Bool
shouldDebug = True

-- TODO: instead of this, return [TypeScheme] from `inferType`
-- so you can add all the variants to the typeEnv
addConstructorsAndFields
  :: [Decl Kind () ]
  -> Infer (Type Kind) ()
addConstructorsAndFields decls = mapM_ go decls
  where
    go (Data kind name args variants) = do
      let tcon = mkTypeCon kind name args
      forM_ variants $ \con -> do
        case con of
          ConDecl varName varArgs _ -> do
            let t = foldr (-->) tcon varArgs
            addToSchemeEnv varName (generalize t)
          ConDeclRec varName fields _ -> do
            -- adds the constructor (e.g. 'MkPerson' in 'data Person = MkPerson String')
            let t = foldr (-->) tcon (fmap snd fields)
            addToSchemeEnv varName (generalize t)
            -- add each member field as well
            forM_ fields $ \(n, t1) -> do
              let ty = tcon --> t1
              addToSchemeEnv n (generalize ty)
    go (Newtype kind name args (ConDecl _ varArgs _)) = do
      let tcon = mkTypeCon kind name args
          t = foldr (-->) tcon varArgs
      addToSchemeEnv name (generalize t)
    go (Newtype kind name args (ConDeclRec varName fields _)) = do
      let tcon = mkTypeCon kind name args
      -- adds the constructor (e.g. 'MkPerson' in 'data Person = MkPerson String')
      let t = foldr (-->) tcon (fmap snd fields)
      addToSchemeEnv varName (generalize t)
      -- add each member field as well
      forM_ fields $ \(n, t1) -> do
        let ty = tcon --> t1
        addToSchemeEnv n (generalize ty)
    go _ = pure ()

-- addKindSigs :: [Decl Kind ()] -> Infer Kind ()
addKindSigs
  :: [Decl kind typ]
  -> Infer Kind ()
addKindSigs decls = do
  let sigs = [ (name, generalize k) | KindSig name k <- decls ]
  mapM_ (uncurry addToSchemeEnv) sigs

addTypeSigs
  :: Generalize (Type kind)
  => [Decl kind typ]
  -> Infer (Type kind) ()
addTypeSigs decls = do
  let sigs = [ (name, generalize typ)
             | TypeSig name _ typ <- decls
             ]
  mapM_ (uncurry addToSchemeEnv) sigs

addBindings :: [Decl Kind ()] -> Infer a ()
addBindings decls =
  forM_ decls $ \decl ->
    case decl of
      Decl _ (Binding () name _ _ : _) ->
        void (addToEnv name)
      _ ->
        pure ()

addToSchemeEnv :: GetName n => n -> Scheme a -> Infer a ()
addToSchemeEnv k v =
  modify $ \s -> s {
    schemeEnv = M.insert (getName k) v (schemeEnv s)
  }

inferKind :: Decl () () -> Infer Kind (Scheme Kind, Decl Kind ())
inferKind decl = do
  dbg "Inferring Kind..."
  elaborated <- elaborateDecl decl
  solve
  d <- substitute elaborated
  pure (generalize (annKind d), d)

populateEnv :: GetName name => [name] -> Infer a ([Name], [MetaVar])
populateEnv decs = fmap unzip $ do
  forM decs $ \d -> do
    let name = getName d
    mv <- addToEnv name
    pure (name, mv)

inferType
  :: Decl Kind ()
  -> Infer (Type Kind) (Maybe (Scheme (Type Kind)), Decl Kind (Type Kind))
inferType decl = do
  elaborated <- elaborateDeclType decl
  solve
  d <- substituteTyped elaborated
  pure (generalizeDeclType d, d)

addToEnv :: GetName name => name -> Infer a MetaVar
addToEnv k = do
  v <- fresh
  modifyEnv (M.insert (getName k) v)
  pure v

modifyEnv :: (Map Name MetaVar -> Map Name MetaVar) -> Infer a ()
modifyEnv f = modify $ \s -> s { env = f (env s) }

-- TODO: implement renaming, to avoid the situation below
-- foo x = x + 1
-- bar foo = foo + 1
-- -- ^ foo here will overwrite the top level binding in env, needs to be renamed
elaborateConDeclType
  :: Type Kind
  -> ConDecl Kind ()
  -> Infer (Type Kind) (ConDecl Kind MetaVar)
elaborateConDeclType t (ConDecl name typs ()) = do
  mv <- fresh
  constrainTypes
    (TypeMetaVar Type mv)
    (foldr (-->) t typs)
  pure (ConDecl name typs mv)
elaborateConDeclType t (ConDeclRec name fields ()) = do
  mv <- fresh
  constrainTypes
    (TypeMetaVar Type mv)
    (foldr (-->) t (snd <$> fields))
  pure (ConDeclRec name fields mv)

mkTypeCon :: Kind -> Name -> [Type Kind] -> Type Kind
mkTypeCon k n = foldl (TypeApp Type) (TypeCon k (TyCon n))

constrainAll :: Ann f => MetaVar -> [f MetaVar] -> Infer (Type Kind) ()
constrainAll mv xs = sequence_
  [ constrainMeta mv (TypeMetaVar Type (ann x))
  | x <- xs
  ]

elaborateDeclType :: Decl Kind () -> Infer (Type Kind) (Decl Kind MetaVar)
elaborateDeclType (Decl () bindings) = do
  mv <- fresh
  bs <- traverse elaborateBindingType bindings
  constrainAll mv bs
  pure (Decl mv bs)
elaborateDeclType (Data kind name args vars) = do
  let con = mkTypeCon kind name args
  vs <- traverse (elaborateConDeclType con) vars
  pure (Data kind name args vs)
elaborateDeclType (TypeSyn kind n args body) =
  pure (TypeSyn kind n args body)
elaborateDeclType (Class kind name args decls) = do
  ds <- traverse elaborateDeclType decls
  pure (Class kind name args ds)
elaborateDeclType (Instance supers ctx decls) = do
  ds <- traverse elaborateDeclType decls
  pure (Instance supers ctx ds)
elaborateDeclType (Newtype kind name args var) = do
  let con = mkTypeCon kind name args
  v <- elaborateConDeclType con var
  pure (Newtype kind name args v)
elaborateDeclType (KindSig name sig) =
  pure (KindSig name sig)
elaborateDeclType (Foreign name typ) =
  pure (Foreign name typ)
elaborateDeclType (TypeSig name args body) =
  pure (TypeSig name args body)
elaborateDeclType (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)

elaborateBindingType :: Binding Kind () -> Infer (Type Kind) (Binding Kind MetaVar)
elaborateBindingType (Binding () name args body) = do
  -- TODO: check for naming conflicts here? or do it in the renamer pass
  -- e.g. foo x@(Just x) = undefined
  mv <- lookupNamedType name
  void $ populateEnv $ S.toList (freeVars args)
  args' <- traverse elaborateExpType args
  body' <- elaborateExpType body
  constrainType mv $
    foldr tFun (TypeMetaVar Type (ann body'))
    (TypeMetaVar Type . ann <$> args')
  pure (Binding mv name args' body')

elaborateExp
  :: Exp () ()
  -> Infer Kind (Exp MetaVar ())
elaborateExp (InfixOp () e1 n e2) = do
  e1_ <- elaborateExp e1
  e2_ <- elaborateExp e2
  pure (InfixOp () e1_ n e2_)
elaborateExp (PrefixNegation () e) = do
  e_ <- elaborateExp e
  pure (PrefixNegation () e_)
elaborateExp (LabeledUpdate () e kvs) = do
  kvs_ <- forM kvs $ \(k,v) -> do
    v_ <- elaborateExp v
    pure (k,v_)
  e_ <- elaborateExp e
  pure (LabeledUpdate () e_ kvs_)
elaborateExp (Var () n) = do
  pure (Var () n)
elaborateExp (PrimOp () n) =
  pure (PrimOp () n)
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
elaborateExp (Fail ()) = do
  pure (Fail ())
elaborateExp (TypeAnn t e) = do
  t' <- elaborateType t
  e' <- elaborateExp e
  pure (TypeAnn t' e')
elaborateExp (Case () e alts) = do
  e_ <- elaborateExp e
  alts_ <- traverse elaborateAlt alts
  pure (Case () e_ alts_)
elaborateExp (IfThenElse () cond e1 e2) = do
  c <- elaborateExp cond
  e1' <- elaborateExp e1
  e2' <- elaborateExp e2
  pure (IfThenElse () c e1' e2')
elaborateExp (Let () decs e) = do
  decs' <- traverse elaborateDecl decs
  e' <- elaborateExp e
  pure (Let () decs' e')
elaborateExp (Do () stmts) = do
  stmts_ <- traverse elaborateStmt stmts
  pure (Do () stmts_)
elaborateExp (LeftSection () e n) = do
  e_ <- elaborateExp e
  pure (LeftSection () e_ n)
elaborateExp (RightSection () n e) = do
  e_ <- elaborateExp e
  pure (RightSection () n e_)
elaborateExp (Tuple () es) = do
  es_ <- traverse elaborateExp es
  pure (Tuple () es_)
elaborateExp (List () es) = do
  es_ <- traverse elaborateExp es
  pure (List () es_)
elaborateExp (ListComp () e stmts) = do
  e_ <- elaborateExp e
  stmts_ <- traverse elaborateStmt stmts
  pure (ListComp () e_ stmts_)
elaborateExp (Sequence () e s f) = do
  e_ <- elaborateExp e
  s_ <- traverse elaborateExp s
  f_ <- traverse elaborateExp f
  pure (Sequence () e_ s_ f_)
elaborateExp (Irrefutable () e) = do
  e_ <- elaborateExp e
  pure (Irrefutable () e_)

elaborateStmt
  :: Stmt () ()
  -> Infer Kind (Stmt MetaVar ())
elaborateStmt (SBind p e) = do
  p_ <- elaborateExp p
  e_ <- elaborateExp e
  pure (SBind p_ e_)
elaborateStmt (SExp e) = do
  e_ <- elaborateExp e
  pure (SExp e_)
elaborateStmt (SLet decls) = do
  decls_ <- traverse elaborateDecl decls
  pure (SLet decls_)

elaborateAlt :: Alt () () -> Infer Kind (Alt MetaVar ())
elaborateAlt (Alt l r ds) =
  Alt <$> elaborateExp l
      <*> elaborateExp r
      <*> traverse elaborateDecl ds
elaborateAlt (AltGd p gds decls) =
  AltGd <$> elaborateExp p
        <*> traverse elaborateGuards gds
        <*> traverse elaborateDecl decls

elaborateGuards :: Guards () () -> Infer Kind (Guards MetaVar ())
elaborateGuards (Guards stmts e) = do
  Guards <$> traverse elaborateStmt stmts <*> elaborateExp e

tFun :: Type Kind -> Type Kind -> Type Kind
tFun = TypeFun Type

elaborateAltType :: Alt Kind () -> Infer (Type Kind) (Alt Kind MetaVar)
elaborateAltType (Alt l r decls) = do
  vs <- uncurry zip <$> populateEnv decls
  decls_ <- traverse elaborateDeclType decls
  generalizeLet vs
  Alt <$> elaborateExpType l
      <*> elaborateExpType r
      <*> pure decls_
elaborateAltType (AltGd p gds decls) = do
  vs <- uncurry zip <$> populateEnv decls
  decls_ <- traverse elaborateDeclType decls
  generalizeLet vs
  AltGd <$> elaborateExpType p
        <*> traverse elaborateGuardsType gds
        <*> pure decls_

elaborateGuardsType
  :: Guards Kind ()
  -> Infer (Type Kind) (Guards Kind MetaVar)
elaborateGuardsType (Guards stmts e) = do
  stmts_ <- traverse elaborateStmtType stmts
  e_ <- elaborateExpType e
  pure (Guards stmts_ e_)

elaborateStmtType :: Stmt Kind () -> Infer (Type Kind) (Stmt Kind MetaVar)
elaborateStmtType (SBind p e) = do
  p_ <- elaborateExpType p
  e_ <- elaborateExpType e
  pure (SBind p_ e_)

elaborateStmtType (SExp e) = do
  e_ <- elaborateExpType e
  pure (SExp e_)

elaborateStmtType (SLet decls) = do
  vs <- uncurry zip <$> populateEnv decls
  decls_ <- traverse elaborateDeclType decls
  generalizeLet vs
  pure (SLet decls_)

elaborateExpType
  :: Exp Kind ()
  -> Infer (Type Kind) (Exp Kind MetaVar)
elaborateExpType (InfixOp () e1 name e2) = do
  mv <- fresh
  op <- lookupNamedType name
  e1_ <- elaborateExpType e1
  e2_ <- elaborateExpType e2
  constrainType op $
    foldr (-->) (TypeMetaVar Type mv)
      [ TypeMetaVar Type (ann e1_)
      , TypeMetaVar Type (ann e2_)
      ]
  pure (InfixOp mv e1_ name e2_)
elaborateExpType (Var () name) = do
  mv <- lookupNamedType name
  pure (Var mv name)
elaborateExpType (PrimOp () name) = do
  mv <- lookupNamedType name
  pure (PrimOp mv name)
elaborateExpType (PrefixNegation () e) = do
  e_ <- elaborateExpType e
  constrainType (ann e_) (TypeCon Type (TyCon "Int"))
  pure (PrefixNegation (ann e_) e_)
elaborateExpType (LabeledUpdate () e kvs) = do
  e_ <- elaborateExpType e -- Person
  kvs_ <- forM kvs $ \(k,v) -> do
    v_ <- elaborateExpType v -- String
    kmv <- lookupNamedType k -- String -> Person
    constrainType kmv
      (TypeMetaVar Type (ann v_) --> TypeMetaVar Type (ann e_))
      -- TODO: get the correct kinds here, ann should have Kind returned
    pure (k,v_)
  pure (LabeledUpdate (ann e_) e_ kvs_)
elaborateExpType (Sequence () e ms mf) = do
  a <- fresh
  e' <- elaborateExpType e
  ms' <- traverse elaborateExpType ms
  mf' <- traverse elaborateExpType mf
  constrainType a (TypeMetaVar Type (ann e'))
  forM_ ms' $ \x ->
    constrainType a (TypeMetaVar Type (ann x))
  forM_ mf' $ \x ->
    constrainType a (TypeMetaVar Type (ann x))
  mv <- fresh
  constrainType mv $
    TypeApp Type
     (TypeCon (Type --> Type) (TyCon "[]"))
     (TypeMetaVar Type a)
  pure (Sequence mv e' ms' mf')
elaborateExpType (ListComp () e stmts) = do
  mv <- fresh
  e' <- elaborateExpType e
  stmts' <- traverse elaborateStmtType stmts
  forM_ stmts' $ \stmt ->
    case stmt of
      SBind p_ e_ ->
        constrainType (ann p_) (TypeMetaVar Type (ann e_))
      SExp e_ ->
        constrainType (ann e_) (TypeCon Type (TyCon "Bool"))
      SLet _ ->
        pure ()
  constrainType mv (TypeMetaVar Type (ann e'))
  pure (ListComp mv e' stmts')
elaborateExpType (Case () scrutinee alts) = do
  patMv <- fresh
  expMv <- fresh
  scrutinee_ <- elaborateExpType scrutinee
  constrainType patMv (TypeMetaVar Type (ann scrutinee_))
  alts_ <- traverse elaborateAltType alts
  forM_ alts_ $ \alt ->
    case alt of
      Alt pat ex _ -> do
        constrainType patMv (TypeMetaVar Type (ann pat))
        constrainType expMv (TypeMetaVar Type (ann ex))
      AltGd pat guards _ -> do
        constrainType patMv (TypeMetaVar Type (ann pat))
        forM_ guards $ \(Guards stmts e) -> do
          constrainType expMv (TypeMetaVar Type (ann e))
          forM_ stmts $ \stmt ->
            case stmt of
              SBind p_ e_ ->
                constrainType (ann p_) (TypeMetaVar Type (ann e_))
              SExp e_ ->
                constrainType (ann e_) (TypeCon Type (TyCon "Bool"))
              SLet _ ->
                pure ()
  constrainType patMv (TypeMetaVar Type (ann scrutinee_))
  pure (Case expMv scrutinee_ alts_)
elaborateExpType (Do () stmts) = do
  mv <- fresh
  void $ populateEnv $ S.toList (freeVars stmts)
  stmts_ <- traverse elaborateStmtType stmts
  forM_ stmts_ $ \stmt ->
    case stmt of
      SBind p e -> do
        m <- fresh
        a <- fresh
        let ma = TypeApp Type (TypeMetaVar (Type --> Type) m) (TypeMetaVar Type a)
        constrainType a (TypeMetaVar Type (ann p))
        constrainTypes ma (TypeMetaVar Type (ann e))
        constrainType mv ma
      SExp e -> do
        constrainType mv (TypeMetaVar Type (ann e))
      SLet _ ->
        pure ()
  case last stmts_ of
    SExp _ -> pure ()
    _ -> throwError LastDoStmtMustBeExp
  pure (Do mv stmts_)

elaborateExpType (Irrefutable () e) = do
  e_ <- elaborateExpType e
  pure (Irrefutable (ann e_) e_)
elaborateExpType (Lit () lit) = do
  mv <- elaborateLit lit
  pure (Lit mv lit)
elaborateExpType (Wildcard ()) = do
  mv <- fresh
  pure (Wildcard mv)
elaborateExpType (Fail ()) = do
  mv <- fresh
  pure (Fail mv)
elaborateExpType (App () f x) = do
  fun <- elaborateExpType f
  arg <- elaborateExpType x
  mv <- fresh
  constrainType (ann fun)
    (TypeMetaVar Type (ann arg) --> TypeMetaVar Type mv)
  pure (App mv fun arg)
elaborateExpType (Lam () args body) = do
  void $ populateEnv $ S.toList (freeVars args)
  args' <- traverse elaborateExpType args
  body' <- elaborateExpType body
  mv <- fresh
  constrainType mv $
    foldr (-->)
      (TypeMetaVar Type(ann body'))
      (fmap (TypeMetaVar Type. ann) args')
  pure (Lam mv args' body')
elaborateExpType (As () name pat) = do
  mv <- lookupNamedType name
  pat' <- elaborateExpType pat
  constrainType mv (TypeMetaVar Type(ann pat'))
  pure (As mv name pat')
elaborateExpType (Con () name args) = do
  _ <- populateEnv $ S.toList (freeVars args)
  mv <- fresh
  con <- lookupNamedType name
  args' <- traverse elaborateExpType args
  constrainType con
    (foldr tFun
       (TypeMetaVar Type mv)
       (TypeMetaVar Type . ann <$> args'))
  pure (Con mv name args')
elaborateExpType (TypeAnn t e) = do
  e' <- elaborateExpType e
  constrainTypes t (TypeMetaVar Type(ann e'))
  pure (TypeAnn t e')
elaborateExpType (IfThenElse () cond e1 e2) = do
  mv <- fresh
  cond' <- elaborateExpType cond
  constrainType (ann cond') (TypeCon Type (TyCon "Bool"))
  e1' <- elaborateExpType e1
  e2' <- elaborateExpType e2
  constrainType (ann e1') (TypeMetaVar Type(ann e2'))
  constrainType mv (TypeMetaVar Type(ann e1'))
  constrainType mv (TypeMetaVar Type(ann e2'))
  pure (IfThenElse mv cond' e1' e2')
elaborateExpType (Let () decs e) = do
  vars <- uncurry zip <$> populateEnv decs
  decs' <- traverse elaborateDeclType decs
  generalizeLet vars
  e' <- elaborateExpType e
  pure (Let (ann e') decs' e')
elaborateExpType (LeftSection () e n) = do
  mv <- fresh
  e_ <- elaborateExpType e
  n_ <- lookupNamedType n
  constrainType n_
    (TypeMetaVar Type (ann e_) --> TypeMetaVar Type mv)
  pure (LeftSection mv e_ n)
elaborateExpType (RightSection () n e) = do
  mv <- fresh
  e_ <- elaborateExpType e
  n_ <- lookupNamedType n
  constrainType n_ (TypeMetaVar Type (ann e_) --> TypeMetaVar Type mv)
  pure (RightSection mv n e_)
elaborateExpType (Tuple () es) = do
  es_ <- traverse elaborateExpType es
  mv <- fresh
  con <- lookupNamedType (parens (replicate (length es - 1) ','))
  constrainType con $
    foldr tFun (TypeMetaVar Type mv)
      [ TypeMetaVar Type (ann e)
      | e <- es_
      ]
  pure (Tuple mv es_)
elaborateExpType (List () es) = do
  es_ <- traverse elaborateExpType es
  mv <- fresh
  con <- lookupNamedType "[]"
  forM_ es_ $ \e ->
    constrainType
      con (TypeApp Type (TypeCon (Type --> Type) (TyCon "[]"))
             (TypeMetaVar Type (ann e)))
  constrainType con (TypeMetaVar Type mv)
  pure (List con es_)

-- z = let { f x y = let { g = x y } in g } in (,) (f ((+)1) 1) (f (const 'a') 'b')

generalizeLet :: [(Name, MetaVar)] -> Infer (Type Kind) ()
generalizeLet vars = do
  dbg "Generalizing Let"
  solve
  ctx <- S.fromList . M.elems <$> gets env
  typeSubs <- gets substitutions
  forM_ vars $ \(name, mv) ->
     case typeSubs M.! mv of
       TypeMetaVar{} ->
         pure ()
       t -> do
         addToSchemeEnv name
           $ applySubs typeSubs
           $ generalizeTypeIgnoringEnv ctx t
  where
    applySubs
      :: Map MetaVar (Type Kind)
      -> Scheme (Type Kind)
      -> Scheme (Type Kind)
    applySubs subs (Scheme vs t) = Scheme vs (cata go t)
      where
        go (TypeMetaVar k m) =
          case M.lookup m subs of
            Nothing -> TypeMetaVar k m
            Just z -> z
        go x = x

elaborateLit :: Lit -> Infer (Type Kind) MetaVar
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

elaborateDecl :: Decl () () -> Infer Kind (Decl MetaVar ())
elaborateDecl decl = do
  dbg "Elaborating..."
  elaborate decl

handleKindSig
  :: Name
  -> MetaVar
  -> Infer Kind ()
handleKindSig name mv = do
  result <- lookupKindEnv name
  forM_ result (constrainMeta mv . KindMetaVar)

elaborate :: Decl () () -> Infer Kind (Decl MetaVar ())
elaborate (TypeSyn () name vars typ) = do
  mv <- addToEnv name
  handleKindSig name mv
  (_, ms) <- populateEnv vars
  let mvs = fmap KindMetaVar ms
  vs <- traverse elaborateType vars
  t <- elaborateType typ
  constrainMeta mv (foldr (-->) (KindMetaVar (ann t)) mvs)
  pure (TypeSyn mv name vs t)
elaborate (Data () name vars variants) = do
  mv <- addToEnv name
  handleKindSig name mv
  (_, mvs) <- fmap (fmap KindMetaVar) <$> populateEnv (getName <$> vars)
  vars' <- traverse elaborateType vars
  vs <- traverse elaborateConDecl variants
  constrainMeta mv (foldr (-->) Type mvs)
  pure (Data mv name vars' vs)
elaborate (Newtype () name vars variant) = do
  mv <- addToEnv name
  handleKindSig  name mv
  (_, mvs) <- fmap (fmap KindMetaVar) <$> populateEnv (getName <$> vars)
  vars' <- traverse elaborateType vars
  v <- elaborateConDecl variant
  constrainMeta mv (foldr (-->) Type mvs)
  pure (Newtype mv name vars' v)
elaborate (Class () supers p decls) = do
  mv <- addToEnv p
  handleKindSig (getName p) mv
  void $ populateEnv $ S.toList (freeVars p <> freeVars decls)
  supers_ <- traverse elaboratePred supers
  p_ <- elaboratePred p
  decls_ <- traverse elaborateDecl decls
  mvs <- fmap KindMetaVar <$>
    traverse lookupName (S.toList (freeVars p))
  constrainMeta mv (foldr (-->) Constraint mvs)
  pure (Class mv supers_ p_ decls_)
elaborate (KindSig name kind) = do
  mv <- addToEnv name
  constrainMeta mv kind
  pure (KindSig name kind)
elaborate (Instance supers ctx decls) = do
  checkInstanceHead supers ctx
  addContextToEnv supers
  supers_ <- traverse elaboratePred supers
  ctx_ <- elaboratePred ctx
  decls_ <- traverse elaborate decls
  pure (Instance supers_ ctx_ decls_)
elaborate (TypeSig name ctx typ) = do
  mv <- addToEnv name
  addContextToEnv ctx
  ctx_ <- traverse elaboratePred ctx
  t <- elaborateType typ
  constrainMeta (ann t) Type
  constrainMeta mv (KindMetaVar (ann t))
  pure (TypeSig name ctx_ t)
elaborate (Foreign name typ) = do
  t <- elaborateType typ
  constrainMeta (ann t) Type
  pure (Foreign name t)
elaborate (Decl () bindings) = do
  bs <- traverse elaborateBinding bindings
  pure (Decl () bs)
elaborate (Fixity fixity precedence names) =
  pure (Fixity fixity precedence names)

elaborateBinding
  :: Binding () ()
  -> Infer Kind (Binding MetaVar ())
elaborateBinding (Binding () name pats e) = do
  ps <- traverse elaborateExp pats
  ex <- elaborateExp e
  pure (Binding () name ps ex)

checkInstanceHead :: Show a => [Pred ()] -> Pred () -> Infer a ()
checkInstanceHead supers ctx =
  forM_ supers $ \superPred ->
    forM_ (freeVars ctx `S.difference` freeVars superPred) $ \x ->
      bail (Doesn'tOccurInInstanceHead x superPred ctx)

addContextToEnv :: [Pred ()] -> Infer a ()
addContextToEnv ctx = do
  let fvs = S.unions [ freeVars typ | Pred _ typ <- ctx ]
  void (populateEnv (S.toList fvs))

elaboratePred :: Pred () -> Infer Kind (Pred MetaVar)
elaboratePred (Pred name typ) = do
  class_ <- lookupName name
  type_ <- elaborateType typ
  constrainMeta class_ (KindMetaVar (ann type_) --> Constraint)
  pure (Pred name type_)

elaborateConDecl :: ConDecl () () -> Infer Kind (ConDecl MetaVar ())
elaborateConDecl (ConDecl name types typ) = do
  ts <- traverse elaborateType types
  forM_ ts (\t -> constrainMeta (ann t) Type)
  pure (ConDecl name ts typ)
elaborateConDecl (ConDeclRec name fields typ) = do
  fields_ <-
    forM fields $ \(n,t1) -> do
      t2 <- elaborateType t1
      constrainMeta (ann t2) Type
      pure (n,t2)
  pure (ConDeclRec name fields_ typ)
elaborateType :: Type () -> Infer Kind (Type MetaVar)
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
  constrainMeta
    (ann fun)
    (KindMetaVar (ann arg) --> KindMetaVar mv)
  pure (TypeApp mv fun arg)
elaborateType (TypeFun () l r) = do
  fun <- elaborateType (funTy `app` l)
  arg <- elaborateType r
  mv <- fresh
  constrainMeta
    (ann fun)
    (KindMetaVar (ann arg) --> KindMetaVar mv)
  pure (TypeApp mv fun arg)
elaborateType (TypeMetaVar k mv) =
  pure (TypeMetaVar k mv)

funTy :: Type ()
funTy = tCon "(->)"

lookupKindEnv :: Instantiate a => Name -> Infer a (Maybe MetaVar)
lookupKindEnv name = do
  kindEnv <- gets schemeEnv
  case M.lookup name kindEnv of
    Just scheme ->
      Just <$> instantiate name scheme
    _ -> pure Nothing

lookupName
  :: (Instantiate a, GetName name, Show a)
  => name
  -> Infer a MetaVar
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

lookupNamedType
  :: (Instantiate a, GetName name, Show a)
  => name
  -> Infer a MetaVar
lookupNamedType named = do
  let name = getName named
  typEnv <- gets schemeEnv
  case M.lookup name typEnv of
    Just scheme ->
      instantiate name scheme
    Nothing -> do
      env <- gets env
      case M.lookup name env of
        Nothing -> bail (UnboundName name)
        Just v -> pure v

class Instantiate a where
  instantiate :: Name -> Scheme a -> Infer a MetaVar

instance Instantiate Kind where
  instantiate = instantiateKind

instance Instantiate (Type Kind) where
  instantiate = instantiateType

class Generalize a where
  generalize :: a -> Scheme a

instance Generalize Kind where
  generalize = generalizeKind

instance Generalize (Type Kind) where
  generalize = generalizeType

instantiateKind :: Name -> Scheme Kind -> Infer Kind MetaVar
instantiateKind name s@(Scheme vars kind) = do
  mv <- fresh
  dbg $ "Instantiating Kind: " <> name <> " :: " <> showScheme s
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  constrainMeta mv (cata (replaceKind mapping) kind)
  pure mv
    where
      replaceKind :: Map Name MetaVar -> Kind -> Kind
      replaceKind mapping (KindVar (MkKindVar v)) =
         case M.lookup v mapping of
           Nothing -> KindVar (MkKindVar v)
           Just mv -> KindMetaVar mv
      replaceKind _ k = k

instantiateType :: Name -> Scheme (Type Kind) -> Infer (Type Kind) MetaVar
instantiateType name s@(Scheme vars typ) = do
  mv <- fresh
  dbg $ "Instantiating Type: " <> name <> " :: " <> show s
  mvs <- replicateM (length vars) fresh
  let mapping = M.fromList (zip vars mvs)
  constrainType mv (cataType (replaceType mapping) typ)
  pure mv
    where
      replaceType mapping (TypeVar kind (TyVar v)) =
         case M.lookup v mapping of
           Nothing -> TypeVar kind (TyVar v)
           Just mv -> TypeMetaVar Type mv
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

instance Ann (Exp kind) where
  ann (InfixOp x _ _ _)     = x
  ann (Irrefutable x _)     = x
  ann (PrefixNegation x _)  = x
  ann (LabeledUpdate x _ _) = x
  ann (Sequence x _ _ _)    = x
  ann (ListComp x _ _)      = x
  ann (Var x _)             = x
  ann (PrimOp x _)          = x
  ann (Do x _)              = x
  ann (Lit x _)             = x
  ann (App x _ _)           = x
  ann (Case x _ _)          = x
  ann (Lam x _ _)           = x
  ann (As x _ _)            = x
  ann (Con x _ _)           = x
  ann (Wildcard x)          = x
  ann (TypeAnn _ x)         = ann x
  ann (Let x _ _)           = x
  ann (IfThenElse x _ _ _)  = x
  ann (Fail x)              = x
  ann (LeftSection x _ _)   = x
  ann (RightSection x _ _)  = x
  ann (Tuple x _)           = x
  ann (List x _)            = x

instance Ann Type where
  ann (TypeVar x _)   = x
  ann (TypeCon x _)   = x
  ann (TypeApp x _ _) = x
  ann (TypeFun x _ _) = x
  ann (TypeMetaVar _ _) = error "Called 'ann' on a MetaVar"

instance Ann (Binding typ) where
  ann (Binding t _ _ _) = t

annKind :: Decl Kind typ -> Kind
annKind (Data x _ _ _)          = x
annKind (TypeSyn x _ _ _)       = x
annKind (Class x _ _ _)         = x
annKind (Newtype x _ _ _)       = x
annKind (KindSig _ k)           = k
annKind (TypeSig _ _ _)         = Type
annKind (Instance _ _ _)        = Constraint
annKind (Foreign _ _)           = Type
annKind (Decl _ _)              = Type
annKind (Fixity _ _ _)          = error "no kind for fixity declaration"

class Constrain a where
  constrain :: a -> a -> Infer a ()
  constrainMeta :: MetaVar -> a -> Infer a ()

instance Constrain Kind where
  constrain = constrainKinds
  constrainMeta = constrainKind

instance Constrain (Type Kind) where
  constrain = constrainTypes
  constrainMeta = constrainType

constrainType :: MetaVar -> Type Kind -> Infer (Type Kind) ()
constrainType m t = constrainTypes (TypeMetaVar Type m) t

constrainTypes :: Type Kind -> Type Kind -> Infer (Type Kind) ()
constrainTypes t1 t2 = do
  dbg ("Constraining... " <> showType t1 <> " = " <> showType t2)
  modify $ \e ->
    e { constraints = Equality t1 t2 : constraints e
      }

constrainKind :: MetaVar -> Kind -> Infer Kind ()
constrainKind m k = constrainKinds (KindMetaVar m) k

constrainKinds :: Kind -> Kind -> Infer Kind ()
constrainKinds k1 k2 = do
  dbg ("Constraining... " <> showKind k1 <> " = " <> showKind k2)
  modify $ \e ->
    e { constraints = Equality k1 k2 : constraints e
      }

generalizeDeclType :: Decl Kind (Type Kind) -> Maybe (Scheme (Type Kind))
generalizeDeclType (Decl t _) = Just (generalize t)
generalizeDeclType _ = Nothing

generalizeBinding :: Binding Kind (Type Kind) -> Scheme (Type Kind)
generalizeBinding = generalize . ann

generalizeType :: Type Kind -> Scheme (Type Kind)
generalizeType = generalizeTypeIgnoringEnv mempty

generalizeTypeIgnoringEnv :: Set MetaVar -> Type Kind -> Scheme (Type Kind)
generalizeTypeIgnoringEnv ctx typ = Scheme vars type'
  where
    metavars = S.toList (metaVars typ `S.difference` ctx)
    mapping  = zip (sort metavars) [0..]
    subs     = M.fromList mapping
    oldVars  = S.toList (freeVars typ)
    vars     = S.toList (freeVars type')
    type'    = cataType quantify typ

    quantify (TypeMetaVar k m) =
      case M.lookup m subs of
        Nothing -> TypeMetaVar k m
        Just m' -> TypeVar k (TyVar (showT m'))

    quantify k                 = k

    showT :: Int -> String
    showT = (combos !!)

    combos =
      [ k
      | k <- concat
             [ pure <$> ['a'..'z']
             , (\k v -> k : show v) <$> ['a' .. 'z'] <*> [ 1 .. 99 :: Int ]
             ]
      ,  k `notElem` oldVars
      ]

generalizeKind :: Kind -> Scheme Kind
generalizeKind kind = Scheme vars kind'
  where
    metavars = S.toList (metaVars kind)
    mapping = zip (sort metavars) [ 0 :: Int .. ]
    subs = M.fromList mapping
    oldVars = freeVars kind

    kind' = cataKind quantify kind
    vars = S.toList (freeVars kind')

    quantify (KindMetaVar m) = KindVar (MkKindVar (combos !! (subs M.! m)))
    quantify k               = k

    combos =
      filter (`notElem` oldVars)
        ( "k" : zipWith (++) (repeat "k") (map show [1 :: Int ..]) )

kk :: String
kk = showDecl @() @() $ Fixity Infixr (Just 1) [ "---->" ]

testInfer :: [Decl () ()] -> IO ()
testInfer decs = do
  dbg "Decls..."
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
        dbg $ name <> " :: " <> showScheme scheme
        x <- runInferWith emptyStateType (inferType decl)
        case x of
          Left e -> print e
          Right (ms, inferred) -> do
            forM_ ms (putStrLn . showScheme)
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
int = Data () "Int" [] [ ConDecl "Int" [] () ]

lol :: Decl () ()
lol = Data () "LOL" [ tVar "a", tVar "b" ]
  [ ConDecl "LOL"
    [ app (app (tCon "Either") (tVar "a")) (tVar "b") ]
    ()
  ]

maybeD :: Decl () ()
maybeD = Data () "Maybe" [ tVar "a" ]
  [ ConDecl "Just" [ tVar "a" ] ()
  , ConDecl "Nothing" [] ()
  ]

maybeDT :: Decl Kind ()
maybeDT = Data (Type --> Type) "Maybe" [ TypeVar Type (TyVar "a") ]
  [ ConDecl "Just" [ TypeVar Type (TyVar "a") ] ()
  , ConDecl "Nothing" [] ()
  ]

eitherDT :: Decl Kind ()
eitherDT = Data (Type --> Type --> Type) "Either"
    [ TypeVar Type (TyVar "a")
    , TypeVar Type (TyVar "b")
    ]
    [ ConDecl "Left" [ TypeVar Type (TyVar "a") ] ()
    , ConDecl "Right" [ TypeVar Type (TyVar "b") ] ()
    ]

person :: Decl () ()
person = Data () "Person" []
  [ ConDecl "Person" [ tCon "String", tCon "Int" ] ()
  ]

statet :: Decl () ()
statet = TypeSyn () "Foo" [] (tCon "StateT")

proxy :: Decl () ()
proxy = Newtype () "Proxy" [ tVar "k" ] (ConDecl "Proxy" [] ())

tree :: Decl () ()
tree = Data () "Tree" [ tVar "a" ]
  [ ConDecl "Node" [ tVar "a", app (tCon "Tree") (tVar "a")
                   , app (tCon "Tree") (tVar "a")
                   ] ()
  ]

treefail :: Decl () ()
treefail = Data () "Tree" [ tVar "a" ]
  [ ConDecl "Node" [ tVar "a", tCon "Tree", tCon "Tree" ] ()
  ]

state :: Decl () ()
state = TypeSyn () "State" [ tVar "s", tVar "a" ]
  (tCon "StateT" `app` tVar "s" `app` tCon "Identity" `app` tVar "a")

thisthat :: Decl () ()
thisthat = Data () "ThisThat" [ tVar "l", tVar "r" ]
  [ ConDecl "This" [ tVar "l" ] ()
  , ConDecl "That" [ tVar "r" ] ()
  ]

tConT :: String -> Type Kind
tConT n = TypeCon Type (TyCon n)

tVarT :: String -> Type Kind
tVarT n = TypeVar Type (TyVar n)

tCon :: String -> Type ()
tCon n = TypeCon () (TyCon n)

tVar :: String -> Type ()
tVar n = TypeVar () (TyVar n)

app :: Type () -> Type () -> Type ()
app x y = TypeApp () x y

appT :: Type Kind -> Type Kind -> Type Kind
appT x y = TypeApp Type x y

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
  [ ConDecl "Cofree"
    [ tVar "a"
    , tVar "f" `app` (tCon "Cofree" `app` tVar "f" `app` tVar "a")
    ] ()
  ]

recfail :: Decl () ()
recfail = Data () "Rec" [ tVar "f", tVar "a" ]
  [ ConDecl "Rec"
    [ tVar "f"
    , app (tVar "f") (tVar "a")
    ] ()
  ]

recTest :: IO ()
recTest = testInferType $
  [ Newtype Type "Person" []
    (ConDeclRec "Person" [ ("getName", TypeCon Type (TyCon "String")) ] ())
  , Decl ()
      [ Binding () "foo" [Var () "p"] (App () (Var () "getName") (Var () "p"))
      ]
  ]


-- tests that inference fails if a kind signature doesn't match
okFailTest :: IO ()
okFailTest
  = testInfer
  [ KindSig "OK" (Type --> Type)
  , TypeSyn () "OK" [] (tCon "Int")
  ]

okTest :: IO ()
okTest
  = testInfer
  [ KindSig "OK" Type
  , TypeSyn () "OK" [] (tCon "Int")
  ]

-- TODO: why does this fail?
instTestFunctorMaybe :: IO ()
instTestFunctorMaybe
  = testInfer
  [ functor
  , Instance
      []
      (Pred "Functor" (tCon "Maybe"))
      []
  ]

sectionTest :: IO ()
sectionTest
  = testInferType
  [ Decl () [ Binding () "plusOneL" []
              (LeftSection () (Lit () (LitInt 1)) "(+)")
            ]
  , Decl () [ Binding () "plusOneR" []
                (RightSection () "(+)" (Lit () (LitInt 1)))
            ]
  ]

tupleTest :: IO ()
tupleTest
  = testInferType
  [ Decl () [ Binding () "tupleAdd"
              [ Tuple () [ Var () "x", Var () "y" ]
              ] (Tuple () [ appE (appE (Var () "(+)") (Var () "x")) (lint 1)
                          , Var () "y"
                          ])
            ]
  ] where
      lint = Lit () . LitInt
      appE = App ()

arithSeqTest :: IO ()
arithSeqTest
  = testInferType
  [ Decl () [ Binding () "test1" []
                $ Sequence ()
                   (Lit () (LitInt 2))
                   (Just (Lit () (LitInt 2)))
                   (Just (Lit () (LitInt 30)))
            ]
  , Decl () [ Binding () "test2" [ Var () "x" ]
                $ Sequence ()
                   (Var () "x")
                   (Just (Lit () (LitInt 2)))
                   (Just (Lit () (LitInt 30)))
            ]
  , Decl () [ Binding () "test3" [ Var () "x" ]
                $ Sequence ()
                   (Var () "x")
                   (Just (Lit () (LitChar 'c')))
                   (Just (Lit () (LitChar 'z')))
            ]
  ]

-- z :: Int
-- z =
--   let
--     f x y = let g = x y in g
--   in
--     f (+1) 1

-- let f = (\ x y -> let g = x y in g) in f (\z -> z) 0

-- z = let { f x y = let { g = x y } in g } in ((f ((+)1)) 1, f (const 'a') 'b')
-- z = let { f x y = let { g = x y } in g } in (,) (f ((+)1)) 1
-- TODO: figure out why 'f' isn't being instantiated to two different types
sample :: IO ()
sample = testInferType [ constD, decl ]
  where
    decl = d [ b "z" [] body ]
    body = l [ d [ b "f" [ v "x", v "y" ] lbody ] ] appf
    lbody = l [ d [ b "g" [ ] (ap' (v "x") (v "y")) ] ] (v "g")
    appf = ap' (ap' (v "f") (rs "(+)" (lit 1))) (lit 1)
      -- ap'
      --   (ap' (v "(,)") (ap' (ap' (v "f") (rs "(+)" (lit 1))) (lit 1)))
      --     (ap' (ap' (v "f") (ap' (v "const") (c 'a'))) (c 'b'))
    d = Decl ()
    b = Binding ()
    l = Let ()
    v = Var ()
    ap' = App ()
    rs = RightSection ()
    lit = Lit () . LitInt

listCompTest :: IO ()
listCompTest
  = testInferType
  [ Decl () [ Binding () "test" [ Var () "x" ]
                $ ListComp () (Var () "foo")
                    [ SExp (App () (Var () "even") (Var () "x"))
                    -- , SBind (Var () "x") (App () (Var () "[]") (Lit () (LitInt 1)))
                    , SLet [ Decl () [ Binding () "foo" [] (Var () "x") ] ]
                    ]
            ]
  ]

listTest :: IO ()
listTest
  = testInferType
  [ Decl () [ Binding () "listAdd"
              [ List () [ Var () "x", Var () "y" ]
              ] (List () [ appE (appE (Var () "(+)") (Var () "x")) (lint 1)
                         , Var () "y"
                         ])
            ]
  ] where
      lint = Lit () . LitInt
      appE = App ()

listTest2 :: IO ()
listTest2
  = testInferType
  [ Decl () [ Binding () "listAdd"
              [ List () [ Var () "x", Var () "y", Var () "z" ]
              ] (List () [])
            ]
  ]

oops :: IO ()
oops
  = testInfer
  [ functor
  , Instance
      [ Pred "Eq" (tVar "b") ]
      (Pred "Functor" (tCon "Maybe"))
      []
  ]

instTestNumEither :: IO ()
instTestNumEither
  = testInfer
  [ functor
  , Instance
      [ Pred "Num" (tVar "a") ]
      (Pred "Functor" (tCon "Either" `app` tCon "a"))
      []
  ]

instTestFail :: IO ()
instTestFail
  = testInfer
  [ functor
  , Instance [] (Pred "Functor" (tCon "Int")) []
  ]

functor :: Decl () ()
functor =
  Class () [] (Pred "Functor" (tVar "f"))
    [ TypeSig "fmap" [] fmap_ ]

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

letinex :: IO ()
letinex = testInferType
  [ Decl () [ Binding () "foo" [] letin ]
  ] where
      letin =
        Let () [ Decl () [ Binding () "id" [ Var () "x" ] (Var () "x") ]
               , fixf
               ] (App () (Var () "id") (Lit () (LitInt 1)))

fixf :: Decl Kind ()
fixf =
  Decl () [ bb
          ]

bb :: Binding Kind ()
bb = Binding () "fix" [ Var () "f" ] (App () (Var () "f") ((App () (Var () "fix")) (Var () "f")))

appp :: Exp Kind ()
appp = (App () (Var () "f") ((App () (Var () "fix")) (Var () "f")))


classT :: IO ()
classT = testInferType
  [ Decl () [ Binding () "ten" [] $ Lit () (LitInt 10) ]
  ]

-- | Constructor patterns
isJustWildTypeAnn :: IO ()
isJustWildTypeAnn = testInferType
  [ maybeDT
  , Decl ()
      [ Binding () "isJust"
          [ Con () "Nothing" []
          ] $ Lit () (LitBool False)
      , Binding () "isJust"
          [ Con () "Just" [ TypeAnn tString (Wildcard ()) ]
          ] $ Lit () (LitBool True)
      ]
  ]

-- The last statement in a 'do block' must be an expression (works)
testDoBlock :: IO ()
testDoBlock = testInferType
  [ eitherDT
  , Decl ()
      [ Binding () "thing" [] $ Do ()
          [ SBind (Lit () (LitString "ay"))
              (App () (Con () "Right" []) (Lit () (LitString "hey")))
          , SExp (App () (Con () "Left" []) (Lit () (LitString "oops")))
          ]
      ]
  ]

testDoBlockLet :: IO ()
testDoBlockLet = testInferType
  [ eitherDT
  , Decl ()
      [ Binding () "thing" [] $ Do ()
          [ SLet [ Decl () [ Binding () "x" [] (Lit () (LitInt 1)) ] ]
          , SExp (Var () "x")
          ]
      ]
  ]

testDoBlockLetFail :: IO ()
testDoBlockLetFail = testInferType
  [ eitherDT
  , Decl ()
      [ Binding () "thing" [] $ Do ()
          [ SLet [ Decl () [ Binding () "x" [] (Lit () (LitInt 1)) ] ]
          , SBind (Lit () (LitString "ay"))
              (App () (Con () "Right" []) (Lit () (LitString "hey")))
          , SExp (Var () "x")
          ]
      ]
  ]

loll :: IO ()
loll = testInferType
  [ Decl ()
      [ Binding () "thing" [ Var () "x" ] $ Case () (Var () "x")
        [ AltGd (Lit () (LitInt 1))
           [ Guards [ SExp (Lit () (LitBool True)) ] (Var () "x")
           , Guards [ SExp (Lit () (LitBool False)) ] (Lit () (LitInt 10))
           ] []
        ]
      ]
  ]

infixex :: IO ()
infixex = testInferType
  [ Decl ()
      [ Binding () "foo" [ Var () "x" ] $
          InfixOp () (Lit () (LitInt 1)) "(+)" (Var () "x")
      ]
  ]



-- Inferred types...
-- isJust :: (Maybe Bool) -> Bool
-- isJust x = case x of {
--  Nothing -> False
--  (Just (_ :: Bool)) -> True
-- }
caseEx :: IO ()
caseEx = testInferType
  [ maybeDT
  , Decl ()
      [ Binding () "isJust"
          [ Var () "x"
          ] $ Case () (Var () "x") alts
      ]
  ]  where
       alts =
         [ Alt (Con () "Nothing" []) (Lit () (LitBool False)) []
         , Alt (Con () "Just" [TypeAnn (TypeCon Type (TyCon "Bool")) (Wildcard ())])
             (Lit () (LitBool True)) []
         ]

ifThenElseEx :: IO ()
ifThenElseEx = testInferType
  [ Decl ()
      [ Binding () "foo"
          [ Var () "x"
          ]
          (IfThenElse ()
             (Lit () (LitBool True))
              (Lit () (LitInt 1))
              (Lit () (LitInt 2)))
      ]
  ]

idstr :: IO ()
idstr = testInferType
  [ Decl ()
      [ Binding () "id"
          [ TypeAnn tString (Var () "x")
          ]
          (Var () "x")
      ]
  ]

negtest :: IO ()
negtest = testInferType
  [ Decl ()
      [ Binding () "negate"
          [ Var () "x"
          ]
          (PrefixNegation () (Var () "x"))
      ]
  ]


constDecStr :: IO ()
constDecStr = testInferType [ constD ]

constD :: Decl Kind ()
constD =
    Decl ()
      [ Binding () "const"
          [ Var () "x"
          , TypeAnn tString (Wildcard ())
          ]
          (Var () "x")
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
  , dec doublay
  , dec irref
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
    doublay    = b "both" [] $ lett [ dec (b "f" [] (v "id")) ]
                                 (appE
                                   (appE (tc "(,)")
                                     (appE (v "f") (char 'a')))
                                     (appE (v "f") (lint 1)))
    irref = b "ref" [ Irrefutable () (v "x") ] (TypeAnn tString (v "x"))


    appE   = App ()
    b      = Binding ()
    dec    = Decl () . pure
    v      = Var ()
    tc x   = Con () x []
    lint   = Lit () . LitInt
    char   = Lit () . LitChar
    str    = Lit () . LitString
    double = Lit () . LitDouble
    lam    = Lam ()
    as     = As ()
    lett   = Let ()

-- both = let f = id in (f 'a', f 1)


testInferType :: [Decl Kind ()] -> IO ()
testInferType decls = do
  dbg "Decls..."
  dbg $ intercalate "\n" (showDecl <$> decls)
  result <- inferTypes decls
  case result of
    Left err -> print err
    Right ds -> do
      dbg "\nInferred types..."
      forM_ ds $ \decl -> do
        case decl of
          Decl typ bindings -> do
            let
              scheme = generalizeType typ
              name = getName decl
            dbg $ name <> " :: " <> show scheme
            forM_ bindings $ \b ->
              putStrLn (showBinding b)
            putStrLn ""
          _ -> pure ()

inferTypes
  :: [Decl Kind ()]
  -> IO (Either (Error (Type Kind)) [Decl Kind (Type Kind)])
inferTypes decls = runInferWith emptyStateType $ do
  addTypeSigs decls
  addBindings decls
  addConstructorsAndFields decls
  xs <-
    forM decls $ \d -> do
      dbg ("Inferring type for decl:\n" <> showDecl d)
      (maybeScheme, decl) <- inferType d
      mapM_ (addToSchemeEnv decl) maybeScheme
      -- decl <$ reset
      pure decl
  dump "done"
  pure xs

reset :: Infer a ()
reset =
  modify $ \s ->
    s { env = mempty
      , substitutions = mempty
      , var = 0
      }

inferKinds :: [Decl () ()] -> IO (Either (Error Kind) [Decl Kind ()])
inferKinds decls = runInferWith emptyStateKind $ do
  addKindSigs decls
  forM decls $ \d -> do
    (scheme, decl) <- inferKind d
    addToSchemeEnv decl scheme
    decl <$ reset

-- entailment
bySuper :: Pred a -> Infer k [Pred a]
bySuper (Pred className t) = do
  superClasses <- getSuperclasses className
  cs <-
    forM superClasses $ \superClass ->
      bySuper (Pred superClass t)
  pure (Pred className t : concat cs)

getSuperclasses
  :: ClassName
  -> Infer k [ClassName]
getSuperclasses name = do
  result <- M.lookup name <$> gets classes
  pure $ case result of
    Nothing -> []
    Just cs -> cs

getInstances
  :: ClassName
  -> Infer k [Instance]
getInstances name = do
  result <- M.lookup name <$> gets instances
  pure (case result of
    Nothing -> []
    Just is -> is)

scEntail :: Eq a => [Pred a] -> Pred a -> Infer k Bool
scEntail ps p = do
  supers <- traverse bySuper ps
  pure (any (p `elem`) supers)

getPredType :: Pred a -> Type a
getPredType (Pred _ t) = t


isHnf :: Pred a -> Bool
isHnf (Pred _ t) = hnf t
  where
    hnf TypeCon{}       = False
    hnf TypeMetaVar{}   = True
    hnf TypeVar{}       = False
    hnf (TypeApp _ x _) = hnf x
    hnf (TypeFun _ x _) = hnf x

concatMapM
  :: (Traversable t, Applicative f)
  => (a -> f [b])
  -> t a
  -> f [b]
concatMapM f xs =
  concat <$>
    traverse f xs

