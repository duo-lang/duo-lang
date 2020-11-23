module Syntax where

  import Data.List (nub)
  import Data.Map (Map)
  import Data.Set (Set)
  import Data.Bifunctor (bimap)

  import Data.Graph.Inductive.Graph
  import Data.Graph.Inductive.PatriciaTree

  ----------------------------------------------------------------------------------
  -- Twice functor
  ----------------------------------------------------------------------------------

  -- oftenly used data structure, so extracting it and making it a functor is useful
  data Twice a = Twice a a deriving (Eq,Show)
  twiceMap :: (a -> b) -> (a -> b) -> Twice a -> Twice b
  twiceMap f g (Twice x y) = Twice (f x) (g y)

  mergeTwice :: (a -> a -> a) -> Twice a -> a
  mergeTwice f (Twice x y) = f x y

  instance Functor Twice where
    fmap f = twiceMap f f

  ---------------------------------------------------------------------------------
  -- Term/commmand Syntax
  ---------------------------------------------------------------------------------

  type XtorName = String -- start with uppercase
  type FreeVarName = String -- start with lowercase
  type TypeIdentifierName = String -- start with uppercase

  data DataOrCodata = Data | Codata deriving (Eq,Show)
  showDataOrCodata :: DataOrCodata -> String
  showDataOrCodata Data = "+"
  showDataOrCodata Codata = "-"

  data PrdOrCns = Prd | Cns deriving (Eq,Show,Ord)

  type XtorArgs a = Twice [Term a]
  getArg :: Int -> PrdOrCns -> XtorArgs a -> Term a
  getArg j Prd (Twice prds _) = prds !! j
  getArg j Cns (Twice _ cnss) = cnss !! j

  type MatchCase a = (XtorName, Twice [a], Command a)

  data Term a =
      BoundVar Int PrdOrCns Int -- de bruijn indices
    | FreeVar FreeVarName a
    | XtorCall DataOrCodata XtorName (XtorArgs a)
    | Match DataOrCodata [MatchCase a]
    | MuAbs PrdOrCns a (Command a) deriving (Eq,Show)
    -- The PrdOrCns parameter describes the type of variable that is being bound by the mu.
    -- If a mu binds a producer, it is itself a consumer and vice versa.
    -- MuAbs Cns == \mu, MuAbs Prd == \tilde{\mu}.

  -- determines if the term is a producer or a consumer
  -- is only defined for closed terms, since we cannot distinguish producer from consumer variable names
  -- We distinguish them only in the mathematical formaliazation of the syntax, not in the actual implementation
  termPrdOrCns :: Term a -> PrdOrCns
  termPrdOrCns (XtorCall Data _ _)   = Prd
  termPrdOrCns (XtorCall Codata _ _) = Cns
  termPrdOrCns (Match Data _)        = Cns
  termPrdOrCns (Match Codata _)      = Prd
  termPrdOrCns (MuAbs Prd _ _)       = Cns
  termPrdOrCns (MuAbs Cns _ _)       = Prd
  termPrdOrCns (BoundVar _ pc _)     = pc
  termPrdOrCns (FreeVar _ _)         = error "termPrdOrCns: free variable found"

  data Command a = Apply (Term a) (Term a) | Print (Term a) | Done deriving (Eq,Show)

  ------------------------------------------------------------------------------
  -- Type syntax
  ------------------------------------------------------------------------------

  newtype UVar = MkUVar {uvar_id :: Int} deriving (Eq,Ord)

  instance Show UVar where
    show (MkUVar i) = "U" ++ show i

  data Polarity = Pos | Neg deriving (Show,Eq,Ord)

  switchPolarity :: Polarity -> Polarity
  switchPolarity Neg = Pos
  switchPolarity Pos = Neg

  applyVariance :: DataOrCodata -> PrdOrCns -> (Polarity -> Polarity)
  applyVariance Data Prd = id
  applyVariance Data Cns = switchPolarity
  applyVariance Codata Prd = switchPolarity
  applyVariance Codata Cns = id

  type XtorSig a = (XtorName, Twice [a])

  data SimpleType =
      TyVar UVar
    | SimpleType DataOrCodata [XtorSig SimpleType]
    deriving (Show,Eq)

  data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)

  -- free type variables
  newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

  alphaRenameTVar :: [TVar] -> TVar -> TVar
  alphaRenameTVar tvs tv
    | tv `elem` tvs = head [newtv | n <- [0..], let newtv = MkTVar (tvar_name tv ++ show n), not (newtv `elem` tvs)]
    | otherwise = tv

  -- bound type variables (used in recursive types)
  newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

  data TargetType
    = TTyUnion [TargetType]
    | TTyInter [TargetType]
    | TTyTVar TVar
    | TTyRVar RVar
    | TTyRec RVar TargetType
    | TTySimple DataOrCodata [XtorSig TargetType]
    deriving (Eq,Show)

  -- replaces all free type variables in the type, so that they don't intersect with the given type variables
  alphaRenameTargetType :: [TVar] -> TargetType -> TargetType
  alphaRenameTargetType tvs (TTyTVar tv)   = TTyTVar (alphaRenameTVar tvs tv)
  alphaRenameTargetType _   (TTyRVar rv)   = TTyRVar rv
  alphaRenameTargetType tvs (TTyUnion tys) = TTyUnion (map (alphaRenameTargetType tvs) tys)
  alphaRenameTargetType tvs (TTyInter tys) = TTyInter (map (alphaRenameTargetType tvs) tys)
  alphaRenameTargetType tvs (TTyRec rv ty) = TTyRec rv (alphaRenameTargetType tvs ty)
  alphaRenameTargetType tvs (TTySimple s sigs) = TTySimple s $ map (bimap id (twiceMap (map (alphaRenameTargetType tvs)) (map (alphaRenameTargetType tvs)))) sigs

  data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType }

  -- renames free variables of a type scheme, so that they don't intersect with the given list
  alphaRenameTypeScheme :: [TVar] -> TypeScheme -> TypeScheme
  alphaRenameTypeScheme tvs (TypeScheme tvs' ty) = TypeScheme (map (alphaRenameTVar tvs) tvs') (alphaRenameTargetType tvs ty)

  unionOrInter :: Polarity -> [TargetType] -> TargetType
  unionOrInter _ [t] = t
  unionOrInter Pos tys = TTyUnion tys
  unionOrInter Neg tys = TTyInter tys

  freeTypeVars' :: TargetType -> [TVar]
  freeTypeVars' (TTyTVar tv) = [tv]
  freeTypeVars' (TTyRVar _)  = []
  freeTypeVars' (TTyUnion ts) = concat $ map freeTypeVars' ts
  freeTypeVars' (TTyInter ts) = concat $ map freeTypeVars' ts
  freeTypeVars' (TTyRec _ t)  = freeTypeVars' t
  freeTypeVars' (TTySimple _ xtors) = concat (map (\(_,Twice prdTypes cnsTypes) -> concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)) xtors)

  freeTypeVars :: TargetType -> [TVar]
  freeTypeVars = nub . freeTypeVars'

  -- generalizes over all free type variables of a type
  generalize :: TargetType -> TypeScheme
  generalize ty = TypeScheme (freeTypeVars ty) ty

  data Error
    = ParseError String
    | GenConstraintsError String
    | EvalError String
    | SolveConstraintsError String
    deriving (Show,Eq)

  -------------------------------------------------------
  -- Graph syntax
  -------------------------------------------------------

  data HeadCons = HeadCons
    { hc_data :: Maybe (Set XtorName)
    , hc_codata :: Maybe (Set XtorName)
    } deriving (Eq,Show,Ord)

  emptyHeadCons :: HeadCons
  emptyHeadCons = HeadCons Nothing Nothing

  singleHeadCons :: DataOrCodata -> Set XtorName -> HeadCons
  singleHeadCons Data xtors = HeadCons (Just xtors) Nothing
  singleHeadCons Codata xtors = HeadCons Nothing (Just xtors)

  type NodeLabel = (Polarity, HeadCons)

  data EdgeLabel
    = EdgeSymbol DataOrCodata XtorName PrdOrCns Int
    deriving (Eq,Show)

  instance Ord EdgeLabel where
    compare (EdgeSymbol _ _ _ x) (EdgeSymbol _ _ _ y) = compare x y

  type FlowEdge = (Node, Node)

  type TypeGr = Gr NodeLabel EdgeLabel
  type TypeGrEps = Gr NodeLabel (Maybe EdgeLabel)

  typeGrToEps :: TypeGr -> TypeGrEps
  typeGrToEps = emap Just

  type TypeAut = (TypeGr, [Node], [FlowEdge])

  type Environment a = Map String a
  type TermEnvironment = Map FreeVarName (Term ())
  type TypeEnvironment = Map TypeIdentifierName TypeScheme
