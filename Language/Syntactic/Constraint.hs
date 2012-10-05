{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Type constrained syntax trees

module Language.Syntactic.Constraint where



import Data.Typeable

import Data.Constraint

import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Render
import Language.Syntactic.Interpretation.Evaluation



--------------------------------------------------------------------------------
-- * Type predicates
--------------------------------------------------------------------------------

-- | Intersection of type predicates
class    (c1 a, c2 a) => (c1 :/\: c2) a
instance (c1 a, c2 a) => (c1 :/\: c2) a

infixr 5 :/\:

-- | Universal type predicate
class    Top a
instance Top a

-- | Proxy type for passing a type predicate @(* -> Constraint)@ to a function
data PProxy :: (* -> Constraint) -> *
  where
    PProxy :: PProxy p

pTop :: PProxy Top
pTop = PProxy

pTypeable :: P Typeable
pTypeable = P

-- | Evidence that the predicate @sub@ is a subset of @sup@
type Sub sub sup = forall a . Dict (sub a) -> Dict (sup a)

-- | Weaken an intersection
weakL :: Sub (c1 :/\: c2) c1
weakL Dict = Dict

-- | Weaken an intersection
weakR :: Sub (c1 :/\: c2) c2
weakR Dict = Dict

-- | Subset relation on type predicates
class sub :< sup
  where
    -- | Compute evidence that @sub@ is a subset of @sup@ (i.e. that @(sup a)@
    -- implies @(sub a)@)
    sub :: Sub sub sup

instance p :< p
  where
    sub = id

instance (p :/\: ps) :< p
  where
    sub = weakL

instance (ps :< q) => ((p :/\: ps) :< q)
  where
    sub = sub . weakR



--------------------------------------------------------------------------------
-- * Constrained syntax
--------------------------------------------------------------------------------

-- | Constrain the result type of the expression by the given predicate
data (expr :| pred) sig
  where
    C :: pred (DenResult sig) => expr sig -> (expr :| pred) sig

infixl 4 :|

instance Project sub sup => Project sub (sup :| pred)
  where
    prj (C s) = prj s

instance Equality dom => Equality (dom :| pred)
  where
    equal (C a) (C b) = equal a b
    exprHash (C a)    = exprHash a

instance Render dom => Render (dom :| pred)
  where
    renderArgs args (C a) = renderArgs args a

instance Eval dom => Eval (dom :| pred)
  where
    evaluate (C a) = evaluate a

instance ToTree dom => ToTree (dom :| pred)
  where
    toTreeArgs args (C a) = toTreeArgs args a



-- | Constrain the result type of the expression by the given predicate
--
-- The difference between ':||' and ':|' is seen in the instances of the 'Sat'
-- type:
--
-- > type Sat (dom :|  pred) = pred :/\: Sat dom
-- > type Sat (dom :|| pred) = pred
data (expr :|| pred) sig
  where
    C' :: pred (DenResult sig) => expr sig -> (expr :|| pred) sig

infixl 4 :||

instance Project sub sup => Project sub (sup :|| pred)
  where
    prj (C' s) = prj s

instance Equality dom => Equality (dom :|| pred)
  where
    equal (C' a) (C' b) = equal a b
    exprHash (C' a)     = exprHash a

instance Render dom => Render (dom :|| pred)
  where
    renderArgs args (C' a) = renderArgs args a

instance Eval dom => Eval (dom :|| pred)
  where
    evaluate (C' a) = evaluate a

instance ToTree dom => ToTree (dom :|| pred)
  where
    toTreeArgs args (C' a) = toTreeArgs args a



-- | The 'C' constructor with an explicit predicate argument
constr :: p (DenResult sig) => PProxy p -> expr sig -> (expr :| p) sig
constr _ = C

-- | The 'C'' constructor with an explicit predicate argument
constr' :: p (DenResult sig) => PProxy p -> expr sig -> (expr :|| p) sig
constr' _ = C'

-- | Guide projection of a constrained symbol by an explicit type predicate
prjC :: Project (sub :| p) sup => sub sig1 -> PProxy p -> sup sig -> Maybe ((sub :| p) sig)
prjC _ _ = prj

-- | Guide projection of a constrained symbol by an explicit type predicate
prjC' :: Project (sub :|| p) sup => sub sig1 -> PProxy p -> sup sig -> Maybe ((sub :|| p) sig)
prjC' _ _ = prj



-- | Expressions that constrain their result types
class Constrained expr
  where
    -- | Returns a predicate that is satisfied by the result type of all
    -- expressions of the given type (see 'exprDict').
    type Sat (expr :: * -> *) :: * -> Constraint

    -- | Compute a constraint on the result type of an expression
    exprDict :: expr a -> Dict (Sat expr (DenResult a))

instance Constrained dom => Constrained (AST dom)
  where
    type Sat (AST dom) = Sat dom
    exprDict (Sym s)  = exprDict s
    exprDict (s :$ _) = exprDict s

instance Constrained (sub1 :+: sub2)
  where
    -- | An over-approximation of the union of @Sat sub1@ and @Sat sub2@
    type Sat (sub1 :+: sub2) = Top
    exprDict (InjL s) = Dict
    exprDict (InjR s) = Dict

instance Constrained dom => Constrained (dom :| pred)
  where
    type Sat (dom :| pred) = pred :/\: Sat dom
    exprDict (C s) = case exprDict s of Dict -> Dict

instance Constrained (dom :|| pred)
  where
    type Sat (dom :|| pred) = pred
    exprDict (C' s) = Dict

type ConstrainedBy expr c = (Constrained expr, Sat expr :< c)

-- | A version of 'exprDict' that returns a constraint for a particular
-- predicate @p@ as long as @(p :< Sat dom)@ holds
exprDictSub :: ConstrainedBy expr p => P p -> expr a -> Dict (p (DenResult a))
exprDictSub _ = sub . exprDict

-- | A version of 'exprDict' that works for domains of the form
-- @(dom1 :+: dom2)@ as long as @(Sat dom1 ~ Sat dom2)@ holds
exprDictPlus :: (Constrained dom1, Constrained dom2, Sat dom1 ~ Sat dom2) =>
    AST (dom1 :+: dom2) a -> Dict (Sat dom1 (DenResult a))
exprDictPlus (s :$ _)       = exprDictPlus s
exprDictPlus (Sym (InjL a)) = exprDict a
exprDictPlus (Sym (InjR a)) = exprDict a



-- | Symbol injection (like ':<:') with constrained result types
class (Project sub sup, Sat sup a) => InjectC sub sup a
  where
    injC :: (DenResult sig ~ a) => sub sig -> sup sig

instance InjectC sub sup a => InjectC sub (AST sup) a
  where
    injC = Sym . injC

instance (InjectC sub sup a, pred a) => InjectC sub (sup :| pred) a
  where
    injC = C . injC

instance (InjectC sub sup a, pred a) => InjectC sub (sup :|| pred) a
  where
    injC = C' . injC

instance Sat expr a => InjectC expr expr a
  where
    injC = id

instance InjectC expr1 (expr1 :+: expr2) a
  where
    injC = InjL

instance InjectC expr1 expr3 a => InjectC expr1 (expr2 :+: expr3) a
  where
    injC = InjR . injC



-- | Generic symbol application
--
-- 'appSymC' has any type of the form:
--
-- > appSymC :: InjectC expr (AST dom) x
-- >     => expr (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF dom a -> ASTF dom b -> ... -> ASTF dom x)
appSymC :: (ApplySym sig f dom, InjectC sym (AST dom) (DenResult sig)) => sym sig -> f
appSymC = appSym' . injC



-- | Similar to '(:||)', but rather than constraining the whole result type, it assumes a result
-- type of the form @c a@ and constrains the @a@.
data SubConstr1 dom p sig
  where
    SubConstr1 :: (p a, DenResult sig ~ c a) => dom sig -> SubConstr1 dom p sig

instance Constrained dom => Constrained (SubConstr1 dom p)
  where
    type Sat (SubConstr1 dom p) = Sat dom
    exprDict (SubConstr1 s) = exprDict s

instance Project sub sup => Project sub (SubConstr1 sup p)
  where
    prj (SubConstr1 s) = prj s

instance Equality dom => Equality (SubConstr1 dom p)
  where
    equal (SubConstr1 a) (SubConstr1 b) = equal a b
    exprHash (SubConstr1 s) = exprHash s

instance Render dom => Render (SubConstr1 dom p)
  where
    renderArgs args (SubConstr1 s) = renderArgs args s

instance ToTree dom => ToTree (SubConstr1 dom p)
  where
    toTreeArgs args (SubConstr1 a) = toTreeArgs args a

instance Eval dom => Eval (SubConstr1 dom p)
  where
    evaluate (SubConstr1 a) = evaluate a



-- | Similar to 'SubConstr1', but it assumes a result type of the form @c a b@ and constrains both
-- @a@ and @b@.
data SubConstr2 dom pa pb sig
  where
    SubConstr2 :: (DenResult sig ~ c a b, pa a, pb b) => dom sig -> SubConstr2 dom pa pb sig

instance Constrained dom => Constrained (SubConstr2 dom pa pb)
  where
    type Sat (SubConstr2 dom pa pb) = Sat dom
    exprDict (SubConstr2 s) = exprDict s

instance Project sub sup => Project sub (SubConstr2 sup pa pb)
  where
    prj (SubConstr2 s) = prj s

instance Equality dom => Equality (SubConstr2 dom pa pb)
  where
    equal (SubConstr2 a) (SubConstr2 b) = equal a b
    exprHash (SubConstr2 s) = exprHash s

instance Render dom => Render (SubConstr2 dom pa pb)
  where
    renderArgs args (SubConstr2 s) = renderArgs args s

instance ToTree dom => ToTree (SubConstr2 dom pa pb)
  where
    toTreeArgs args (SubConstr2 a) = toTreeArgs args a

instance Eval dom => Eval (SubConstr2 dom pa pb)
  where
    evaluate (SubConstr2 a) = evaluate a



-- | The 'SubConstr1' constructor with an explicit predicate argument
subConstr1 :: (DenResult sig ~ c a, p a) => PProxy p -> dom sig -> SubConstr1 dom p sig
subConstr1 _ = SubConstr1

-- | The 'SubConstr2' constructor with explicit predicate arguments
subConstr2 :: (DenResult sig ~ c a b, pa a, pb b) =>
    PProxy pa -> PProxy pb -> dom sig -> SubConstr2 dom pa pb sig
subConstr2 _ _ = SubConstr2

-- | Guide projection of a 'SubConstr1' symbol by an explicit type predicate
prjSubConstr1 :: Project (SubConstr1 sym p) sup =>
    sym sig1 -> PProxy pa -> sup sig -> Maybe (SubConstr1 sym p sig)
prjSubConstr1 _ _ = prj

-- | Guide projection of a 'SubConstr2' symbol by an explicit type predicate
prjSubConstr2 :: Project (SubConstr2 sym pa pb) sup =>
    sym sig1 -> PProxy pa -> PProxy pb -> sup sig -> Maybe (SubConstr2 sym pa pb sig)
prjSubConstr2 _ _ _ = prj



-- | 'AST' with existentially quantified result type
data ASTE dom
  where
    ASTE :: ASTF dom a -> ASTE dom

liftASTE
    :: (forall a . ASTF dom a -> b)
    -> ASTE dom
    -> b
liftASTE f (ASTE a) = f a

liftASTE2
    :: (forall a b . ASTF dom a -> ASTF dom b -> c)
    -> ASTE dom -> ASTE dom -> c
liftASTE2 f (ASTE a) (ASTE b) = f a b



-- | 'AST' with bounded existentially quantified result type
data ASTB dom p
  where
    ASTB :: p a => ASTF dom a -> ASTB dom p

liftASTB
    :: (forall a . p a => ASTF dom a -> b)
    -> ASTB dom p
    -> b
liftASTB f (ASTB a) = f a

liftASTB2
    :: (forall a b . (p a, p b) => ASTF dom a -> ASTF dom b -> c)
    -> ASTB dom p -> ASTB dom p -> c
liftASTB2 f (ASTB a) (ASTB b) = f a b

type ASTSAT dom = ASTB dom (Sat dom)



-- * Misc.

-- | Empty symbol type
--
-- Use-case:
--
-- > data A a
-- > data B a
-- >
-- > test :: AST (A :+: (B:||Eq) :+: Empty) a
-- > test = injC (undefined :: (B :|| Eq) a)
--
-- Without 'Empty', this would lead to an overlapping instance error due to the instances
--
-- > InjectC (B :|| Eq) (B :|| Eq) (DenResult a)
--
-- and
--
-- > InjectC sub sup a, pred a) => InjectC sub (sup :|| pred) a
data Empty a

instance Constrained Empty
  where
    type Sat Empty = Top
    exprDict = error "Not implemented: exprDict for Empty"

instance Equality Empty where equal      = error "Not implemented: equal for Empty"
                              exprHash   = error "Not implemented: exprHash for Empty"
instance Eval     Empty where evaluate   = error "Not implemented: equal for Empty"
instance Render   Empty where renderArgs = error "Not implemented: renderArgs for Empty"
instance ToTree   Empty

