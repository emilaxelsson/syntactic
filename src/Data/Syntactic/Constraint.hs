{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- TODO Only `InjectC` should be used overlapped. Move to separate module?

-- | Type-constrained syntax trees

module Data.Syntactic.Constraint where



import Data.Typeable

import Data.Constraint

import Data.PolyProxy
import Data.Syntactic.Syntax
import Data.Syntactic.Interpretation.Equality
import Data.Syntactic.Interpretation.Render
import Data.Syntactic.Interpretation.Evaluation



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

pTop :: P Top
pTop = P

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
class (sub :: * -> Constraint) :< (sup :: * -> Constraint)
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
data (:|) :: (* -> *) -> (* -> Constraint) -> (* -> *)
  where
    C :: pred (DenResult sig) => expr sig -> (expr :| pred) sig

infixl 4 :|

instance Project sub sup => Project sub (sup :| pred)
  where
    prj (C s) = prj s

instance Equality sym => Equality (sym :| pred)
  where
    equal (C a) (C b) = equal a b
    exprHash (C a)    = exprHash a

instance Render sym => Render (sym :| pred)
  where
    renderSym (C a) = renderSym a
    renderArgs args (C a) = renderArgs args a

instance Eval sym => Eval (sym :| pred)
  where
    evaluate (C a) = evaluate a

instance StringTree sym => StringTree (sym :| pred)
  where
    stringTreeSym args (C a) = stringTreeSym args a



-- | Constrain the result type of the expression by the given predicate
--
-- The difference between ':||' and ':|' is seen in the instances of the 'Sat'
-- type:
--
-- > type Sat (sym :|  pred) = pred :/\: Sat sym
-- > type Sat (sym :|| pred) = pred
data (:||) :: (* -> *) -> (* -> Constraint) -> (* -> *)
  where
    C' :: pred (DenResult sig) => expr sig -> (expr :|| pred) sig

infixl 4 :||

instance Project sub sup => Project sub (sup :|| pred)
  where
    prj (C' s) = prj s

instance Equality sym => Equality (sym :|| pred)
  where
    equal (C' a) (C' b) = equal a b
    exprHash (C' a)     = exprHash a

instance Render sym => Render (sym :|| pred)
  where
    renderSym (C' a) = renderSym a
    renderArgs args (C' a) = renderArgs args a

instance Eval sym => Eval (sym :|| pred)
  where
    evaluate (C' a) = evaluate a

instance StringTree sym => StringTree (sym :|| pred)
  where
    stringTreeSym args (C' a) = stringTreeSym args a



-- | Expressions that constrain their result types
class Constrained expr
  where
    -- | Returns a predicate that is satisfied by the result type of all
    -- expressions of the given type (see 'exprDict').
    type Sat expr :: * -> Constraint

    -- | Compute a constraint on the result type of an expression
    exprDict :: expr a -> Dict (Sat expr (DenResult a))

instance Constrained sym => Constrained (AST sym)
  where
    type Sat (AST sym) = Sat sym
    exprDict (Sym s)  = exprDict s
    exprDict (s :$ _) = exprDict s

instance Constrained (sym1 :+: sym2)
  where
    -- | An over-approximation of the union of @Sat sym1@ and @Sat sym2@
    type Sat (sym1 :+: sym2) = Top
    exprDict (InjL s) = Dict
    exprDict (InjR s) = Dict

instance Constrained sym => Constrained (sym :| pred)
  where
    type Sat (sym :| pred) = pred :/\: Sat sym
    exprDict (C s) = case exprDict s of Dict -> Dict

instance Constrained (sym :|| pred)
  where
    type Sat (sym :|| pred) = pred
    exprDict (C' s) = Dict

type ConstrainedBy expr p = (Constrained expr, Sat expr :< p)

-- | A version of 'exprDict' that returns a constraint for a particular
-- predicate @p@ as long as @(p :< Sat sym)@ holds
exprDictSub :: ConstrainedBy expr p => P p -> expr a -> Dict (p (DenResult a))
exprDictSub _ = sub . exprDict

-- | A version of 'exprDict' that works for domains of the form
-- @(sym1 :+: sym2)@ as long as @(Sat sym1 ~ Sat sym2)@ holds
exprDictPlus :: (Constrained sym1, Constrained sym2, Sat sym1 ~ Sat sym2) =>
    AST (sym1 :+: sym2) a -> Dict (Sat sym1 (DenResult a))
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
-- > appSymC :: InjectC sub (AST sup) x
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF sup a -> ASTF sup b -> ... -> ASTF sup x)
appSymC :: (ApplySym sig f sup, InjectC sub (AST sup) (DenResult sig)) => sub sig -> f
appSymC = appSym' . injC



-- | Similar to ':||', but rather than constraining the whole result type, it assumes a result
-- type of the form @c a@ and constrains the @a@.
data SubConstr1 :: (* -> *) -> (* -> *) -> (* -> Constraint) -> (* -> *)
  where
    SubConstr1 :: (p a, DenResult sig ~ c a) => sym sig -> SubConstr1 c sym p sig

instance Constrained sym => Constrained (SubConstr1 c sym p)
  where
    type Sat (SubConstr1 c sym p) = Sat sym
    exprDict (SubConstr1 s) = exprDict s

instance Project sub sup => Project sub (SubConstr1 c sup p)
  where
    prj (SubConstr1 s) = prj s

instance Equality sym => Equality (SubConstr1 c sym p)
  where
    equal (SubConstr1 a) (SubConstr1 b) = equal a b
    exprHash (SubConstr1 s) = exprHash s

instance Render sym => Render (SubConstr1 c sym p)
  where
    renderSym (SubConstr1 s) = renderSym s
    renderArgs args (SubConstr1 s) = renderArgs args s

instance StringTree sym => StringTree (SubConstr1 c sym p)
  where
    stringTreeSym args (SubConstr1 a) = stringTreeSym args a

instance Eval sym => Eval (SubConstr1 c sym p)
  where
    evaluate (SubConstr1 a) = evaluate a



-- | Similar to 'SubConstr1', but assumes a result type of the form @c a b@ and constrains both @a@
-- and @b@.
data SubConstr2 :: (* -> * -> *) -> (* -> *) -> (* -> Constraint) -> (* -> Constraint) -> (* -> *)
  where
    SubConstr2 :: (DenResult sig ~ c a b, pa a, pb b) => sym sig -> SubConstr2 c sym pa pb sig

instance Constrained sym => Constrained (SubConstr2 c sym pa pb)
  where
    type Sat (SubConstr2 c sym pa pb) = Sat sym
    exprDict (SubConstr2 s) = exprDict s

instance Project sub sup => Project sub (SubConstr2 c sup pa pb)
  where
    prj (SubConstr2 s) = prj s

instance Equality sym => Equality (SubConstr2 c sym pa pb)
  where
    equal (SubConstr2 a) (SubConstr2 b) = equal a b
    exprHash (SubConstr2 s) = exprHash s

instance Render sym => Render (SubConstr2 c sym pa pb)
  where
    renderSym (SubConstr2 s) = renderSym s
    renderArgs args (SubConstr2 s) = renderArgs args s

instance StringTree sym => StringTree (SubConstr2 c sym pa pb)
  where
    stringTreeSym args (SubConstr2 a) = stringTreeSym args a

instance Eval sym => Eval (SubConstr2 c sym pa pb)
  where
    evaluate (SubConstr2 a) = evaluate a



--------------------------------------------------------------------------------
-- * Existential quantification
--------------------------------------------------------------------------------

-- | Existential quantification of 'Full'-indexed data
data E e
  where
    E :: e (Full a) -> E e

liftE :: (forall a . e (Full a) -> b) -> E e -> b
liftE f (E a) = f a

liftE2 :: (forall a b . e (Full a) -> e (Full b) -> c) -> E e -> E e -> c
liftE2 f (E a) (E b) = f a b



-- | Constrained existential quantification of 'Full'-indexed data
data B :: (* -> *) -> (* -> Constraint) -> *
  where
    B :: p a => e (Full a) -> B e p

liftB :: (forall a . p a => e (Full a) -> b) -> B e p -> b
liftB f (B a) = f a

liftB2 :: (forall a b . (p a, p b) => e (Full a) -> e (Full b) -> c) -> B e p -> B e p -> c
liftB2 f (B a) (B b) = f a b

type ASTSAT sym = B sym (Sat sym)



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

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
data Empty :: * -> *

instance Constrained Empty
  where
    type Sat Empty = Top
    exprDict = error "Not implemented: exprDict for Empty"

instance Equality   Empty where equal      = error "Not implemented: equal for Empty"
                                exprHash   = error "Not implemented: exprHash for Empty"
instance Eval       Empty where evaluate   = error "Not implemented: equal for Empty"
instance Render     Empty where renderSym  = error "Not implemented: renderSym for Empty"
                                renderArgs = error "Not implemented: renderArgs for Empty"
instance StringTree Empty

universe :: ASTF sym a -> [E (AST sym)]
universe a = E a : go a
  where
    go :: AST sym a -> [E (AST sym)]
    go (Sym s)  = []
    go (s :$ a) = go s ++ universe a

