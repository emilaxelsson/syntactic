{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ <= 708)
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE UndecidableInstances #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 800)
{-# LANGUAGE UndecidableSuperClasses #-}
#endif


-- | Type-constrained syntax trees

module Language.Syntactic.Constraint where



import Data.Typeable

import Data.Constraint

import Data.PolyProxy
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
  where
    {-# SPECIALIZE instance (c1 a, c2 a) => (c1 :/\: c2) a #-}

infixr 5 :/\:

-- | Universal type predicate
class    Top a
instance Top a where
  {-# SPECIALIZE instance Top a #-}

pTop :: P Top
pTop = P
{-# INLINABLE pTop #-}

pTypeable :: P Typeable
pTypeable = P
{-# INLINABLE pTypeable #-}

-- | Evidence that the predicate @sub@ is a subset of @sup@
type Sub sub sup = forall a . Dict (sub a) -> Dict (sup a)

-- | Weaken an intersection
weakL :: Sub (c1 :/\: c2) c1
weakL Dict = Dict
{-# INLINABLE weakL #-}

-- | Weaken an intersection
weakR :: Sub (c1 :/\: c2) c2
weakR Dict = Dict
{-# INLINABLE weakR #-}

-- | Subset relation on type predicates
class (sub :: * -> Constraint) :< (sup :: * -> Constraint)
  where
    -- | Compute evidence that @sub@ is a subset of @sup@ (i.e. that @(sup a)@
    -- implies @(sub a)@)
    sub :: Sub sub sup

instance p :< p
  where
    {-# SPECIALIZE instance p :< p #-}
    {-# INLINABLE sub #-}
    sub = id

instance (p :/\: ps) :< p
  where
    {-# SPECIALIZE instance (p :/\: ps) :< p #-}
    {-# INLINABLE sub #-}
    sub = weakL

instance (ps :< q) => ((p :/\: ps) :< q)
  where
    {-# SPECIALIZE instance (ps :< q) => ((p :/\: ps) :< q) #-}
    {-# INLINABLE sub #-}
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
    {-# SPECIALIZE instance (Project sub sup) => Project sub (sup :| pred) #-}
    {-# INLINABLE prj #-}
    prj (C s) = prj s

instance Equality dom => Equality (dom :| pred)
  where
    {-# SPECIALIZE instance (Equality dom) => Equality (dom :| pred) #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (C a) (C b) = equal a b
    exprHash (C a)    = exprHash a

instance Render dom => Render (dom :| pred)
  where
    {-# SPECIALIZE instance (Render dom) => Render (dom :| pred) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (C a) = renderSym a
    renderArgs args (C a) = renderArgs args a

instance Eval dom => Eval (dom :| pred)
  where
    {-# SPECIALIZE instance (Eval dom) => Eval (dom :| pred) #-}
    {-# INLINABLE evaluate #-}
    evaluate (C a) = evaluate a

instance StringTree dom => StringTree (dom :| pred)
  where
    {-# SPECIALIZE instance (StringTree dom) => StringTree (dom :| pred) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args (C a) = stringTreeSym args a



-- | Constrain the result type of the expression by the given predicate
--
-- The difference between ':||' and ':|' is seen in the instances of the 'Sat'
-- type:
--
-- > type Sat (dom :|  pred) = pred :/\: Sat dom
-- > type Sat (dom :|| pred) = pred
data (:||) :: (* -> *) -> (* -> Constraint) -> (* -> *)
  where
    C' :: pred (DenResult sig) => expr sig -> (expr :|| pred) sig

infixl 4 :||

instance Project sub sup => Project sub (sup :|| pred)
  where
    {-# SPECIALIZE instance (Project sub sup) => Project sub (sup :|| pred) #-}
    {-# INLINABLE prj #-}
    prj (C' s) = prj s

instance Equality dom => Equality (dom :|| pred)
  where
    {-# SPECIALIZE instance (Equality dom) => Equality (dom :|| pred) #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (C' a) (C' b) = equal a b
    exprHash (C' a)     = exprHash a

instance Render dom => Render (dom :|| pred)
  where
    {-# SPECIALIZE instance (Render dom) => Render (dom :|| pred) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (C' a) = renderSym a
    renderArgs args (C' a) = renderArgs args a

instance Eval dom => Eval (dom :|| pred)
  where
    {-# SPECIALIZE instance (Eval dom) => Eval (dom :|| pred) #-}
    {-# INLINABLE evaluate #-}
    evaluate (C' a) = evaluate a

instance StringTree dom => StringTree (dom :|| pred)
  where
    {-# SPECIALIZE instance (StringTree dom) => StringTree (dom :|| pred) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args (C' a) = stringTreeSym args a



-- | Expressions that constrain their result types
class Constrained expr
  where
    -- | Returns a predicate that is satisfied by the result type of all
    -- expressions of the given type (see 'exprDict').
    type Sat expr :: * -> Constraint

    -- | Compute a constraint on the result type of an expression
    exprDict :: expr a -> Dict (Sat expr (DenResult a))

instance Constrained dom => Constrained (AST dom)
  where
    {-# SPECIALIZE instance (Constrained dom) => Constrained (AST dom) #-}
    {-# INLINABLE exprDict #-}
    type Sat (AST dom) = Sat dom
    exprDict (Sym s)  = exprDict s
    exprDict (s :$ _) = exprDict s

instance Constrained (sub1 :+: sub2)
  where
    {-# SPECIALIZE instance (Constrained (sub1 :+: sub2)) #-}
    {-# INLINABLE exprDict #-}
    -- | An over-approximation of the union of @Sat sub1@ and @Sat sub2@
    type Sat (sub1 :+: sub2) = Top
    exprDict (InjL _) = Dict
    exprDict (InjR _) = Dict

instance Constrained dom => Constrained (dom :| pred)
  where
    {-# SPECIALIZE instance (Constrained dom) => Constrained (dom :| pred) #-}
    {-# INLINABLE exprDict #-}
    type Sat (dom :| pred) = pred :/\: Sat dom
    exprDict (C s) = case exprDict s of Dict -> Dict

instance Constrained (dom :|| pred)
  where
    {-# SPECIALIZE instance Constrained (dom :|| pred) #-}
    {-# INLINABLE exprDict #-}
    type Sat (dom :|| pred) = pred
    exprDict (C' _) = Dict

type ConstrainedBy expr p = (Constrained expr, Sat expr :< p)

-- | A version of 'exprDict' that returns a constraint for a particular
-- predicate @p@ as long as @(p :< Sat dom)@ holds
exprDictSub :: ConstrainedBy expr p => P p -> expr a -> Dict (p (DenResult a))
{-# SPECIALIZE INLINE exprDictSub :: (ConstrainedBy expr p) => P p -> expr a -> Dict (p (DenResult a)) #-}
exprDictSub = const $ sub . exprDict

-- | A version of 'exprDict' that works for domains of the form
-- @(dom1 :+: dom2)@ as long as @(Sat dom1 ~ Sat dom2)@ holds
exprDictPlus :: (Constrained dom1, Constrained dom2, Sat dom1 ~ Sat dom2) =>
    AST (dom1 :+: dom2) a -> Dict (Sat dom1 (DenResult a))
{-# SPECIALIZE INLINE
      exprDictPlus :: (Constrained dom1, Constrained dom2, Sat dom1 ~ Sat dom2)
                   => AST (dom1 :+: dom2) a -> Dict (Sat dom1 (DenResult a)) #-}
exprDictPlus (s :$ _)       = exprDictPlus s
exprDictPlus (Sym (InjL a)) = exprDict a
exprDictPlus (Sym (InjR a)) = exprDict a



-- | Symbol injection (like ':<:') with constrained result types
class (Project sub sup, Sat sup a) => InjectC sub sup a
  where
    injC :: (DenResult sig ~ a) => sub sig -> sup sig

instance (InjectC sub sup a, Sat (AST sup) a) =>
    InjectC sub (AST sup) a
  where
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,2,0)
    {-# SPECIALIZE instance (InjectC sub sup a, Sat (AST sup) a) => InjectC sub (AST sup) a #-}
#endif
#endif
    {-# INLINABLE injC #-}
    injC = Sym . injC

instance (InjectC sub sup a, Sat (sup :| pred) a) =>
    InjectC sub (sup :| pred) a
  where
    {-# SPECIALIZE instance (InjectC sub sup a, Sat (sup :| pred) a) => InjectC sub (sup :| pred) a #-}
    {-# INLINABLE injC #-}
    injC = C . injC

instance (InjectC sub sup a, Sat (sup :|| pred) a) =>
    InjectC sub (sup :|| pred) a
  where
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,2,0)
    {-# SPECIALIZE instance (InjectC sub sup a, Sat (sup :|| pred) a) => InjectC sub (sup :|| pred) a #-}
#endif
#endif
    {-# INLINABLE injC #-}
    injC = C' . injC

instance (Sat expr a) => InjectC expr expr a
  where
    {-# SPECIALIZE instance (Sat expr a) => InjectC expr expr a #-}
    {-# INLINABLE injC #-}
    injC = id

instance {-# OVERLAPPABLE #-} InjectC expr1 (expr1 :+: expr2) a
  where
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,2,0)
    {-# SPECIALIZE instance InjectC expr1 (expr1 :+: expr2) a #-}
#endif
#endif
    {-# INLINABLE injC #-}
    injC = InjL

instance {-# OVERLAPPABLE #-} InjectC expr1 expr3 a =>
    InjectC expr1 (expr2 :+: expr3) a
  where
#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(7,10,2,0)
    {-# SPECIALIZE instance InjectC expr1 expr3 a => InjectC expr1 (expr2 :+: expr3) a #-}
#endif
#endif
    {-# INLINABLE injC #-}
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
{-# INLINABLE appSymC #-}



-- | Similar to ':||', but rather than constraining the whole result type, it assumes a result
-- type of the form @c a@ and constrains the @a@.
data SubConstr1 :: (* -> *) -> (* -> *) -> (* -> Constraint) -> (* -> *)
  where
    SubConstr1 :: (p a, DenResult sig ~ c a) => dom sig -> SubConstr1 c dom p sig

instance Constrained dom => Constrained (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance Constrained dom => Constrained (SubConstr1 c dom p) #-}
    {-# INLINABLE exprDict #-}
    type Sat (SubConstr1 c dom p) = Sat dom
    exprDict (SubConstr1 s) = exprDict s

instance Project sub sup => Project sub (SubConstr1 c sup p)
  where
    {-# SPECIALIZE instance Project sub sup => Project sub (SubConstr1 c sup p) #-}
    {-# INLINABLE prj #-}
    prj (SubConstr1 s) = prj s

instance Equality dom => Equality (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance Equality dom => Equality (SubConstr1 c dom p) #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (SubConstr1 a) (SubConstr1 b) = equal a b
    exprHash (SubConstr1 s) = exprHash s

instance Render dom => Render (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance Render dom => Render (SubConstr1 c dom p) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (SubConstr1 s) = renderSym s
    renderArgs args (SubConstr1 s) = renderArgs args s

instance StringTree dom => StringTree (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance StringTree dom => StringTree (SubConstr1 c dom p) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args (SubConstr1 a) = stringTreeSym args a

instance Eval dom => Eval (SubConstr1 c dom p)
  where
    {-# SPECIALIZE instance Eval dom => Eval (SubConstr1 c dom p) #-}
    {-# INLINABLE evaluate #-}
    evaluate (SubConstr1 a) = evaluate a



-- | Similar to 'SubConstr1', but assumes a result type of the form @c a b@ and constrains both @a@
-- and @b@.
data SubConstr2 :: (* -> * -> *) -> (* -> *) -> (* -> Constraint) -> (* -> Constraint) -> (* -> *)
  where
    SubConstr2 :: (DenResult sig ~ c a b, pa a, pb b) => dom sig -> SubConstr2 c dom pa pb sig

instance Constrained dom => Constrained (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance Constrained dom => Constrained (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE exprDict #-}
    type Sat (SubConstr2 c dom pa pb) = Sat dom
    exprDict (SubConstr2 s) = exprDict s

instance Project sub sup => Project sub (SubConstr2 c sup pa pb)
  where
    {-# SPECIALIZE instance Project sub sup => Project sub (SubConstr2 c sup pa pb) #-}
    {-# INLINABLE prj #-}
    prj (SubConstr2 s) = prj s

instance Equality dom => Equality (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance Equality dom => Equality (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (SubConstr2 a) (SubConstr2 b) = equal a b
    exprHash (SubConstr2 s) = exprHash s

instance Render dom => Render (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance Render dom => Render (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (SubConstr2 s) = renderSym s
    renderArgs args (SubConstr2 s) = renderArgs args s

instance StringTree dom => StringTree (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance StringTree dom => StringTree (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args (SubConstr2 a) = stringTreeSym args a

instance Eval dom => Eval (SubConstr2 c dom pa pb)
  where
    {-# SPECIALIZE instance Eval dom => Eval (SubConstr2 c dom pa pb) #-}
    {-# INLINABLE evaluate #-}
    evaluate (SubConstr2 a) = evaluate a



--------------------------------------------------------------------------------
-- * Existential quantification
--------------------------------------------------------------------------------

-- | 'AST' with existentially quantified result type
data ASTE :: (* -> *) -> *
  where
    ASTE :: ASTF dom a -> ASTE dom

liftASTE
    :: (forall a . ASTF dom a -> b)
    -> ASTE dom
    -> b
liftASTE f (ASTE a) = f a
{-# INLINABLE liftASTE #-}

liftASTE2
    :: (forall a b . ASTF dom a -> ASTF dom b -> c)
    -> ASTE dom -> ASTE dom -> c
liftASTE2 f (ASTE a) (ASTE b) = f a b
{-# INLINABLE liftASTE2 #-}



-- | 'AST' with bounded existentially quantified result type
data ASTB :: (* -> *) -> (* -> Constraint) -> *
  where
    ASTB :: p a => ASTF dom a -> ASTB dom p

liftASTB
    :: (forall a . p a => ASTF dom a -> b)
    -> ASTB dom p
    -> b
liftASTB f (ASTB a) = f a
{-# INLINABLE liftASTB #-}

liftASTB2
    :: (forall a b . (p a, p b) => ASTF dom a -> ASTF dom b -> c)
    -> ASTB dom p -> ASTB dom p -> c
liftASTB2 f (ASTB a) (ASTB b) = f a b
{-# INLINABLE liftASTB2 #-}

type ASTSAT dom = ASTB dom (Sat dom)



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

instance Equality Empty where
  equal      = error "Not implemented: equal for Empty"
  exprHash   = error "Not implemented: exprHash for Empty"
instance Eval Empty where
  evaluate   = error "Not implemented: equal for Empty"
instance Render Empty where
  renderSym  = error "Not implemented: renderSym for Empty"
  renderArgs = error "Not implemented: renderArgs for Empty"
instance StringTree Empty



universe :: ASTF dom a -> [ASTE dom]
universe a = ASTE a : go a
  where
    go :: AST dom a -> [ASTE dom]
    go (Sym _)  = []
    go (s :$ b) = go s ++ universe b
