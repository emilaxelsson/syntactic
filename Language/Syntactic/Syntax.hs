{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generic representation of typed syntax trees
--
-- As a simple demonstration, take the following simple language:
--
-- > data Expr1 a
-- >   where
-- >     Num1 :: Int -> Expr1 Int
-- >     Add1 :: Expr1 Int -> Expr1 Int -> Expr1 Int
--
-- Using the present library, this can be rewritten as follows:
--
-- > data Num2 a where Num2 :: Int -> Num2 (Full Int)
-- > data Add2 a where Add2 :: Add2 (Int :-> Int :-> Full Int)
-- >
-- > type Expr2 a = ASTF (Num2 :+: Add2) a
--
-- Note that @Num2@ and @Add2@ are /non-recursive/. The only recursive data type
-- here is 'AST', which is provided by the library. Now, the important point is
-- that @Expr1@ and @Expr2@ are completely isomorphic! This is indicated by the
-- following conversions:
--
-- > conv12 :: Expr1 a -> Expr2 a
-- > conv12 (Num1 n)   = inj (Num2 n)
-- > conv12 (Add1 a b) = inj Add2 :$ conv12 a :$ conv12 b
-- >
-- > conv21 :: Expr2 a -> Expr1 a
-- > conv21 (prj -> Just (Num2 n))         = Num1 n
-- > conv21 ((prj -> Just Add2) :$ a :$ b) = Add1 (conv21 a) (conv21 b)
--
-- A key property here is that the patterns in @conv21@ are actually complete.
--
-- So, why should one use @Expr2@ instead of @Expr1@? The answer is that @Expr2@
-- can be processed by generic algorithms defined over 'AST', for example:
--
-- > countNodes :: ASTF domain a -> Int
-- > countNodes = count
-- >   where
-- >     count :: AST domain a -> Int
-- >     count (Sym _)  = 1
-- >     count (a :$ b) = count a + count b
--
-- Furthermore, although @Expr2@ was defined to use exactly the constructors
-- 'Num2' and 'Add2', it is possible to leave the set of constructors open,
-- leading to more modular and reusable code. This can be seen by relaxing the
-- types of @conv12@ and @conv21@:
--
-- > conv12 :: (Num2 :<: dom, Add2 :<: dom) => Expr1 a -> ASTF dom a
-- > conv21 :: (Num2 :<: dom, Add2 :<: dom) => ASTF dom a -> Expr1 a
--
-- This way of encoding open data types is taken from /Data types à la carte/
-- (Wouter Swierstra, /Journal of Functional Programming/, 2008). However, we do
-- not need Swierstra's fixed-point machinery for recursive data types. Instead
-- we rely on 'AST' being recursive.

module Language.Syntactic.Syntax
    ( -- * Syntax trees
      Full (..)
    , (:->) (..)
    , Args (..)
    , WrapFull (..)
    , Signature
    , Denotation
    , DenResult
    , ConsWit (..)
    , WitnessCons (..)
    , fromEval
    , toEval
    , listArgs
    , mapArgs
    , mapArgsM
    , appArgs
    , appEvalArgs
    , ($:)
    , AST (..)
    , ASTF
    , (:+:) (..)
    , ApplySym
    , appSym
    , appSymCtx
      -- * Subsumption
    , (:<:) (..)
    , injCtx
    , prjCtx
      -- * Syntactic sugar
    , Syntactic (..)
    , resugar
    , SyntacticN (..)
    , sugarSym
    , sugarSymCtx
      -- * AST processing
    , queryNode
    , queryNodeSimple
    , transformNode
      -- * Restricted syntax trees
    , Sat (..)
    , Witness (PolyWit, SimpleWit)
        -- TODO A warning reports that these are already exported by 'Sat (..)',
        --      but that is actually not the case. This seems to have been fixed
        --      recently:
        --
        --        http://hackage.haskell.org/trac/ghc/ticket/2436#comment:12
        --
        --      I don't know if the fix just removes the warning, or if it means
        --      that 'Sat (..)' is enough.
    , witnessByProxy
    , SatWit (..)
    , fromSatWit
    , WitnessSat (..)
    , MaybeWitnessSat (..)
    , maybeWitnessSatDefault
    , withContext
    , Poly
    , poly
    , SimpleCtx
    , simpleCtx
    ) where



import Control.Monad.Identity
import Data.Typeable

import Data.Proxy



--------------------------------------------------------------------------------
-- * Syntax trees
--------------------------------------------------------------------------------

-- | The type of a fully applied constructor
newtype Full a = Full { result :: a }
  deriving (Eq, Show, Typeable)

-- | The type of a partially applied (or unapplied) constructor
newtype a :-> b = Partial (a -> b)
  deriving (Typeable)

-- | Heterogeneous list, indexed by a container type and a 'Signature'
data family Args (c :: * -> *) a

data instance Args c (Full a)  = Nil
data instance Args c (a :-> b) = Typeable a => c (Full a) :* Args c b
  -- The 'Typeable' constraint is needed in order to be able to rebuild an 'AST'
  -- from an 'Args' (since '(:$)' has a `Typeable` constraint).

infixr :->, :*

-- | Can be used to turn a type constructor indexed by @a@ to a type constructor
-- indexed by @(`Full` a)@. This is useful together with 'Args', which assumes
-- its constructor to be indexed by @(`Full` a)@. That is, use
--
-- > Args (WrapFull c) ...
--
-- instead of
--
-- > Args c ...
--
-- if @c@ is not indexed by @(`Full` a)@.
data WrapFull c a
  where
    WrapFull :: { unwrapFull :: c a } -> WrapFull c (Full a)

-- | Fully or partially applied constructor
--
-- This class is private to the module to guarantee that all members of the
-- class have the form:
--
-- > Full a
-- > a1 :-> Full a2
-- > a1 :-> a2 :-> ... :-> Full an
--
-- The closed class also has the property:
-- @Signature' (a :-> b)@   iff.   @Signature' b@.
class Signature' a
  where
    type Denotation' a
    type DenResult' a

    fromEval'    :: Denotation' a -> a
    toEval'      :: a -> Denotation' a
    listArgs'    :: (forall a . c (Full a) -> b) -> Args c a -> [b]
    mapArgs'     :: (forall a . c1 (Full a) -> c2 (Full a)) -> Args c1 a -> Args c2 a
    mapArgsM'    :: Monad m => (forall a . c1 (Full a) -> m (c2 (Full a))) -> Args c1 a -> m (Args c2 a)
    appArgs'     :: AST dom a -> Args (AST dom) a -> ASTF dom (DenResult a)
    appEvalArgs' :: Denotation a -> Args Identity a -> DenResult a

instance Signature' (Full a)
  where
    type Denotation' (Full a) = a
    type DenResult'  (Full a) = a

    fromEval'          = Full
    toEval'            = result
    listArgs'    f Nil = []
    mapArgs'     f Nil = Nil
    mapArgsM'    f Nil = return Nil
    appArgs'     a Nil = a
    appEvalArgs' a Nil = a

instance Signature' b => Signature' (a :-> b)
  where
    type Denotation' (a :-> b) = a -> Denotation' b
    type DenResult'  (a :-> b) = DenResult' b

    fromEval'                = Partial . (fromEval' .)
    toEval' (Partial f)      = toEval' . f
    listArgs'    f (a :* as) = f a : listArgs' f as
    mapArgs'     f (a :* as) = f a :* mapArgs' f as
    mapArgsM'    f (a :* as) = liftM2 (:*) (f a) (mapArgsM' f as)
    appArgs'     c (a :* as) = appArgs' (c :$ a) as
    appEvalArgs' f (a :* as) = appEvalArgs' (f $ result $ runIdentity a) as

-- | Fully or partially applied constructor
--
-- This is a public alias for the hidden class 'Signature''. The only instances
-- are:
--
-- > instance Signature' (Full a)
-- > instance Signature' b => Signature' (a :-> b)
class    Signature' a => Signature a
instance Signature' a => Signature a

-- | Maps a 'Signature' to a simpler form where ':->' has been replaced by @->@,
-- and 'Full' has been removed. This is a public alias for the hidden type
-- 'Denotation''.
type Denotation a = Denotation' a

-- | Returns the result type ('Full' removed) of a 'Signature'. This is a public
-- alias for the hidden type 'DenResult''.
type DenResult a = DenResult' a

-- | A witness of @(`Signature` a)@
data ConsWit a
  where
    ConsWit :: Signature a => ConsWit a

-- | Expressions in syntactic are supposed to have the form
-- @(`Signature` a => expr a)@. This class lets us witness the 'Signature'
-- constraint of an expression without examining the expression.
class WitnessCons expr
  where
    witnessCons :: expr a -> ConsWit a

instance (WitnessCons sub1, WitnessCons sub2) => WitnessCons (sub1 :+: sub2)
  where
    witnessCons (InjL a) = witnessCons a
    witnessCons (InjR a) = witnessCons a

-- | Make a constructor evaluation from a 'Denotation' representation
fromEval :: Signature a => Denotation a -> a
fromEval = fromEval'

toEval :: Signature a => a -> Denotation a
toEval = toEval'

-- | Convert a heterogeneous list to a normal list
listArgs :: Signature a => (forall a . c (Full a) -> b) -> Args c a -> [b]
listArgs = listArgs'

-- | Change the container of each element in a heterogeneous list
mapArgs :: Signature a =>
    (forall a . c1 (Full a) -> c2 (Full a)) -> Args c1 a -> Args c2 a
mapArgs = mapArgs'

-- | Change the container of each element in a heterogeneous list, monadic
-- version
mapArgsM :: (Monad m, Signature a) =>
    (forall a . c1 (Full a) -> m (c2 (Full a))) -> Args c1 a -> m (Args c2 a)
mapArgsM = mapArgsM'

-- | Apply the syntax tree to the listed arguments
appArgs :: Signature a =>
    AST dom a -> Args (AST dom) a -> ASTF dom (DenResult a)
appArgs = appArgs'

-- | Apply the evaluation function to the listed arguments
appEvalArgs :: Signature a => Denotation a -> Args Identity a -> DenResult a
appEvalArgs = appEvalArgs'

-- | Semantic constructor application
($:) :: (a :-> b) -> a -> b
Partial f $: a = f a



-- | Generic abstract syntax tree, parameterized by a symbol domain
--
-- In general, @(`AST` dom (a `:->` b))@ represents a partially applied (or
-- unapplied) constructor, missing at least one argument, while
-- @(`AST` dom (`Full` a))@ represents a fully applied constructor, i.e. a
-- complete syntax tree.
-- It is not possible to construct a total value of type @(`AST` dom a)@ that
-- does not fulfill the constraint @(`Signature` a)@.
--
-- Note that the hidden class 'Signature'' mentioned in the type of 'Sym' is
-- interchangeable with 'Signature'.
data AST dom a
  where
    Sym  :: Signature' a => dom a -> AST dom a
    (:$) :: Typeable a => AST dom (a :-> b) -> ASTF dom a -> AST dom b

-- | Fully applied abstract syntax tree
type ASTF dom a = AST dom (Full a)

-- | Co-product of two symbol domains
data dom1 :+: dom2 :: * -> *
  where
    InjL :: dom1 a -> (dom1 :+: dom2) a
    InjR :: dom2 a -> (dom1 :+: dom2) a

infixl 1 :$
infixr :+:



-- | Class that performs the type-level recursion needed by 'appSym'
class ApplySym a f dom | a dom -> f, f -> a dom
  where
    appSym' :: AST dom a -> f

instance ApplySym (Full a) (ASTF dom a) dom
  where
    appSym' = id

instance (Typeable a, ApplySym b f' dom) =>
    ApplySym (a :-> b) (ASTF dom a -> f') dom
  where
    appSym' sym a = appSym' (sym :$ a)

-- | Generic symbol application
--
-- 'appSym' has any type of the form:
--
-- > appSym :: (expr :<: AST dom, Typeable a, Typeable b, ..., Typeable x)
-- >     => expr (a :-> b :-> ... :-> Full x)
-- >     -> (ASTF dom a -> ASTF dom b -> ... -> ASTF dom x)
appSym :: (ApplySym a f dom, Signature a, sym :<: AST dom) => sym a -> f
appSym sym = appSym' (inj sym)

-- | Generic symbol application with explicit context
appSymCtx  :: (ApplySym a f dom, Signature a, sym ctx :<: dom) =>
    Proxy ctx -> sym ctx a -> f
appSymCtx _ = appSym



--------------------------------------------------------------------------------
-- * Subsumption
--------------------------------------------------------------------------------

class sub :<: sup
  where
    -- | Injection from @sub@ to @sup@
    inj :: Signature a => sub a -> sup a

    -- | Partial projection from @sup@ to @sub@
    prj :: sup a -> Maybe (sub a)

instance (sub :<: sup) => ((:<:) sub (AST sup))
                            -- GHC 6.12 requires prefix syntax here
  where
    inj = Sym . inj

    prj (Sym a) = prj a
    prj _       = Nothing

instance ((:<:) expr expr)
  where
    inj = id
    prj = Just

instance ((:<:) expr1 (expr1 :+: expr2))
  where
    inj = InjL

    prj (InjL a) = Just a
    prj _        = Nothing

instance (expr1 :<: expr3) => ((:<:) expr1 (expr2 :+: expr3))
  where
    inj = InjR . inj

    prj (InjR a) = prj a
    prj _        = Nothing



-- | 'inj' with explicit context
injCtx :: (sub ctx :<: sup, Signature a) => Proxy ctx -> sub ctx a -> sup a
injCtx _ = inj

-- | 'prj' with explicit context
prjCtx :: (sub ctx :<: sup) => Proxy ctx -> sup a -> Maybe (sub ctx a)
prjCtx _ = prj



--------------------------------------------------------------------------------
-- * Syntactic sugar
--------------------------------------------------------------------------------

-- | It is assumed that for all types @A@ fulfilling @(`Syntactic` A dom)@:
--
-- > eval a == eval (desugar $ (id :: A -> A) $ sugar a)
--
-- (using 'Language.Syntactic.Interpretation.Evaluation.eval')
class Typeable (Internal a) => Syntactic a dom | a -> dom
    -- Note: using a functional dependency rather than an associated type,
    -- because this makes it possible to make a class alias constraining dom.
    -- GHC doesn't yet handle equality super classes.
  where
    type Internal a
    desugar :: a -> ASTF dom (Internal a)
    sugar   :: ASTF dom (Internal a) -> a

instance Typeable a => Syntactic (ASTF dom a) dom
  where
    type Internal (ASTF dom a) = a
    desugar = id
    sugar   = id

-- | Syntactic type casting
resugar :: (Syntactic a dom, Syntactic b dom, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar

-- | N-ary syntactic functions
--
-- 'desugarN' has any type of the form:
--
-- > desugarN ::
-- >     ( Syntactic a dom
-- >     , Syntactic b dom
-- >     , ...
-- >     , Syntactic x dom
-- >     ) => (a -> b -> ... -> x)
-- >       -> (  AST dom (Full (Internal a))
-- >          -> AST dom (Full (Internal b))
-- >          -> ...
-- >          -> AST dom (Full (Internal x))
-- >          )
--
-- ...and vice versa for 'sugarN'.
class SyntacticN a internal | a -> internal
  where
    desugarN :: a -> internal
    sugarN   :: internal -> a

instance (Syntactic a dom, ia ~ AST dom (Full (Internal a))) => SyntacticN a ia
  where
    desugarN = desugar
    sugarN   = sugar

instance
    ( Syntactic a dom
    , ia ~ Internal a
    , SyntacticN b ib
    ) =>
      SyntacticN (a -> b) (AST dom (Full ia) -> ib)
  where
    desugarN f = desugarN . f . sugar
    sugarN f   = sugarN . f . desugar



-- | \"Sugared\" symbol application
--
-- 'sugarSym' has any type of the form:
--
-- > sugarSym ::
-- >     ( expr :<: AST dom
-- >     , Syntactic a dom
-- >     , Syntactic b dom
-- >     , ...
-- >     , Syntactic x dom
-- >     ) => expr (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >       -> (a -> b -> ... -> x)
sugarSym
    :: (Signature a, sym :<: AST dom, ApplySym a b dom, SyntacticN c b)
    => sym a -> c
sugarSym = sugarN . appSym

-- | \"Sugared\" symbol application with explicit context
sugarSymCtx
    :: (Signature a, sym ctx :<: dom, ApplySym a b dom, SyntacticN c b)
    => Proxy ctx -> sym ctx a -> c
sugarSymCtx _ = sugarSym



--------------------------------------------------------------------------------
-- * AST processing
--------------------------------------------------------------------------------

newtype Const a b = Const {unConst :: a}
  -- Only used in the definition of 'queryNodeSimple'

newtype WrapAST c dom a = WrapAST { unWrapAST :: c (AST dom a) }
  -- Only used in the definition of 'transformNode'

-- | Query an 'AST' using a function that gets direct access to the top-most
-- constructor and its sub-trees
--
-- Note that, by instantiating the type @c@ with @`AST` dom'@, we get the
-- following type, which shows that 'queryNode' can be directly used to
-- transform syntax trees (see also 'transformNode'):
--
-- > (forall b . (Signature b, a ~ DenResult b) => dom b -> Args (AST dom) b -> ASTF dom' a)
-- > -> ASTF dom a
-- > -> ASTF dom' a
queryNode :: forall dom c a
    .  (forall b . (Signature b, a ~ DenResult b) =>
           dom b -> Args (AST dom) b -> c (Full a))
    -> ASTF dom a
    -> c (Full a)
queryNode f a = query a Nil
  where
    query :: (a ~ DenResult b) => AST dom b -> Args (AST dom) b -> c (Full a)
    query (Sym a)  args = f a args
    query (c :$ a) args = query c (a :* args)

-- | A simpler version of 'queryNode'
--
-- This function can be used to create 'AST' traversal functions indexed by the
-- symbol types, for example:
--
-- > class Count subDomain
-- >   where
-- >     count' :: Count domain => subDomain a -> Args (AST domain) a -> Int
-- >
-- > instance (Count sub1, Count sub2) => Count (sub1 :+: sub2)
-- >   where
-- >     count' (InjL a) args = count' a args
-- >     count' (InjR a) args = count' a args
-- >
-- > count :: Count dom => ASTF dom a -> Int
-- > count = queryNodeSimple count'
--
-- Here, @count@ represents some static analysis on an 'AST'. Each constructor
-- in the tree will be queried by @count'@ indexed by the corresponding symbol
-- type. That way, @count'@ can be seen as an open-ended function on an open
-- data type. The @(Count domain)@ constraint on @count'@ is to allow recursion
-- over sub-trees.
--
-- Let's say we have a symbol
--
-- > data Add a
-- >   where
-- >     Add :: Add (Int :-> Int :-> Full Int)
--
-- Then the @Count@ instance for @Add@ might look as follows:
--
-- > instance Count Add
-- >   where
-- >     count' Add (a :* b :* Nil) = 1 + count a + count b
queryNodeSimple :: forall dom a c
    .  (forall b . (Signature b, a ~ DenResult b) =>
           dom b -> Args (AST dom) b -> c)
    -> ASTF dom a
    -> c
queryNodeSimple f a = unConst $ queryNode (\c -> Const . f c) a

-- | A version of 'queryNode' where the result is a transformed syntax tree,
-- wrapped in a type constructor @c@
transformNode :: forall dom dom' c a
    .  (  forall b . (Signature b, a ~ DenResult b)
       => dom b -> Args (AST dom) b -> c (ASTF dom' a)
       )
    -> ASTF dom a
    -> c (ASTF dom' a)
transformNode f a = unWrapAST $ queryNode (\a args -> WrapAST (f a args)) a



--------------------------------------------------------------------------------
-- * Restricted syntax trees
--------------------------------------------------------------------------------

-- | An abstract representation of a constraint on @a@. An instance might look
-- as follows:
--
-- > instance MyClass a => Sat MyContext a
-- >   where
-- >     data Witness MyContext a = MyClass a => MyWitness
-- >     witness = MyWitness
--
-- This allows us to use @(`Sat` MyContext a)@ instead of @(MyClass a)@. The
-- point with this is that @MyContext@ can be provided as a parameter, so this
-- effectively allows us to parameterize on class constraints. Note that the
-- existential context in the data definition is important. This means that,
-- given a constraint @(`Sat` MyContext a)@, we can always construct the context
-- @(MyClass a)@ by calling the 'witness' method (the class instance only
-- declares the reverse relationship).
--
-- This way of parameterizing over type classes was inspired by
-- /Restricted Data Types in Haskell/ (John Hughes, /Haskell Workshop/, 1999).
class Sat ctx a
  where
    data Witness ctx a
    witness :: Witness ctx a
  -- TODO Could probably use a one-parameter class instead, see
  --
  -- http://www.haskell.org/pipermail/glasgow-haskell-users/2011-December/021292.html
  --
  -- (but without the Super type family). Or even better, use ConstraintKinds.

witnessByProxy :: Sat ctx a => Proxy ctx -> Proxy a -> Witness ctx a
witnessByProxy _ _ = witness

-- | Witness of a @(`Sat` ctx a)@ constraint. This is different from
-- @(`Witness` ctx a)@, which witnesses the class encoded by @ctx@. 'Witness''
-- has a single constructor for all contexts, while 'Witness' has different
-- constructors for different contexts.
data SatWit ctx a
  where
    SatWit :: Sat ctx a => SatWit ctx a

fromSatWit :: SatWit ctx a -> Witness ctx a
fromSatWit SatWit = witness

-- | Expressions that act as witnesses of their result type
class WitnessSat expr
  where
    type SatContext expr
    witnessSat :: expr a -> SatWit (SatContext expr) (DenResult a)

-- | Expressions that act as witnesses of their result type
class MaybeWitnessSat ctx expr
  where
    maybeWitnessSat :: Proxy ctx -> expr a -> Maybe (SatWit ctx (DenResult a))

instance MaybeWitnessSat ctx dom => MaybeWitnessSat ctx (AST dom)
  where
    maybeWitnessSat ctx (Sym a)  = maybeWitnessSat ctx a
    maybeWitnessSat ctx (f :$ _) = maybeWitnessSat ctx f

instance (MaybeWitnessSat ctx sub1, MaybeWitnessSat ctx sub2) =>
    MaybeWitnessSat ctx (sub1 :+: sub2)
  where
    maybeWitnessSat ctx (InjL a) = maybeWitnessSat ctx a
    maybeWitnessSat ctx (InjR a) = maybeWitnessSat ctx a

-- | Convenient default implementation of 'maybeWitnessSat'
maybeWitnessSatDefault :: WitnessSat expr
    => Proxy (SatContext expr)
    -> expr a
    -> Maybe (SatWit (SatContext expr) (DenResult a))
maybeWitnessSatDefault _ = Just . witnessSat

-- | Type application for constraining the @ctx@ type of a parameterized symbol
withContext :: sym ctx a -> Proxy ctx -> sym ctx a
withContext = const

-- | Representation of a fully polymorphic constraint -- i.e. @(`Sat` `Poly` a)@
-- is satisfied by all types @a@.
data Poly

instance Sat Poly a
  where
    data Witness Poly a = PolyWit
    witness = PolyWit

poly :: Proxy Poly
poly = Proxy

-- | Representation of \"simple\" types: types satisfying
-- @(`Eq` a, `Show` a, `Typeable` a)@
data SimpleCtx

instance (Eq a, Show a, Typeable a) => Sat SimpleCtx a
  where
    data Witness SimpleCtx a = (Eq a, Show a, Typeable a) => SimpleWit
    witness = SimpleWit

simpleCtx :: Proxy SimpleCtx
simpleCtx = Proxy

