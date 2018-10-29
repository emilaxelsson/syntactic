{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Well-scoped terms

module Language.Syntactic.Functional.WellScoped where



import Control.Monad.Reader
import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Functional



-- | Environment extension
class Ext ext orig
  where
    -- | Remove the extension of an environment
    unext :: ext -> orig
    -- | Return the amount by which an environment has been extended
    diff :: Num a => Proxy ext -> Proxy orig -> a

instance {-# OVERLAPS #-} Ext env env
  where
    unext = id
    diff _ _ = 0

instance {-# OVERLAPS #-} (Ext env e, ext ~ (a,env)) => Ext ext e
  where
    unext = unext . snd
    diff m n = diff (fmap snd m) n + 1

-- | Lookup in an extended environment
lookEnv :: forall env a e . Ext env (a,e) => Proxy e -> Reader env a
lookEnv _ = reader $ \env -> let (a, _ :: e) = unext env in a

-- | Well-scoped variable binding
--
-- Well-scoped terms are introduced to be able to evaluate without type casting. The implementation
-- is inspired by \"Typing Dynamic Typing\" (Baars and Swierstra, ICFP 2002,
-- <http://doi.acm.org/10.1145/581478.581494>) where expressions are represented as (essentially)
-- @`Reader` env a@ after \"compilation\". However, a major difference is that
-- \"Typing Dynamic Typing\" starts from an untyped term, and thus needs (safe) dynamic type casting
-- during compilation. In contrast, the denotational semantics of 'BindingWS' (the 'Eval' instance)
-- uses no type casting.
data BindingWS sig
  where
    VarWS :: Ext env (a,e) => Proxy e -> BindingWS (Full (Reader env a))
    LamWS :: BindingWS (Reader (a,e) b :-> Full (Reader e (a -> b)))

instance Symbol BindingWS
  where
    symSig (VarWS _) = signature
    symSig LamWS     = signature

instance NFData1 BindingWS
  where
    rnf1 (VarWS Proxy) = ()
    rnf1 LamWS         = ()

instance Eval BindingWS
  where
    evalSym (VarWS p) = lookEnv p
    evalSym LamWS     = \f -> reader $ \e -> \a -> runReader f (a,e)

-- | Higher-order interface for well-scoped variable binding
--
-- Inspired by Conor McBride's "I am not a number, I am a classy hack"
-- (<http://mazzo.li/epilogue/index.html%3Fp=773.html>).
lamWS :: forall a e sym b . (BindingWS :<: sym)
    => ((forall env . (Ext env (a,e)) => ASTF sym (Reader env a)) -> ASTF sym (Reader (a,e) b))
    -> ASTF sym (Reader e (a -> b))
lamWS f = smartSym LamWS $ f $ smartSym (VarWS (Proxy :: Proxy e))

-- | Evaluation of open well-scoped terms
evalOpenWS :: Eval s => env -> ASTF s (Reader env a) -> a
evalOpenWS e = ($ e) . runReader . evalDen

-- | Evaluation of closed well-scoped terms
evalClosedWS :: Eval s => ASTF s (Reader () a) -> a
evalClosedWS = evalOpenWS ()

-- | Mapping from a symbol signature
--
-- > a :-> b :-> Full c
--
-- to
--
-- > Reader env a :-> Reader env b :-> Full (Reader env c)
type family   LiftReader env sig
type instance LiftReader env (Full a)    = Full (Reader env a)
type instance LiftReader env (a :-> sig) = Reader env a :-> LiftReader env sig

type family UnReader a
type instance UnReader (Reader e a) = a

-- | Mapping from a symbol signature
--
-- > Reader e a :-> Reader e b :-> Full (Reader e c)
--
-- to
--
-- > a :-> b :-> Full c
type family   LowerReader sig
type instance LowerReader (Full a)    = Full (UnReader a)
type instance LowerReader (a :-> sig) = UnReader a :-> LowerReader sig

-- | Wrap a symbol to give it a 'LiftReader' signature
data ReaderSym sym sig
  where
    ReaderSym
        :: ( Signature sig
           , Denotation (LiftReader env sig) ~ DenotationM (Reader env) sig
           , LowerReader (LiftReader env sig) ~ sig
           )
        => Proxy env
        -> sym sig
        -> ReaderSym sym (LiftReader env sig)

instance Eval sym => Eval (ReaderSym sym)
  where
    evalSym (ReaderSym (_ :: Proxy env) s) = liftDenotationM signature p s $ evalSym s
      where
        p = Proxy :: Proxy (Reader env)

-- | Well-scoped 'AST'
type WS sym env a = ASTF (BindingWS :+: ReaderSym sym) (Reader env a)

-- | Convert the representation of variables and binders from 'BindingWS' to 'Binding'. The latter
-- is easier to analyze, has a 'Render' instance, etc.
fromWS :: WS sym env a -> ASTF (Binding :+: sym) a
fromWS = fromDeBruijn . go
  where
    go :: AST (BindingWS :+: ReaderSym sym) sig -> AST (Binding :+: sym) (LowerReader sig)
    go (Sym (InjL s@(VarWS p)))     = Sym (InjL (Var (diff (mkProxy2 s) (mkProxy1 s p))))
      where
        mkProxy1 = (\_ _ -> Proxy) :: BindingWS (Full (Reader e' a)) -> Proxy e -> Proxy (a,e)
        mkProxy2 = (\_ -> Proxy)   :: BindingWS (Full (Reader e' a)) -> Proxy e'
    go (Sym (InjL LamWS))           = Sym $ InjL $ Lam (-1) -- -1 since we're using De Bruijn
    go (s :$ a)                     = go s :$ go a
    go (Sym (InjR (ReaderSym _ s))) = Sym $ InjR s

-- | Make a smart constructor for well-scoped terms. 'smartWS' has any type of the form:
--
-- > smartWS :: (sub :<: sup, bsym ~ (BindingWS :+: ReaderSym sup))
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> ASTF bsym (Reader env a) -> ASTF bsym (Reader env b) -> ... -> ASTF bsym (Reader env x)
smartWS :: forall sig sig' bsym f sub sup env a
    .  ( Signature sig
       , Signature sig'
       , sub :<: sup
       , bsym ~ (BindingWS :+: ReaderSym sup)
       , f    ~ SmartFun bsym sig'
       , sig' ~ SmartSig f
       , bsym ~ SmartSym f
       , sig' ~ LiftReader env sig
       , Denotation (LiftReader env sig) ~ DenotationM (Reader env) sig
       , LowerReader (LiftReader env sig) ~ sig
       , Reader env a ~ DenResult sig'
       )
    => sub sig -> f
smartWS s = smartSym' $ InjR $ ReaderSym (Proxy :: Proxy env) $ inj s

