{-# OPTIONS_GHC -fcontext-stack=25 #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Imperative.Compiler where



import Prelude as P

import Control.Monad.State

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.SimpleCodeMotion

import MuFeldspar.Core
import Imperative.Imperative



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

type Result = Ident

ident :: String -> VarId -> Ident
ident base i = base ++ show i

freshVar :: State VarId String
freshVar = do
    v <- get; put (v+1)
    return (ident "x" v)

viewInfix :: String -> Maybe String
viewInfix name
    | head name P.== '(' && last name P.== ')' = Just (tail $ init name)
    | otherwise = Nothing

projLambda :: (Lambda Poly :<: dom) => AST dom a -> Maybe VarId
projLambda = liftM getVar . project
  where
    getVar :: Lambda Poly a -> VarId
    getVar (Lambda var) = var



--------------------------------------------------------------------------------
-- * Generic machinery
--------------------------------------------------------------------------------

class Compile sub dom
  where
    compileSym :: sub a -> Result -> HList (AST dom) a -> State VarId Prog

instance (Compile sub1 dom, Compile sub2 dom) => Compile (sub1 :+: sub2) dom
  where
    compileSym (InjectL a) = compileSym a
    compileSym (InjectR a) = compileSym a

compileM :: Compile dom dom => Result -> ASTF dom a -> State VarId Prog
compileM result = queryNodeSimple (flip compileSym result)

compileFresh :: Compile dom dom => ASTF dom a -> State VarId (Result,Prog)
compileFresh arg = do
    var  <- freshVar
    prog <- compileM var arg
    return (var,prog)

compileTop :: (Compile dom dom, Lambda Poly :<: dom) =>
    [Ident] -> ASTF dom a -> Main
compileTop params ((projLambda -> Just inp) :$: body) =
    compileTop (ident "v" inp:params) body
compileTop params a = Main (reverse params) prog
  where
    prog = flip evalState 0 $ compileM "out" a

compile :: Syntactic a FeldDomainAll => a -> Main
compile = compileTop [] . reifySmart poly



instance Compile dom dom => Compile (Sym ctx) dom
  where
    compileSym (Sym name _) result args = do
        (varArgs,progs) <- liftM unzip $ listHListM compileFresh args
        return $ concat progs ++ [result := expr varArgs]
      where
        expr [a,b]
            | Just op <- viewInfix name = Op op (Var a) (Var b)
        expr args                       = App name (map Var args)

compileSymb :: (IsSymbol expr, Compile dom dom) =>
    expr a -> Result -> HList (AST dom) a -> State VarId Prog
compileSymb = compileSym . toSym



--------------------------------------------------------------------------------
-- * Compilation of sub-domains
--------------------------------------------------------------------------------

instance Compile (Variable Poly) dom
  where
    compileSym (Variable i) result _ = return [result := Var (ident "v" i)]

instance Compile (Lambda Poly) dom
  where
    compileSym = error "Can only compile top-level Lambda"

instance Compile (Literal Poly) dom
  where
    compileSym (Literal a) result _ = return [result := Lit (show a)]

instance Compile dom dom => Compile NUM dom        where compileSym = compileSymb
instance Compile dom dom => Compile INTEGRAL dom   where compileSym = compileSymb
instance Compile dom dom => Compile FRACTIONAL dom where compileSym = compileSymb
instance Compile dom dom => Compile Conversion dom where compileSym = compileSymb
instance Compile dom dom => Compile COMPLEX dom    where compileSym = compileSymb
instance Compile dom dom => Compile BITS dom       where compileSym = compileSymb
instance Compile dom dom => Compile Logic dom      where compileSym = compileSymb
instance Compile dom dom => Compile ORD dom        where compileSym = compileSymb
instance Compile dom dom => Compile Array dom      where compileSym = compileSymb

instance Compile dom dom => Compile (Condition Poly) dom
  where
    compileSym Condition result (cond :*: tHEN :*: eLSE :*: Nil) = do
        (condVar,condProg) <- compileFresh cond
        thenProg           <- compileM result tHEN
        elseProg           <- compileM result eLSE
        return $ condProg ++ [Cond (Var condVar) thenProg elseProg]

instance Compile dom dom => Compile (Tuple Poly) dom  where compileSym = compileSymb
instance Compile dom dom => Compile (Select Poly) dom where compileSym = compileSymb

instance (Compile dom dom, Lambda Poly :<: dom) => Compile (Let Poly Poly) dom
  where
    compileSym Let result (a :*: ((projLambda -> Just var) :$: body) :*: Nil) =
        liftM2 (++)
          (compileM (ident "v" var) a)
          (compileM result body)

instance (Compile dom dom, Lambda Poly :<: dom) => Compile Parallel dom
  where
    compileSym par@Parallel result (len :*: (lamIx :$: body) :*: Nil)
        | Just ix <- projLambda lamIx
        = do (lenVar,lenProg)   <- compileFresh len
             (elemVar,bodyProg) <- compileFresh body
             let ixVar          =  ident "v" ix
                 emptyProg      =  result := Lit "[]"
                 assignProg     =  result := App "updateArr" [Var result, Var ixVar, Var elemVar]
             let fullBody       =  bodyProg ++ [assignProg]
             return
               $  lenProg
               ++ [emptyProg, For True (Var lenVar) ixVar fullBody]

instance (Compile dom dom, Lambda Poly :<: dom) => Compile Sequential dom
  where
    compileSym seq@Sequential result (len :*: init :*: (lamIx :$: (lamSt :$: body)) :*: Nil)
        | Just ix <- projLambda lamIx
        , Just st <- projLambda lamSt
        = do (lenVar,lenProg)   <- compileFresh len
             let ixVar          =  ident "v" ix
                 stVar          =  ident "v" st
             initProg           <- compileM stVar init
             (bodyVar,bodyProg) <- compileFresh body
             elemVar            <- freshVar
             let fstProg        =  elemVar := App "sel1" [Var bodyVar]
                 sndProg        =  stVar   := App "sel2" [Var bodyVar]
                 emptyProg      =  result  := Lit "[]"
                 assignProg     =  result  := App "setIx" [Var result, Var ixVar, Var elemVar]
             let fullBody       =  bodyProg ++ [fstProg,sndProg,assignProg]
             return
               $  lenProg
               ++ initProg
               ++ [emptyProg, For False (Var lenVar) ixVar fullBody]

instance (Compile dom dom, Lambda Poly :<: dom) => Compile ForLoop dom
  where
    compileSym ForLoop result (len :*: init :*: (lamIx :$: (lamSt :$: body)) :*: Nil)
        | Just ix <- projLambda lamIx
        , Just st <- projLambda lamSt
        = do (lenVar,lenProg) <- compileFresh len
             let ixVar        =  ident "v" ix
                 stVar        =  ident "v" st
             initProg         <- compileM stVar init
             bodyProg         <- compileM stVar body
             return
               $  lenProg
               ++ initProg
               ++ [For False (Var lenVar) ixVar bodyProg, result := Var stVar]

