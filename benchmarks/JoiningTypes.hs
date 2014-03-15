{-# LANGUAGE GADTs, TypeOperators, TemplateHaskell #-}
module JoiningTypes (main) where

import Criterion.Main
import Data.Syntactic


-- Comparing one type vs joined types
data Expr1 t where
  EI    :: Int  -> Expr1 (Full Int)
  EB    :: Bool -> Expr1 (Full Bool)
  EAdd  :: Expr1 (Int :-> Int :-> Full Int)
  EEq   :: (Eq t) => Expr1 (t   :-> t   :-> Full Bool)
  EIf   :: Expr1 (Bool :-> a :-> a :-> Full a)

type Expr1' a = AST Expr1 (Full a)

int  :: Int -> Expr1' Int
int = Sym . EI

bool :: Bool -> Expr1' Bool
bool = Sym . EB

add  :: Expr1' Int -> Expr1' Int -> Expr1' Int
add a b = Sym EAdd :$ a :$ b

eq   :: (Eq a) => Expr1' a -> Expr1' a -> Expr1' Bool
eq a b = Sym EEq :$ a :$ b

if'  :: Expr1' Bool -> Expr1' a -> Expr1' a -> Expr1' a
if' c a b = Sym EIf :$ c :$ a :$ b

instance Semantic Expr1 where
  semantics (EI n)  = Sem "EI" n
  semantics (EB b)  = Sem "EB" b
  semantics (EAdd)  = Sem "EAdd" (+)
  semantics (EEq)   = Sem "EEq"  (==)
  semantics (EIf)   = Sem "EIf" (\c a b -> if c then a else b)

semanticInstances ''Expr1

-- Joined types
data ExprI t where
  EIJ    :: Int  -> ExprI (Full Int)
  EAddJ  :: ExprI (Int :-> Int :-> Full Int)

data ExprB t where
  EBJ    :: Bool -> ExprB (Full Bool)
  EEqJ   :: (Eq t) => ExprB (t   :-> t   :-> Full Bool)
  EIfJ   :: ExprB (Bool :-> a :-> a :-> Full a)

type ExprJ = ExprI :+: ExprB
type ExprJ' a = AST ExprJ (Full a)

intJ  :: Int -> ExprJ' Int
intJ = Sym . inj . EIJ

boolJ :: Bool -> ExprJ' Bool
boolJ = Sym . inj . EBJ

addJ  :: ExprJ' Int -> ExprJ' Int -> ExprJ' Int
addJ a b = Sym (inj EAddJ) :$ a :$ b

eqJ   :: (Eq a) => ExprJ' a -> ExprJ' a -> ExprJ' Bool
eqJ a b = Sym (inj EEqJ) :$ a :$ b

ifJ  :: ExprJ' Bool -> ExprJ' a -> ExprJ' a -> ExprJ' a
ifJ c a b = Sym (inj EIfJ) :$ c :$ a :$ b

instance Semantic ExprI where
  semantics (EIJ n)  = Sem "EI" n
  semantics (EAddJ)  = Sem "EAdd" (+)
instance Semantic ExprB where
  semantics (EBJ b)  = Sem "EB" b
  semantics (EEqJ)   = Sem "EEq"  (==)
  semantics (EIfJ)   = Sem "EIf" (\c a b -> if c then a else b)

semanticInstances ''ExprI
semanticInstances ''ExprB

-- Joined types (4 joins)

data Expr4J1 t where
  E4JI    :: Int  -> Expr4J1 (Full Int)
data Expr4J2 t where
  E4JB    :: Bool -> Expr4J2 (Full Bool)
data Expr4J3 t where
  E4JAdd  :: Expr4J3 (Int :-> Int :-> Full Int)
data Expr4J4 t where
  E4JEq   :: (Eq t) => Expr4J4 (t   :-> t   :-> Full Bool)
data Expr4J5 t where  
  E4JIf   :: Expr4J5 (Bool :-> a :-> a :-> Full a)

type Expr4J = Expr4J1 :+: Expr4J2 :+: Expr4J3 :+: Expr4J4 :+: Expr4J5
type Expr4J' a = AST Expr4J (Full a)

int4  :: Int -> Expr4J' Int
int4 = Sym . inj . E4JI

bool4 :: Bool -> Expr4J' Bool
bool4 = Sym . inj . E4JB

add4  :: Expr4J' Int -> Expr4J' Int -> Expr4J' Int
add4 a b = Sym (inj E4JAdd) :$ a :$ b

eq4   :: (Eq a) => Expr4J' a -> Expr4J' a -> Expr4J' Bool
eq4 a b = Sym (inj E4JEq) :$ a :$ b

if4  :: Expr4J' Bool -> Expr4J' a -> Expr4J' a -> Expr4J' a
if4 c a b = Sym (inj E4JIf) :$ c :$ a :$ b

instance Semantic Expr4J1 where
  semantics (E4JI n)  = Sem "EI" n

instance Semantic Expr4J2 where
  semantics (E4JB b)  = Sem "EB" b
  
instance Semantic Expr4J3 where
  semantics (E4JAdd)  = Sem "EAdd" (+)
  
instance Semantic Expr4J4 where
  semantics (E4JEq)   = Sem "EEq"  (==)
  
instance Semantic Expr4J5 where
  semantics (E4JIf)   = Sem "EIf" (\c a b -> if c then a else b)

semanticInstances ''Expr4J1
semanticInstances ''Expr4J2
semanticInstances ''Expr4J3
semanticInstances ''Expr4J4
semanticInstances ''Expr4J5

-- Expressions
syntacticExpr :: Int -> Expr1' Int
syntacticExpr 0 = if' (eq (int 5) (int 4)) (int 5) (int 0) 
syntacticExpr n = (add (syntacticExpr (n-1)) (syntacticExpr (n-1))) 

syntacticExprJ :: Int -> ExprJ' Int
syntacticExprJ 0 = ifJ (eqJ (intJ 5) (intJ 4)) (intJ 5) (intJ 0) 
syntacticExprJ n = (addJ (syntacticExprJ (n-1)) (syntacticExprJ (n-1))) 

syntacticExpr4J :: Int -> Expr4J' Int
syntacticExpr4J 0 = if4 (eq4 (int4 5) (int4 4)) (int4 5) (int4 0) 
syntacticExpr4J n = (add4 (syntacticExpr4J (n-1)) (syntacticExpr4J (n-1))) 

main = defaultMain [bgroup "eval 10" [ bench "syntactic 0 joins"   $ nf evaluate (syntacticExpr 10)
                                     , bench "syntactic 1 join"  $ nf evaluate (syntacticExprJ 10)
                                     , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 10)]
                   , bgroup "eval 15" [ bench "syntactic 0 joins"      $ nf evaluate (syntacticExpr 15) 
                                      , bench "syntactic 1 join" $ nf evaluate (syntacticExprJ 15) 
                                      , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 15)]
                   , bgroup "eval 20" [ bench "syntactic 0 joins"      $ nf evaluate (syntacticExpr 20)
                                      , bench "syntactic 1 join" $ nf evaluate (syntacticExprJ 20) 
                                      , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 20)]
                   , bgroup "size 10" [ bench "syntactic 0 joins"       $ nf size (syntacticExpr 10)
                                      , bench "syntactic 1 join"  $ nf size (syntacticExprJ 10)
                                      , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 10)]
                   , bgroup "size 15" [ bench "syntactic 0 joins"      $ nf size (syntacticExpr 15) 
                                      , bench "syntactic 1 join" $ nf size (syntacticExprJ 15)
                                      , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 15)]
                   , bgroup "size 20" [ bench "syntactic 0 joins"      $ nf size (syntacticExpr 20)
                                      , bench "syntactic 1 join" $ nf size (syntacticExprJ 20)
                                      , bench "syntactic 4 joins" $ nf evaluate (syntacticExpr4J 20)]]
