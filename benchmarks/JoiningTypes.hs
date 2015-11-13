module JoiningTypes (main) where

import Criterion.Main
import Criterion.Types
import Language.Syntactic
import Language.Syntactic.Functional

-- Normal DSL, not joined types.
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

instance Render Expr1 where
  renderSym (EI n)  = "EI"
  renderSym (EB b)  = "EB"
  renderSym (EAdd)  = "EAdd"
  renderSym (EEq)   = "EEq"
  renderSym (EIf)   = "EIf"

instance Equality   Expr1
instance StringTree Expr1

instance Eval Expr1 where
  evalSym (EI n)  = n
  evalSym (EB b)  = b
  evalSym EAdd    = (+)
  evalSym EEq     = (==)
  evalSym EIf     = \c a b -> if c then a else b

instance EvalEnv Expr1 env where
  compileSym p (EI n) = compileSymDefault signature p (EI n)
  compileSym p (EB b) = compileSymDefault signature p (EB b)
  compileSym p EAdd   = compileSymDefault signature p EAdd
  compileSym p EEq    = compileSymDefault signature p EEq
  compileSym p EIf    = compileSymDefault signature p EIf

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

instance Render ExprI where
  renderSym (EIJ n)  = "EI"
  renderSym (EAddJ)  = "EAdd"
instance Render ExprB where
  renderSym (EBJ b)  = "EB"
  renderSym (EEqJ)   = "EEq"
  renderSym (EIfJ)   = "EIf"

instance Equality   ExprI
instance StringTree ExprI
instance Equality   ExprB
instance StringTree ExprB

instance Eval ExprI where
  evalSym (EIJ n) = n
  evalSym EAddJ   = (+)

instance Eval ExprB where
  evalSym (EBJ b) = b
  evalSym EEqJ    = (==)
  evalSym EIfJ    = \c a b -> if c then a else b

instance EvalEnv ExprI env where
  compileSym p (EIJ n) = compileSymDefault signature p (EIJ n)
  compileSym p EAddJ   = compileSymDefault signature p EAddJ

instance EvalEnv ExprB env where
  compileSym p (EBJ b) = compileSymDefault signature p (EBJ b)
  compileSym p EEqJ    = compileSymDefault signature p EEqJ
  compileSym p EIfJ    = compileSymDefault signature p EIfJ

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

instance Render Expr4J1 where
  renderSym (E4JI n)  = "EI"

instance Render Expr4J2 where
  renderSym (E4JB b)  = "EB"

instance Render Expr4J3 where
  renderSym (E4JAdd)  = "EAdd"

instance Render Expr4J4 where
  renderSym (E4JEq)   = "EEq"

instance Render Expr4J5 where
  renderSym (E4JIf)   = "EIf"

instance Equality   Expr4J1
instance StringTree Expr4J1
instance Equality   Expr4J2
instance StringTree Expr4J2
instance Equality   Expr4J3
instance StringTree Expr4J3
instance Equality   Expr4J5
instance StringTree Expr4J5

instance Eval Expr4J1 where
  evalSym (E4JI n)  = n

instance Eval Expr4J2 where
  evalSym (E4JB b)  = b

instance Eval Expr4J3 where
  evalSym E4JAdd    = (+)

instance Eval Expr4J4 where
  evalSym E4JEq     = (==)

instance Eval Expr4J5 where
  evalSym E4JIf     = \c a b -> if c then a else b

instance EvalEnv Expr4J1 env where
  compileSym p (E4JI n)  = compileSymDefault signature p (E4JI n)

instance EvalEnv Expr4J2 env where
  compileSym p (E4JB b)  = compileSymDefault signature p (E4JB b)

instance EvalEnv Expr4J3 env where
  compileSym p E4JAdd    = compileSymDefault signature p E4JAdd

instance EvalEnv Expr4J4 env where
  compileSym p E4JEq     = compileSymDefault signature p E4JEq

instance EvalEnv Expr4J5 env where
  compileSym p E4JIf     = compileSymDefault signature p E4JIf

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

main :: IO ()
main = defaultMainWith (defaultConfig {csvFile = Just "bench-results/joiningTypes.csv"})
         [ bgroup "eval 10" [ bench "syntactic 0 joins" $ nf evalDen (syntacticExpr 10)
                            , bench "syntactic 1 join"  $ nf evalDen (syntacticExprJ 10)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 10)]
         , bgroup "eval 15" [ bench "syntactic 0 joins" $ nf evalDen (syntacticExpr 15)
                            , bench "syntactic 1 join"  $ nf evalDen (syntacticExprJ 15)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 15)]
         , bgroup "eval 20" [ bench "syntactic 0 joins" $ nf evalDen (syntacticExpr 20)
                            , bench "syntactic 1 join"  $ nf evalDen (syntacticExprJ 20)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 20)]
         , bgroup "size 10" [ bench "syntactic 0 joins" $ nf size (syntacticExpr 10)
                            , bench "syntactic 1 join"  $ nf size (syntacticExprJ 10)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 10)]
         , bgroup "size 15" [ bench "syntactic 0 joins" $ nf size (syntacticExpr 15)
                            , bench "syntactic 1 join"  $ nf size (syntacticExprJ 15)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 15)]
         , bgroup "size 20" [ bench "syntactic 0 joins" $ nf size (syntacticExpr 20)
                            , bench "syntactic 1 join"  $ nf size (syntacticExprJ 20)
                            , bench "syntactic 4 joins" $ nf evalDen (syntacticExpr4J 20)]]

