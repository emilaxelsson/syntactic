module Imperative.Imperative where



import Data.List



type Ident = String

data Expr
    = Lit String           -- Literal
    | Var Ident            -- Variable
    | App String [Expr]    -- Function call
    | Op String Expr Expr  -- Binary operator

type IsPar = Bool  --  Parallel or sequential loop?

data Stmt
    = Nop                        -- No-op
    | Ident := Expr              -- Assignment
    | Cond Expr Prog Prog        -- Conditional
    | For IsPar Expr Ident Prog  -- For loop

type Prog = [Stmt]

data Main = Main
    { mainInp  :: [Ident]
    , mainBody :: Prog
    }

instance Show Main
  where
    show = renderMain



paren :: String -> String
paren = ("(" ++) . (++ ")")

-- | Like 'unlines', but without the final newline
unLines :: [String] -> String
unLines = concat . intersperse "\n"

indent :: Int -> String -> String
indent n = unLines . map move . lines
  where
    move = (replicate n ' ' ++)

renderExpr :: Expr -> String
renderExpr (Lit a)        = a
renderExpr (Var ident)    = ident
renderExpr (App str args) = paren $ unwords (str : map renderExpr args)
renderExpr (Op str a b)   = paren $ unwords [renderExpr a, str, renderExpr b]

mkNop :: Prog -> Prog
mkNop []   = [Nop]
mkNop prog = prog

renderStmt :: Stmt -> String
renderStmt Nop             = "nop"
renderStmt (ident := expr) = ident ++ " := " ++ renderExpr expr
renderStmt (Cond cond tHEN eLSE)
    | isSmall =
        ("if " ++ renderExpr cond ++ " then " ++ tRend ++ " else " ++ eRend)
    | otherwise =
        ("\nif " ++ renderExpr cond ++ " then\n")
          ++
        indent 2 tRend
          ++
        "\nelse\n"
          ++
        indent 2 eRend
  where
    t       = mkNop tHEN
    e       = mkNop eLSE
    tRend   = renderProg t
    eRend   = renderProg e
    isSmall = length (lines tRend) <= 1 && length (lines eRend) <= 1
renderStmt (For isPar len index body) =
    (loop ++ index ++ " in 0 .. (" ++ renderExpr len ++ "-1) do\n")
      ++
    indent 2 (renderProg body)
  where
    loop = if isPar then "\npar " else "\nfor "

renderProg :: Prog -> String
renderProg = unLines . map renderStmt

renderMain :: Main -> String
renderMain (Main params prog) =
    ("main (" ++ concat (intersperse "," params) ++ ")\n")
      ++
    indent 2 (renderProg prog)

printMain :: Main -> IO ()
printMain = putStrLn . (++"\n") . renderMain

