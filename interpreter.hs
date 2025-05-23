module Interpreter where

import Types
import Helpers
import Evaluation
import TypeChecking

-- Interpreter
i2c :: Int -> Term
i2c 0 = TmZero
i2c n = TmSucc (i2c (n - 1))

c2i :: Term -> Int
c2i TmZero = 0
c2i (TmSucc t) = 1 + c2i t
c2i _ = error "Not a numeric value"


s2t_var :: String
s2t_var = ['0'..'9']

s2t_lam :: String
-- s2t_lam = "\\."
s2t_lam = "\\"

s2t_sym :: String
s2t_sym = "()="

s2t_idt :: String
s2t_idt = ['a' .. 'z'] ++ ['0'..'9']

nonIdentifiers :: [String]
nonIdentifiers = ["true", "false", "zero", "succ", "plus", "if", "eq", "and", "or", "not", "iszero", "lt", "mul"]

stringToType :: String -> Ty
stringToType "bool" = TyBool
stringToType "nat" = TyNat
stringToType _ = TyAny

typeToString :: Ty -> String
typeToString TyBool = "bool"
typeToString TyNat = "nat"
typeToString TyAny = "any"

t2s (TmVar x) = show x
t2s (TmLam var ty t) = s2t_lam ++ var ++ ": " ++ typeToString ty ++ "." ++ t2s t
t2s (TmApp s t@(TmApp _ _)) = t2s s ++ " (" ++ t2s t ++ ")"
t2s (TmApp s t@(TmLam {})) = t2s s ++ " (" ++ t2s t ++ ")"
t2s (TmApp s@(TmLam {}) t) = "(" ++ t2s s ++ ") " ++ t2s t
t2s (TmApp s t) = t2s s ++ " " ++ t2s t
t2s s@(TmSucc t) = "c" ++ show (c2i s)
t2s p@(TmPred t) = "c" ++ show (c2i p)
t2s TmZero = "zero"
t2s TmTrue = "true"
t2s TmFalse = "false"
t2s (TmPlus s t) = "plus " ++ t2s s ++ " " ++ t2s t
t2s (TmEq s t) = "eq " ++ t2s s ++ " " ++ t2s t

s2t_static_mem :: [(String, Term)]
s2t_static_mem = 
       [
        -- TODO: Add here predefined terms if needed
       ]
       ++ [('c' : show i, i2c i) | i <- [0 .. 1000]]

s2t_set_mem :: [(String, Term)] -> String -> Term -> [(String, Term)]
s2t_set_mem (p@(a, b) : m) s t = 
  if a == s then (a, t) : m else p : s2t_set_mem m s t
s2t_set_mem [] s t = [(s, t)] 

s2t_get_mem :: [(String, Term)] -> String -> [Term]
s2t_get_mem ((a, b) : m) s = 
  if a == s then [b] else s2t_get_mem m s
s2t_get_mem [] _ = []


s2t_read_var :: String -> (String, String)
s2t_read_var s = f ("", s)
  where f (t, s@(c : cs)) = if c `elem` s2t_var then f (c : t, cs) else (reverse t, s)
        f (t, "") = (reverse t, "")

s2t_read_lam :: String -> (String, String)
s2t_read_lam s
  | h == s2t_lam = let (a, b) = span (/= '.') (drop l s)
                   in (h ++ a ++ ".", drop 1 b)
  | otherwise = ("", s)
  where h = take l s
        l = length s2t_lam

extractVarAndType :: String -> (String, String)
extractVarAndType s = (a, dropWhile (== ' ') $ drop 1 b)
  where (a, b) = span (/= ':') c
        c = init (drop 1 s)


s2t_read_idt :: String -> (String, String)
s2t_read_idt s = f ("", s)
  where f (t, s@(c : cs)) = if c `elem` s2t_idt then f (c : t, cs) else (reverse t, s)
        f (t, "") = (reverse t, "")


s2t_tokenize :: String -> [(String, String)] -> [(String, String)]
s2t_tokenize s@(c : cs) t
  | c == ' ' = s2t_tokenize cs t
  | c `elem` s2t_var = if v == [] then [] else s2t_tokenize vs ((v, "var") : t)
  | c == head s2t_lam = if l == [] then [] else s2t_tokenize ls ((l, "lam") : t)
  | c `elem` s2t_sym = s2t_tokenize cs (([c], "sym") : t)
  | c `elem` s2t_idt =
      let (i, is) = s2t_read_idt s
      in if i `elem` nonIdentifiers
         then s2t_tokenize is ((i, i) : t)  -- label the term with its own name
         else s2t_tokenize is ((i, "idt") : t)
  | otherwise = []
  where (v, vs) = s2t_read_var s
        (l, ls) = s2t_read_lam s
s2t_tokenize "" t = reverse t

s2t_interpret_var :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_var m ((n, "var") : s) = 
  if all (`elem` s2t_var) n then ([TmVar (read n :: Int)], s) else ([], [])

-- Pomocna tail-rekurzivna funkcija, interpretira term oblika
--      term*
s2t_interpret_lst :: [(String, Term)] -> [(String, String)] -> [Term] -> ([Term], [(String, String)])
s2t_interpret_lst m s@((")", "sym") : _) l = (reverse l, s)
s2t_interpret_lst m [] l = (reverse l, [])
s2t_interpret_lst m s l = if t' == [] then ([], []) else s2t_interpret_lst m s' (t' ++ l)
  where (t', s') = s2t_interpret_term m s

-- Interpretira term oblika kao niz lijevo asocijativnih primjena terma App
--      "(" + term* + ")"
s2t_interpret_grp :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_grp m (("(", "sym") : s)
  | l == [] || s' == [] = ([], [])
  | head s' == (")", "sym") = ([foldl (\a e -> TmApp a e) (head l) (tail l)], tail s')
  | otherwise = ([], [])
  where (l, s') = s2t_interpret_lst m s []

-- Interpretira term oblika:
--      "\." + term*
s2t_interpret_lam :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_lam m ((lamDef, "lam") : s)
  -- NOTE: TyAny is for testing purposes only, remove it later
  | l /= [] = ([TmLam varName varType (foldl (\a e -> TmApp a e) (head l) (tail l))], s')
  | otherwise = ([], [])
  where (l, s') = s2t_interpret_lst m s []
        (varName, typeName) = extractVarAndType lamDef
        varType = stringToType typeName

-- Interpretira term oblika
--      (znak iz s2t_idt)*
-- koji mora postojati u memoriji
s2t_interpret_idt :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_idt m ((i, "idt") : s) = if t == [] then ([], []) else (t, s)
  where t = s2t_get_mem m i

s2t_interpret_true :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_true m (("true", "true") : s) = ([TmTrue], s)

s2t_interpret_false :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_false m (("false", "false") : s) = ([TmFalse], s)

s2t_interpret_zero :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_zero m (("zero", "zero") : s) = ([TmZero], s)

s2t_interpret_succ :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_succ m (("succ", "succ") : s) =
  case s2t_interpret_term m s of
    ([t], s') -> ([TmSucc t], s')
    _ -> ([], [])

s2t_interpret_plus :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_plus m (("plus", "plus") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmPlus t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_mul :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_mul m (("mul", "mul") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmMul t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_eq :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_eq m (("eq", "eq") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmEq t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_if :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_if m (("if", "if") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) ->
          case s2t_interpret_term m s2 of
            ([t3], s3) -> ([TmIf t1 t2 t3], s3)
            _ -> ([], [])
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_and :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_and m (("and", "and") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmAnd t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_or :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_or m (("or", "or") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmOr t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_not :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_not m (("not", "not") : s) =
  case s2t_interpret_term m s of
    ([t], s') -> ([TmNot t], s')
    _ -> ([], [])

s2t_interpret_iszero :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_iszero m (("iszero", "iszero") : s) =
  case s2t_interpret_term m s of
    ([t], s') -> ([TmIsZero t], s')
    _ -> ([], [])

s2t_interpret_lt :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_lt m (("lt", "lt") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmLt t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

s2t_interpret_term :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_term m s@((a, b) : _)
  | a == "(" && b == "sym" = s2t_interpret_grp m s
  | b == "var" = s2t_interpret_var m s
  | b == "lam" = s2t_interpret_lam m s
  | b == "idt" = s2t_interpret_idt m s
  | b == "true" = s2t_interpret_true m s
  | b == "false" = s2t_interpret_false m s
  | b == "zero" = s2t_interpret_zero m s
  | b == "succ" = s2t_interpret_succ m s
  | b == "plus" = s2t_interpret_plus m s
  | b == "mul" = s2t_interpret_mul m s
  | b == "eq" = s2t_interpret_eq m s
  | b == "if" = s2t_interpret_if m s
  | b == "and" = s2t_interpret_and m s
  | b == "or" = s2t_interpret_or m s
  | b == "not" = s2t_interpret_not m s
  | b == "iszero" = s2t_interpret_iszero m s
  | b == "lt" = s2t_interpret_lt m s
  | otherwise = ([], [])

s2t_interpret_assign :: [(String, Term)] -> [(String, String)] -> [(String, Term)]
s2t_interpret_assign m ((a, "idt") : ("=", "sym") : t) = 
  if l == [] || s /= [] then [] else s2t_set_mem m a (head l)
  where (l, s) = s2t_interpret_term m (("(", "sym") : t ++ [(")", "sym")])

s2t_interpreter :: [(String, Term)] -> (Term -> String) -> IO ()
s2t_interpreter m f =
  do putStr ">> "
     l <- getLine
     if l == [] then do
       s2t_interpreter m f
     else if l == "-h" || l == "-help" then do
       putStr "Commands:\n"
       putStr "-lambda: lambda notation\n"
       putStr "-int: integer notation\n"
       putStr "-raw: raw output\n"
       putStr "-exit: shut down the interpreter\n"
       putStr "-clear: clear screen\n"
       s2t_interpreter m f
     else if l == "-lambda" then do
       putStr "Setting lambda notation.\n"
       s2t_interpreter m t2s
     else if l == "-int" then do
       putStr "Setting integer notation.\n"
       s2t_interpreter m (\x -> let n = c2i x in if n == -1 then "NaN" else 'c' : show n)
     else if l == "-raw" then do
       putStr "Switching to raw output.\n"
       s2t_interpreter m (\x -> show x)
     else if l == "-exit" then do
       putStr "The end.\n"
       return ()
     else if l == "-clear" then do
       putStr $ replicate 72 '\n'
       s2t_interpreter m f
     else if head l == '-' then do
       putStr $ "Unrecognized command.\n"
       s2t_interpreter m f
     else do
       let s = s2t_tokenize (dbruj [] [] l) []
       if s == [] then do
         putStr "Invalid input.\n"
         s2t_interpreter m f
       else if ("=", "sym") `elem` s then do
         let n = s2t_interpret_assign m s
         if n == [] then do
           putStr "Invalid input.\n"
           s2t_interpreter m f
         else do
           putStr $ (fst . head) s ++ " defined.\n"
           s2t_interpreter n f
       else do
         let (t, r) = s2t_interpret_term m (("(", "sym") : s ++ [(")", "sym")])
         if t == [] || r /= [] then do
           putStr "Invalid input.\n"
         else do
            let evalResult = eval [] (head t)

            case evalResult of
                Left err -> do
                    putStrLn err
                Right term -> do
                    let p = f term
                    
                    -- print $ head t
                    
                    if p /= "" then do
                        putStrLn p
                    else do
                        let termString = t2s term
                        putStrLn termString
         s2t_interpreter m f
                   
main = do putStr "Haskell interpreter of the simply typed lambda calculus.\n"
          putStr "Input -h for help, exit to terminate the program.\n"
          s2t_interpreter s2t_static_mem t2s