import DeBruijn

data Ty =
    TyBool
    | TyArr Ty Ty
    | TyNat
    | TyAny
    deriving (Show, Eq, Read)

data Term =
    -- Booleans
    TmTrue
    | TmFalse
    | TmZero
    -- Arithmetic
    | TmSucc Term
    | TmPred Term
    | TmIsZero Term
    | TmPlus Term Term
    | TmEq Term Term
    | TmLt Term Term
    -- Conditionals
    | TmIf Term Term Term
    | TmVar Int
    | TmLam String Ty Term
    | TmApp Term Term deriving (Show, Eq, Read)

type Context = [(String, Ty)]

addToContext :: Context -> String -> Ty -> Context
addToContext ctx x ty = (x, ty) : ctx

getFromContext :: Context -> Int -> Either String Ty
getFromContext ctx i
    | i < 0 || i >= length ctx = Left $ "Index " ++ show i ++ " out of bounds"
    | otherwise = Right (snd (ctx !! i))

-- Is Value
isVal :: Term -> Bool
isVal t = case t of
    TmLam {} -> True
    TmTrue -> True
    TmFalse -> True
    TmZero -> True
    TmSucc t1 -> isNumericVal t1
    _ -> False

-- Is Numeric Value
isNumericVal :: Term -> Bool
isNumericVal TmZero = True
isNumericVal (TmSucc t) = isNumericVal t
isNumericVal _ = False

shift :: Int -> Term -> Term
shift d t = f 0 t
  where f c v@(TmVar x) = if x >= c then TmVar (d + x) else v
        f c (TmLam name ty t) = TmLam name ty (f (c + 1) t)
        f c (TmApp t1 t2) = TmApp (f c t1) (f c t2)
        f c (TmIf t1 t2 t3) = TmIf (f c t1) (f c t2) (f c t3)
        f c (TmSucc t1) = TmSucc (f c t1)
        f c (TmPred t1) = TmPred (f c t1)
        f c (TmIsZero t1) = TmIsZero (f c t1)
        f c (TmPlus t1 t2) = TmPlus (f c t1) (f c t2)
        f c (TmEq t1 t2) = TmEq (f c t1) (f c t2)
        f c (TmLt t1 t2) = TmLt (f c t1) (f c t2)
        f _ t = t

subst :: Int -> Term -> Term -> Term
subst j s t = f 0 t
  where f c v@(TmVar x) = if j + c == x then shift c s else v
        f c (TmLam name ty t) = TmLam name ty (f (c + 1) t)
        f c (TmApp t1 t2) = TmApp (f c t1) (f c t2)
        f c (TmIf t1 t2 t3) = TmIf (f c t1) (f c t2) (f c t3)
        f c (TmSucc t1) = TmSucc (f c t1)
        f c (TmPred t1) = TmPred (f c t1)
        f c (TmIsZero t1) = TmIsZero (f c t1)
        f c (TmPlus t1 t2) = TmPlus (f c t1) (f c t2)
        f c (TmEq t1 t2) = TmEq (f c t1) (f c t2)
        f c (TmLt t1 t2) = TmLt (f c t1) (f c t2)
        f _ t = t

beta :: Term -> Term -> Term
beta s t = shift (-1) $ subst 0 (shift 1 s) t


-- Eval Step
evalStep :: Term -> Either String Term
-- Beta-reduction rule
evalStep (TmApp (TmLam _ _ t12) v2) | isVal v2 = Right $ beta v2 t12
evalStep (TmApp t1 t2)
  | isVal t1 = case evalStep t2 of
                  Right t2' -> Right $ TmApp t1 t2'
                  Left err -> Left err
  | otherwise = case evalStep t1 of
                  Right t1' -> Right $ TmApp t1' t2
                  Left err -> Left err
evalStep t@(TmLam {}) = Right t

-- Conditional evaluation
evalStep (TmIf TmTrue t2 _) = Right t2
evalStep (TmIf TmFalse _ t3) = Right t3
evalStep (TmIf t1 t2 t3) = case evalStep t1 of
                              Right t1' -> Right $ TmIf t1' t2 t3
                              Left err -> Left err

-- Arithmetic operations
evalStep (TmSucc t1) = do
  t1' <- evalStep t1
  Right $ TmSucc t1'

evalStep (TmPred TmZero) = Right TmZero
evalStep (TmPred (TmSucc nv1)) | isNumericVal nv1 = Right nv1
evalStep (TmPred t1) = do
  t1' <- evalStep t1
  Right $ TmPred t1'

evalStep (TmIsZero TmZero) = Right TmTrue
evalStep (TmIsZero (TmSucc nv1)) | isNumericVal nv1 = Right TmFalse
evalStep (TmIsZero t1) = do
  t1' <- evalStep t1
  Right $ TmIsZero t1'

evalStep (TmPlus TmZero t) = Right t
evalStep (TmPlus (TmSucc t1) t2) = do
    t1' <- evalStep t1
    Right $ TmSucc (TmPlus t1' t2)
evalStep (TmPlus t1 t2)
    | isVal t1 = case evalStep t2 of
        Right t2' -> Right $ TmPlus t1 t2'
        Left err -> Left err
    | otherwise = case evalStep t1 of
        Right t1' -> Right $ TmPlus t1' t2
        Left err -> Left err

-- Equality
evalStep (TmEq TmZero TmZero) = Right TmTrue
evalStep (TmEq (TmSucc _) TmZero) = Right TmFalse
evalStep (TmEq TmZero (TmSucc _)) = Right TmFalse
evalStep (TmEq (TmSucc t1) (TmSucc t2)) = Right $ TmEq t1 t2
evalStep (TmEq TmTrue TmTrue) = Right TmTrue
evalStep (TmEq TmFalse TmFalse) = Right TmTrue
evalStep (TmEq TmTrue TmFalse) = Right TmFalse
evalStep (TmEq TmFalse TmTrue) = Right TmFalse
evalStep (TmEq t1 t2)
    | not $ isNumericVal t1 = do
        t1' <- evalStep t1
        Right $ TmEq t1' t2
    | not $ isNumericVal t2 = do
        t2' <- evalStep t2
        Right $ TmEq t1 t2'
evalStep (TmEq _ _) = Right TmFalse

-- Less than
evalStep (TmLt TmZero TmZero) = Right TmFalse
evalStep (TmLt (TmSucc _) TmZero) = Right TmFalse
evalStep (TmLt TmZero (TmSucc _)) = Right TmTrue
evalStep (TmLt (TmSucc t1) (TmSucc t2)) = Right $ TmLt t1 t2
evalStep (TmLt t1 t2)
    | not (isNumericVal t1) = do
        t1' <- evalStep t1
        Right $ TmLt t1' t2
    | not (isNumericVal t2) = do
        t2' <- evalStep t2
        Right $ TmLt t1 t2'
evalStep (TmLt _ _) = Right TmFalse

evalStep t
  | isVal t = Right t
  | otherwise = Left "No rule applies"

-- Type of
typeOf :: Context -> Term -> Either String Ty
typeOf ctx TmTrue = Right TyBool
typeOf ctx TmFalse = Right TyBool
typeOf ctx TmZero = Right TyNat

typeOf ctx (TmVar x) = getFromContext ctx x

typeOf ctx (TmLam name tyT1 t2) = do
  let ctx' = addToContext ctx name tyT1
  tyT2 <- typeOf ctx' t2
  Right (TyArr tyT1 tyT2)

typeOf ctx (TmApp t1 t2) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  case tyT1 of
    TyArr tyT11 tyT12 ->
      if tyT2 == tyT11
        then Right tyT12
        else Left "Parameter type mismatch"
    _ -> Left "Arrow type expected"

typeOf ctx (TmIf t1 t2 t3) = do
  tyT1 <- typeOf ctx t1
  if tyT1 == TyBool
    then do
      tyT2 <- typeOf ctx t2
      tyT3 <- typeOf ctx t3
      if tyT2 == tyT3
        then Right tyT2
        else Left "Branches have different types"
    else Left "Guard of conditional is not a boolean"

-- Arithmetic
typeOf ctx (TmSucc t1) = do
  tyT1 <- typeOf ctx t1
  if tyT1 == TyNat
    then Right TyNat
    else Left "Argument of succ is not a number"

typeOf ctx (TmPred t1) = do
  tyT1 <- typeOf ctx t1
  if tyT1 == TyNat
    then Right TyNat
    else Left "Argument of pred is not a number"

typeOf ctx (TmIsZero t1) = do
  tyT1 <- typeOf ctx t1
  if tyT1 == TyNat
    then Right TyBool
    else Left "Argument of iszero is not a number"

typeOf ctx (TmPlus t1 t2) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  if tyT1 == TyNat && tyT2 == TyNat
    then Right TyNat
    else Left "Arguments of plus are not numbers"

typeOf ctx (TmEq t1 t2) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  if (tyT1 == TyNat && tyT2 == TyNat) || (tyT1 == TyBool && tyT2 == TyBool)
    then Right TyBool
    else Left "Arguments of eq are not numbers or booleans"

typeOf ctx (TmLt t1 t2) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  if tyT1 == TyNat && tyT2 == TyNat
    then Right TyBool
    else Left "Arguments of lt are not numbers"

-- Eval
eval :: Context -> Term -> Either String Term
eval ctx t = case typeOf ctx t of
    Left err -> Left $ "Type error: " ++ err
    Right _ -> case evalStep t of
        Right t' -> if t' == t then Right t else eval ctx t'
        Left err -> Left $ "Evaluation error: " ++ err


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
t2s s@(TmSucc t) = "c" ++ [intToChar(c2i s)]
t2s p@(TmPred t) = "c" ++ [intToChar(c2i p)]
t2s TmZero = "zero"
t2s TmTrue = "true"
t2s TmFalse = "false"
t2s (TmPlus s t) = "plus " ++ t2s s ++ " " ++ t2s t
t2s (TmEq s t) = "eq " ++ t2s s ++ " " ++ t2s t

nonIdentifiers = ["true", "false", "zero", "succ", "plus", "if", "eq"]

s2t_static_mem :: [(String, Term)]
s2t_static_mem = 
       []
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

primjerLam = s2t_read_lam "\\x: bool.(plus 0 c2)"
prvi = fst primjerLam

extractVarAndType :: String -> (String, String)
extractVarAndType s = (a, dropWhile (== ' ') $ drop 1 b)
  where (a, b) = span (/= ':') c
        c = init (drop 1 s)

primjerExtract :: (String, String)
primjerExtract = extractVarAndType prvi
 

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

-- Parse "true"
s2t_interpret_true :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_true m (("true", "true") : s) = ([TmTrue], s)

-- Parse "false"
s2t_interpret_false :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_false m (("false", "false") : s) = ([TmFalse], s)

-- Parse "zero"
s2t_interpret_zero :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_zero m (("zero", "zero") : s) = ([TmZero], s)

-- Parse "succ" followed by a term
s2t_interpret_succ :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_succ m (("succ", "succ") : s) =
  case s2t_interpret_term m s of
    ([t], s') -> ([TmSucc t], s')
    _ -> ([], [])

-- Parse "plus" followed by two terms
s2t_interpret_plus :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_plus m (("plus", "plus") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmPlus t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

-- Parse "eq" followed by two terms
s2t_interpret_eq :: [(String, Term)] -> [(String, String)] -> ([Term], [(String, String)])
s2t_interpret_eq m (("eq", "eq") : s) =
  case s2t_interpret_term m s of
    ([t1], s1) ->
      case s2t_interpret_term m s1 of
        ([t2], s2) -> ([TmEq t1 t2], s2)
        _ -> ([], [])
    _ -> ([], [])

-- Parse "if" followed by three terms
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

-- Main function to interpret a term
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
  | b == "eq" = s2t_interpret_eq m s
  | b == "if" = s2t_interpret_if m s
  | otherwise = ([], [])

-- Primjer
primjer = s2t_interpret_term s2t_static_mem (s2t_tokenize "\\.(plus 0 c2)" [])

s2t_interpret_assign :: [(String, Term)] -> [(String, String)] -> [(String, Term)]
s2t_interpret_assign m ((a, "idt") : ("=", "sym") : t) = 
  if l == [] || s /= [] then [] else s2t_set_mem m a (head l)
  where (l, s) = s2t_interpret_term m (("(", "sym") : t ++ [(")", "sym")])

-- Primjer
primjer2 = s2t_interpret_assign s2t_static_mem (s2t_tokenize "a = \\.(plus 0 c2)" [])

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
                    
                    print $ head t
                    
                    if p /= "" then do
                        putStrLn p
                    else do
                        let termString = t2s term
                        putStrLn termString
         s2t_interpreter m f
                   
main = do putStr "Haskell interpreter of the simply typed lambda calculus.\n"
          putStr "Input -h for help, exit to terminate the program.\n"
          s2t_interpreter s2t_static_mem t2s   