data Ty =
    TyBool
    | TyArr Ty Ty
    | TyNat
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
evalStep (TmEq t1 t2)
    | not (isNumericVal t1) = do
        t1' <- evalStep t1
        Right $ TmEq t1' t2
    | not (isNumericVal t2) = do
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
  if tyT1 == TyNat && tyT2 == TyNat
    then Right TyBool
    else Left "Arguments of eq are not numbers"

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

-- Testing
main :: IO ()
main = do
    let term = TmApp (TmLam "x" TyNat (TmPlus (TmVar 0) (TmSucc $ TmSucc TmZero))) (TmSucc TmZero)
    print $ eval [] term

    let testIf = TmApp (TmLam "x" TyBool (TmIf (TmVar 0) TmTrue TmFalse))

    let addOneToNumber = TmApp (TmLam "x" TyBool (TmPlus (TmVar 0) (TmSucc TmZero)))
    print $ eval [] (addOneToNumber (TmSucc TmZero))

    let testEq = TmLt (TmSucc TmZero) (addOneToNumber (TmSucc TmZero))
    print $ eval [] testEq