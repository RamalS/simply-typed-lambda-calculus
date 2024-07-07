module Evaluation where
    
import Types
import Helpers
import TypeChecking

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
        f c (TmAnd t1 t2) = TmAnd (f c t1) (f c t2)
        f c (TmOr t1 t2) = TmOr (f c t1) (f c t2)
        f c (TmNot t1) = TmNot (f c t1)
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
        f c (TmAnd t1 t2) = TmAnd (f c t1) (f c t2)
        f c (TmOr t1 t2) = TmOr (f c t1) (f c t2)
        f c (TmNot t1) = TmNot (f c t1)
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

-- Logical operators
evalStep (TmAnd TmTrue t2) = Right t2
evalStep (TmAnd TmFalse _) = Right TmFalse
evalStep (TmAnd t1 t2) = do
    t1' <- evalStep t1
    Right $ TmAnd t1' t2

evalStep (TmOr TmTrue _) = Right TmTrue
evalStep (TmOr TmFalse t2) = Right t2
evalStep (TmOr t1 t2) = do
    t1' <- evalStep t1
    Right $ TmOr t1' t2

evalStep (TmNot TmTrue) = Right TmFalse
evalStep (TmNot TmFalse) = Right TmTrue
evalStep (TmNot t) = do
    t' <- evalStep t
    Right $ TmNot t'

evalStep t
  | isVal t = Right t
  | otherwise = Left "No rule applies"

-- Eval
eval :: Context -> Term -> Either String Term
eval ctx t = case typeOf ctx t of
    Left err -> Left $ "Type error: " ++ err
    Right _ -> case evalStep t of
        Right t' -> if t' == t then Right t else eval ctx t'
        Left err -> Left $ "Evaluation error: " ++ err