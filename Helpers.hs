module Helpers where
import Types

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
