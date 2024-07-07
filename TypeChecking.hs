module TypeChecking where
import Types
import Helpers

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

-- Logical operators
typeOf ctx (TmAnd t1 t2) = do
    tyT1 <- typeOf ctx t1
    tyT2 <- typeOf ctx t2
    if tyT1 == TyBool && tyT2 == TyBool
        then Right TyBool
        else Left "Arguments of and are not booleans"

typeOf ctx (TmOr t1 t2) = do
    tyT1 <- typeOf ctx t1
    tyT2 <- typeOf ctx t2
    if tyT1 == TyBool && tyT2 == TyBool
        then Right TyBool
        else Left "Arguments of or are not booleans"

typeOf ctx (TmNot t1) = do
    tyT1 <- typeOf ctx t1
    if tyT1 == TyBool
        then Right TyBool
        else Left "Argument of not is not a boolean"

typeOf ctx (TmMul t1 t2) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  if tyT1 == TyNat && tyT2 == TyNat
    then Right TyNat
    else Left "Arguments of mul are not numbers"