module Types where

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