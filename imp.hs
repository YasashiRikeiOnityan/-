{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Prelude (Int, String, (+), (-), (*))

type N = Int

type Loc = String

data Aexp = Const N   -- n
    | Var Loc         -- X
    | Add Aexp Aexp   -- a0 + a1
    | Sub Aexp Aexp   -- a0 - a1
    | Mul Aexp Aexp   -- a0 * a1

data Bexp = Tru       -- true
    | Fal             -- false
    | Equ Aexp Aexp   -- a0 = a1
    | Leq Aexp Aexp   -- a0 <= a1
    | Not Bexp        -- not b
    | And Bexp Bexp   -- b0 and b1
    | Or Bexp Bexp    -- b0 or b1

data Com = Skip       -- skip
    | Assign Loc Aexp -- X := a
    | Seq Com Com     -- c0;c1
    | If Bexp Com Com -- if b then c0 else c1
    | While Bexp Com  -- while b c

type Sigma = Loc -> N

type AEConf = (Aexp, Sigma)

type BEConf = (Bexp, Sigma)

aexpEqual :: Aexp -> Aexp -> Bexp
aexpEqual (Const n1) (Const n2) = n1 == n2
aexpEqual (Var v1) (Var v2) = v1 == v2
aexpEqual (Add a11 a12) (Add a21 a22) = aexpEqual a11 a21 && aexpEqual a12 a22
aexpEqual (Sub a11 a12) (Sub a21 a22) = aexpEqual a11 a21 && aexpEqual a12 a22
aexpEqual (Mul a11 a12) (Mul a21 a22) = aexpEqual a11 a21 && aexpEqual a12 a22
aexpEqual _ _ = Fal

bexpEqual :: Bexp -> Bexp -> Bexp
bexpEqual Tru Tru = Tru
bexpEqual Fal Fal = Fal
bexpEqual (Equ a11 a12) (Equ a21 a22) = aexpEqual a11 a21 && aexpEqual a12 a22
bexpEqual (Leq a11 a12) (Leq a21 a22) = aexpEqual a11 a21 && aexpEqual a12 a22
bexpEqual (Not b1) (Not b2) = bexpEqual b1 b2
bexpEqual (And b11 b12) (And b21 b22) = bexpEqual b11 b21 && bexpEqual b21 b22
bexpEqual (Or b11 b12) (Or b21 b22) = bexpEqual b11 b21 && bexpEqual b21 b22
bexpEqual _ _ = Fal

comEqual :: Com -> Com -> Bexp
comEqual Skip Skip = Tru
comEqual (Assign l1 a1) (Assign l2 a2) = aexpEqual (Var l1) (Var l2) && aexpEqual a1 a2
comEqual (Seq c11 c12) (Seq c21 c22) = comEqual c11 c21 && comEqual c12 c22
comEqual (If b1 c11 c12) (If b2 c21 c22) = bexpEqual b1 b2 && comEqual c11 c12 && comEqual c21 c22
comEqual (While b1 c1) (While b2 c2) = bexpEqual b1 b2 && comEqual c1 c2
comEqual _ _ = Fal

sigma :: Sigma
sigma _ = 0

evalAexp :: AEConf -> N
evalAexp (Const n, _) = n
evalAexp (Var "Init", _) = 0
evalAexp (Mul a1 a2, s) = evalAexp (a1, s) * evalAexp (a2, s)
evalAexp (Add a1 a2, s) = evalAexp (a1, s) + evalAexp (a2, s)
evalAexp (Sub a1 a2, s) = evalAexp (a1, s) - evalAexp (a2, s)

evalBexp :: BEConf -> Bexp
evalBexp (Tru, _) = Tru
evalBexp (Fal, _) = Fal
evalBexp (Equ a1 a2, s) = evalAexp (a1, s) == evalAexp (a2, s)

(&&) :: Bexp -> Bexp -> Bexp
Tru && x =  x
Fal && _ =  Fal

not :: Bexp -> Bexp
not Tru = Fal
not Fal = Tru

class Eq a where
    (==), (/=) :: a -> a -> Bexp
    {-# HLINT ignore "Use /=" #-}
    {-# HLINT ignore "Use ==" #-}
    x /= y = not (x == y)
    x == y = not (x /= y)

instance Eq Aexp where
    