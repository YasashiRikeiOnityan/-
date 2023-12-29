-- 必要なものだけインポートする (自分で定義できそうなものはインポートしない方針で)
import Prelude (Int, String, Bool, Show, (+), (-), (*), (==), (<=), ($))

-- 型定義
------------------------------------
type N = Int

type Loc = String

data Aexp = Const N   -- n
    | Var Loc         -- X
    | Add Aexp Aexp   -- a0 + a1
    | Sub Aexp Aexp   -- a0 - a1
    | Mul Aexp Aexp   -- a0 * a1
    deriving Show

data Bexp = Tru       -- true
    | Fal             -- false
    | Equ Aexp Aexp   -- a0 = a1
    | Leq Aexp Aexp   -- a0 <= a1
    | Not Bexp        -- not b
    | And Bexp Bexp   -- b0 and b1
    | Or Bexp Bexp    -- b0 or b1
    deriving Show

data Com = Skip       -- skip
    | Assign Loc Aexp -- X := a
    | Seq Com Com     -- c0;c1
    | If Bexp Com Com -- if b then c0 else c1
    | While Bexp Com  -- while b c
    deriving Show

type State = (Loc, N)

type States = [State]

-- 状態（σ : Loc -> N）
type Sigma = Loc -> N

type AEConf = (Aexp, States)

type BEConf = (Bexp, States)

type CConf = (Com, States)
------------------------------------

-- 前準備
------------------------------------
(&&) :: Bexp -> Bexp -> Bexp
Tru && x =  x
Fal && _ =  Fal

(||) :: Bexp -> Bexp -> Bexp
Tru || _ = Tru
Fal || x = x

bool2bexp :: Bool -> Bexp
bool2bexp b = if b then Tru else Fal

not :: Bexp -> Bexp
not Tru = Fal
not Fal = Tru

myIf :: Bexp -> a -> a -> a
myIf Tru f g = f
myIf Fal f g = g

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

map :: (a -> b) -> [a] -> [b]
{-# NOINLINE [0] map #-}
map _ [] = []
map f (x : xs) = f x : map f xs

states :: States
states = [("X", 0), ("Y", 0), ("Z", 0)]
-------------------------------------

-- 問題2.1 同一性判定
-------------------------------------
aexpEqual :: Aexp -> Aexp -> Bexp
aexpEqual (Const n1) (Const n2) = bool2bexp (n1 == n2)
aexpEqual (Var v1) (Var v2) = bool2bexp (v1 == v2)
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
-------------------------------------

-- 問題2.2, 2.6 評価規則
-------------------------------------
evalAexp :: AEConf -> N
evalAexp (Const n, _) = n
evalAexp (Var "Init", _) = 0
evalAexp (Mul a1 a2, s) = evalAexp (a1, s) * evalAexp (a2, s)
evalAexp (Add a1 a2, s) = evalAexp (a1, s) + evalAexp (a2, s)
evalAexp (Sub a1 a2, s) = evalAexp (a1, s) - evalAexp (a2, s)

evalBexp :: BEConf -> Bexp
evalBexp (Tru, _) = Tru
evalBexp (Fal, _) = Fal
evalBexp (Equ a1 a2, s) = bool2bexp $ evalAexp (a1, s) == evalAexp (a2, s)
evalBexp (Leq a1 a2, s) = bool2bexp $ evalAexp (a1, s) <= evalAexp (a2, s)
evalBexp (Not b, s) = not $ evalBexp (b, s)
evalBexp (And b1 b2, s) = evalBexp (b1, s) && evalBexp (b2, s)
evalBexp (Or b1 b2, s) = evalBexp (b1, s) || evalBexp (b2, s)

evalCom :: CConf -> States
evalCom (Skip, s) = s
evalCom (Assign l a, s) = assign (evalAexp (a, s)) l s
evalCom (Seq c1 c2, s) = evalCom (c2, evalCom (c1, s))
evalCom (If b c1 c2, s) = myIf b (evalCom (c1, s)) (evalCom (c2, s))
evalCom (While b c, s) = myIf b (evalCom (While b c, evalCom (c, s))) s

-- σ[m/X](Y)
assign :: N -> Loc -> States -> States
assign m loc = map (\x -> if fst x == loc then (loc, m) else x)
-------------------------------------
