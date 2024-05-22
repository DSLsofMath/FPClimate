Just some live-coding examples from seminar 8.
/Patrik Jansson
\begin{code}
module Live8 where
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Fin
open import Data.Bool using (Bool; false; true; _∧_; _∨_; _xor_)
open import Data.Nat using (zero; suc) renaming (ℕ to Nat)
open import Data.Product
open import Prob.SP
\end{code}

\begin{code}
module BudgetExample (InnerX : Nat -> Set) (M : Set -> Set) where
  X : Nat -> Set
  X t = Nat × InnerX t -- your available budget, paired with another state component
  Y : (t : Nat) -> X t -> Set
  Y t (b , xi) = Fin (suc b)  -- how much of your budget do you want to invest now
  -- then next will have to "subtract" the "action" from the budget
  next : (t : Nat) -> (x : X t) -> Y t x -> M (X (suc t))
  next t (b , xi) y = {!!}

\end{code}
\begin{code}
data InitialState : Set where
  initPos : InitialState

X : Nat -> Set
X zero     = InitialState
X (suc t)  = Fin (suc (suc t))
  -- Fin n ~= {0,1,2,...,n-1}
ex0 : X 0
ex0 = initPos
ex1 : X 1 -- Fin 2
ex1 = suc zero

Y : (t : Nat) -> X t -> Set
Y t x = Bool

-- toFin : (t : Nat) -> Fin (suc t
-- toFin = ?
-- M = Id
M : Set -> Set
M A = A

next2 : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (suc t))
next2 t x y = zero

stay : ∀ {n} -> Fin n -> Fin (suc n)
stay zero         = Fin.zero
stay (suc {n} x)  = Fin.suc {Nat.suc n} (stay x)

next3 : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (suc t))
next3 zero initPos false  = zero
next3 zero initPos true   = suc zero
next3 (suc t) x false  = stay x
next3 (suc t) x true   = suc x

ex3 = next3 0 initPos true    -- = 1
ex4 = next3 1 ex3     true    -- = 2
ex4' = next3 1 ex3    false   -- = 1

postulate Val : Set

reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (nx : X (suc t)) -> Val
reward = {!!}

\end{code}

-- false means "stay" and true means "+1"


  x : Fin (suc (suc t))       -- x : {0,1,2,...,t+1}

Goal: Fin (suc (suc (suc t))) -- y : {0,1,2,...,t+2}
