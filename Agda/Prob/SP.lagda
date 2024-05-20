\begin{code}
{-# OPTIONS --without-K #-}

module Prob.SP where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Float using (Float; _+_; _÷_; _<ᵇ_)
open import Data.Bool using (Bool; false; true; _∧_; _∨_; _xor_)
open import Data.Product using (Σ; _×_; _,_) renaming (proj₁ to π₁ ; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Unary using (Pred; Decidable)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec) renaming ([] to []v; _∷_ to _∷v_)

-- to be moved out

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

filterByB : {A : Set} -> (A -> Bool) -> List A -> List A
filterByB p [] = []
filterByB p (a ∷ as) with (p a)
... | false  =       filterByB p as
... | true   = a ∷  filterByB p as


-- Finite probability distributions (simple minded)

SP  : Set -> Set
SP Ω = List (Ω × Float)

-- The idea is that if all the weights of |sp : SP Ω| are non-negative
-- and if their sum is positive |sp| represents a finite probability
-- distribution on |Ω|.

-- TODO implement a data type |VeriSP : Set -> Set| that fulfils these
-- requirements by construction. Here is one possible step on the way:

data VeriSP (Ω : Set) : Set where
  η     : Ω -> VeriSP Ω
  _::_  : Σ (Ω × Float) (\ (ω , w) -> (0.0 <ᵇ w) ≡ true) -> VeriSP Ω -> VeriSP Ω

-- and then translate to

veriSPtoSP : ∀ {Ω} -> VeriSP Ω -> SP Ω
veriSPtoSP (η ω) = (ω , 1.0) ∷ []
veriSPtoSP ((ωw , prf) :: vsp) = ωw ∷ (veriSPtoSP vsp)

-- and apply the stuff that we are going to implement next, see below.


-- Events (just an alias for characteristic functions)

Event : Set -> Set
Event Ω = Ω -> Bool

_∈_ : ∀ {Ω} -> Ω -> Event Ω -> Bool
ω ∈ e = e ω

∅ : ∀ {Ω} -> Event Ω
∅ = \ ω -> false

◯  : ∀ {Ω} -> Event Ω
◯ = \ ω -> true


-- probability of an event according to a finite probability distribution

sumws : ∀ {Ω} -> SP Ω -> Float
sumws [] = 0.0
sumws ((ω , w) ∷ ωws) = w + sumws ωws

prob : ∀ {Ω} -> SP Ω -> Event Ω -> Float
prob sp e = sumws (filterByB (\ (ω , w) -> ω ∈ e) sp) ÷ (sumws sp)

-- For |prob sp e| to be the probability of |e| according to |sp|, all
-- the weights of |sp| must be non-negative and their sum must be
-- positive.

-- TODO: test that under these assumption |prob| satisfies the
-- probability laws, that is, fulfill
--
--   1) prob sp ∅ = 0
--   2) prob sp ◯ = 1
--   3) e1 ∩ e2 = ∅ => prob sp (e1 ∪ e2) = prob sp e1 + prob sp e2
--
-- for arbitrary |sp|, |e1| and |e2|.

-- Dice examples

data Dice : Set where  one two three four five six  :  Dice

eq : Dice -> Dice -> Bool
eq one    one    = true
eq two    two    = true
eq three  three  = true
eq four   four   = true
eq five   five   = true
eq six    six    = true
eq _      _      = false


fairDice : SP Dice
fairDice = (one , 1.0) ∷ (two , 1.0) ∷ (three , 1.0) ∷ (four , 1.0) ∷ (five , 1.0) ∷ (six , 1.0) ∷ []

biasedDice : SP Dice
biasedDice = (one , 3.0) ∷ (two , 2.0) ∷ (three , 1.0) ∷ (four , 0.0) ∷ (five , 1.0) ∷ (six , 2.0) ∷ []


-- ... implement a few generic combinators for events

_and_  : ∀ {Ω} -> Event Ω -> Event Ω -> Event Ω
e1 and e2 = \ ω -> (ω ∈ e1) ∧ (ω ∈ e2)

_or_  : ∀ {Ω} -> Event Ω -> Event Ω -> Event Ω
e1 or e2 = \ ω -> (ω ∈ e1) ∨ (ω ∈ e2)

-- TODO run some simple tests like
--
--   prob fairDice ∅
--   prob fairDice (eq six)
--   prob fairDice ((eq six) or (eq three))


-- monad SP

fmapSP : {A B : Set} -> (A -> B) -> SP A -> SP B
fmapSP f [] = []
fmapSP f ((ω , w) ∷ ωws) = (f ω , w) ∷ (fmapSP f ωws)

ηSP : ∀ {Ω} -> Ω -> SP Ω
ηSP ω = (ω , 1.0) ∷ []

-- TODO: implement a combinator embedding a list as a distribution
-- (all of the same weight).


-- TODO: specify and implemet |μSP| and point to
-- https://en.wikipedia.org/wiki/Law_of_total_probability

divBy : ∀ {Ω} -> Float -> SP Ω -> SP Ω
divBy x = map (\ (ω , w) -> (ω , w ÷ x))

normalize : ∀ {Ω} -> SP Ω -> SP Ω
normalize sp = divBy (sumws sp) sp

μSP : ∀ {Ω} -> SP (SP Ω) -> SP Ω
μSP [] = []
μSP ((sp , w) ∷ sps) =
  let  sw = sumws sp
       p  = w ÷ sw
  in divBy p sp ++ μSP sps

_>>=SP_ : ∀ {Ω₁ Ω₂} -> SP Ω₁ -> (Ω₁ -> SP Ω₂) -> SP Ω₂
sp >>=SP cp = μSP (fmapSP cp sp)

_>=>SP_ : ∀ {Ω₁ Ω₂ Ω₃ : Set} -> (Ω₁ -> SP Ω₂) -> (Ω₂ -> SP Ω₃) -> (Ω₁ -> SP Ω₃)
f >=>SP cp = \ ω -> μSP (fmapSP cp (f ω))


-- With the monadic operators in place, we can start solving interesting
-- problems.

-- TODO: compute the trajectories of the uncontrolled random walk
-- example from L5 ...

rw : ℕ -> SP ℕ
rw zero     = (0 , 0.5) ∷ (1 , 0.5) ∷ []
rw (suc n)  = (n , 1.0 ÷ 3.0) ∷ (suc n , 1.0 ÷ 3.0) ∷ (suc (suc n) , 1.0 ÷ 3.0) ∷ []

trjSP : {Ω : Set} -> (Ω -> SP Ω) -> (n : ℕ) -> Ω -> SP (Vec Ω (suc n))
trjSP f   zero    ω  =  fmapSP (ω ∷v_) (ηSP []v)
trjSP f ( suc n)  ω  =  fmapSP (ω ∷v_) (f ω >>=SP (trjSP f n))

-- normalize (trjSP rw 0 10)
-- normalize (trjSP rw 1 10)
-- normalize (trjSP rw 2 10)
-- normalize (trjSP rw 3 10)
-- ...

-- TODO If you roll a fair dice and then, if the outcome is |one| or
-- |five| stick to this outcome. Otherwise roll the biased dice. What
-- is the probability of the outcome to be greater than |four|?

r1 : SP Dice
r1 = fairDice

r2 : SP Dice
r2 = biasedDice

example : Dice -> SP Dice
example one   =  ηSP one
example two   =  r2
example three =  r2
example four  =  r2
example five  =  ηSP five
example six   =  r2

-- prob (r1 >>=SP example) ((eq five) or (eq six))

-- TODO: Implement the Monty Hall problem ...

data Game : Set where
  Win  : Game
  Lose : Game

first : SP Game
first = (Win , 1.0 ÷ 3.0) ∷ (Lose , 1.0 ÷ 3.0) ∷ (Lose , 1.0 ÷ 3.0) ∷ []

stick : Game -> SP Game
stick Win  = (Win  , 1.0) ∷ []
stick Lose = (Lose , 1.0) ∷ []

switch : Game -> SP Game
switch Win  = (Lose , 1.0) ∷ []
switch Lose = (Win  , 1.0) ∷  []

-- normalize (first >>=SP stick)
-- normalize (first >>=SP switch)

-- TODO: implement a simple SDP you like or one of the SDPs from the
-- last two papers ...
\end{code}
