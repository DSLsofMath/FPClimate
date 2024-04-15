{-# OPTIONS --universe-polymorphism #-}

module Cezar.Logic where

open import Level

-- more polimorphic versions of the Cezar.Logic module

data False : Set where

contradiction : {l : Level}{A : Set l} -> False -> A
contradiction ()

data True : Set where
  * : True

¬ : {l : Level} -> Set l -> Set l
¬ A = A -> False

data _⋁_ {lA lB : Level} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  inl : A -> A ⋁ B
  inr : B -> A ⋁ B

⋁Elim : {lA lB lC : Level} {A : Set lA} {B : Set lB} -> {C : A ⋁ B -> Set lC} ->
        ((a : A) -> C (inl a)) ->           
        ((b : B) -> C (inr b)) ->           
        (s : A ⋁ B) -> C s                  
⋁Elim f g (inl a) = f a
⋁Elim f g (inr b) = g b

data _⋀_ {lA lB : Level} (A : Set lA) (B : Set lB) : Set (lA ⊔ lB) where
  _,_ : A -> B -> A ⋀ B

fst : {lA lB : Level} {A : Set lA} {B : Set lB} ->
      A ⋀ B -> A
fst (a , b) = a

snd : {lA lB : Level} {A : Set lA} {B : Set lB} ->
      A ⋀ B -> B
snd (a , b) = b

infixl 10 _⋀_  
infixl 6 _,_

data ∃ {lA lB : Level} {A : Set lA} (B : A -> Set lB) : Set (lA ⊔ lB) where
  _,_ : (a : A) -> B a -> ∃ B

outl :  {lA lB : Level} {A : Set lA} {B : A -> Set lB} ->
        ∃ B -> A
outl (a , b) = a

outr : {lA lB : Level} {A : Set lA} {B : A -> Set lB} ->
       (p : ∃ B) -> B (outl p)
outr (a , b) = b

_<->_   : {l l' : Level}(A : Set l)(B : Set l') -> Set (l ⊔ l')
A <-> B = A -> B ⋀ B -> A