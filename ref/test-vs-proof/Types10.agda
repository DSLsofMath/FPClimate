module Types10 where

open import Relation.Binary.PropositionalEquality 
open import Relation.Binary hiding (Rel)
open import Function using (_on_)
import Relation.Binary.On as On
open import Relation.Nullary.Core

open import Data.Nat hiding (fold ; _<_)
                   renaming (_≤_ to _≤n_ ;
                             _+_ to _+n_)

open import Cezar.Float renaming (_<=_ to _≤F_ ;
                                  _+_  to _+f_ ;
                                  _*_  to _*f_ ;
                                  _<_  to _<f_)
open import Cezar.Logic
open import Cezar.Int renaming (_+_ to _+i_ ;
                                _<_ to _<i_ )
open import Cezar.Bool using (Bool;false;true;lift2;if_then_else)

_×_ : Set -> Set -> Set
_×_ = _⋀_

_≤f_ = lift2 _≤F_

id : {A : Set} -> A -> A
id a = a

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
g ∘ f = \ a → g (f a)

_=f=_ : {A B : Set} -> (f g : A -> B) -> Set
f =f= g  =  ∀ a -> f a ≡ g a
-- Alternatives without forall notation:
-- f =f= g  =  (a : _) -> f a ≡ g a
-- _=f=_ {A} f g  =  (a : A) -> f a ≡ g a

record Functor (F : Set -> Set) : Set1 where
  field
    fmap    :  {A B : Set} -> (A -> B) -> F A -> F B
    idLaw   :  {A : Set} ->  
               fmap (id {A}) =f= id {F A}
    compLaw :  {A B C : Set} -> (f : B -> C) -> (g : A -> B) ->
               fmap (f ∘ g)  =f=  (fmap f ∘ fmap g)

data List (A : Set) : Set where
  [_]   : A -> List A
  _::_  : A -> List A -> List A

fold : {A B : Set} -> (A -> B) -> (A -> B -> B) -> List A -> B
fold w c [ a ]      = w a
fold w c (a :: as)  = c a (fold w c as)


map : {A B : Set} -> (A -> B) -> (List A -> List B)
map f = fold  ([_] ∘ f)  (\ a bs → f a :: bs)

mapId' :  {A : Set} -> 
          map (id {A}) =f= id
mapId' [ a ]      = refl
mapId' (a :: as)  with mapId' as
...               |  indHyp  = cong (\ as → a :: as) indHyp

mapComp' : {A B C : Set} -> (f : B -> C) -> (g : A -> B) ->
          map (f ∘ g)  =f=  (map f ∘ map g)
mapComp' f g [ a ]      = refl
mapComp' f g (a :: as)  with mapComp' f g as
...                    |  indHyp  =  cong (\ as → f (g a) :: as) indHyp

mapId :  {A : Set} ->
         map (id {A}) =f= id
mapId [ a ]      = refl
mapId (a :: as)  = cong (\ as → a :: as) (mapId as)

mapComp : {A B C : Set} -> (f : B -> C) -> (g : A -> B) ->
          map (f ∘ g)  =f=  (map f ∘ map g)
mapComp f g [ a ]      =  refl
mapComp f g (a :: as)  =  cong (\ as → f (g a) :: as) (mapComp f g as)

FunctorList : Functor List
FunctorList = record {  fmap     = map;
                        idLaw    = mapId; 
                        compLaw  = mapComp }

-- the Haskell type system cannot ensure functoriality
map' : {A B : Set} -> (A -> B) -> (List A -> List B)
map' f [ a ]      = [ f a ]
map' f (a :: as)  = map' f as

module Old where

  IsIncreasing :  {A : Set} {_≤_ : A -> A -> Set} ->
                  IsPreorder _≡_ _≤_ -> (A -> A) -> Set
  IsIncreasing {A} {_≤_} p≤ f = (a : A) -> a ≤ f a

  VulnMeas  :  {F : Set -> Set} -> Functor F ->
               {V : Set} -> {_≤_ : V -> V -> Set} ->  IsPreorder _≡_ _≤_ ->
               {W : Set} -> {_⊑_ : W -> W -> Set} ->  IsPreorder _≡_ _⊑_ ->
               (m : F V -> W) -> Set
  VulnMeas {F} fF {V} {_≤_} p≤ {W} {_⊑_} p⊑ m =
      (i : V -> V) -> IsIncreasing p≤ i ->
      (x : F V) ->
      m x ⊑ (m (fmap i x))
    where fmap = Functor.fmap fF

module New where
  IsIncreasing :  {A : Set} (_≤_ : A -> A -> Set) ->
                  (A -> A) -> Set
  IsIncreasing _≤_ f  =  ∀ a ->  a ≤ f a

  VulnMeas  :  {F : Set -> Set} ->  Functor F ->
               {V : Set}  -> {_≤_ : V -> V -> Set}  -> IsPreorder _≡_ _≤_  ->
               {W : Set}  -> {_⊑_ : W -> W -> Set}  -> IsPreorder _≡_ _⊑_  ->
               (m : F V -> W) -> Set
  VulnMeas {F} fF {V} {_≤_} p≤ {W} {_⊑_} p⊑ m =
      (i : V -> V) ->  IsIncreasing  _≤_   i         -> 
                       IsIncreasing  _m⊑_  (fmap i)
    where  fmap = Functor.fmap fF
           _m⊑_ : F V -> F V -> Set
           x m⊑ y  =  m x ⊑ m y

module NewSimple where
  IsIncreasing :  {A : Set} {_≤_ : A -> A -> Set} ->
                  (A -> A) -> Set
  IsIncreasing {A} {_≤_} f = (a : A) -> a ≤ f a

  -- Why should we carry around the IsPreorder evidence? It is not needed for IsIncreasing anymore.
  VulnMeas  :  {F : Set -> Set} ->  Functor F ->
               {V : Set}  -> (_≤_ : V -> V -> Set)  ->
               {W : Set}  -> (_⊑_ : W -> W -> Set)  ->
               (m : F V -> W) -> Set
  VulnMeas {F} fF {V} _≤_ {W} _⊑_ m =
      (i : V -> V) ->  IsIncreasing  {V}    {_≤_}   i         -> 
                       IsIncreasing  {F V}  {_m⊑_}  (fmap i)
    where  fmap = Functor.fmap fF
           _m⊑_ = \ x y -> m x ⊑ m y
           -- alternative def.: 

-- open Old
open New
-- open NewSimple -- requires updates further down

postulate X Y : Set -- harm values and vulnerability values
postulate _≤_ : X -> X -> Set -- preorder on X
postulate _⊑_ : Y -> Y -> Set -- preorder on Y
postulate p≤ : IsPreorder _≡_ _≤_
postulate p⊑ : IsPreorder _≡_ _⊑_
postulate F : Set -> Set
postulate fF : Functor F
postulate v : F X  -> Y

module MoreComplex where
  -- Patrik: another version based on inclusion / implication. Not used.

  Rel : Set -> Set1
  Rel A = A -> A -> Set

  RelLift : (F : Set -> Set) -> Set1
  RelLift F = {A : Set} -> Rel A -> Rel (F A)

  PreorderPreserving : (F : Set -> Set) -> RelLift F -> Set1
  PreorderPreserving F liftOrd = 
    {V : Set} -> {_≤_ : V -> V -> Set} -> IsPreorder _≡_ _≤_ ->
                                          IsPreorder _≡_ (liftOrd _≤_)

  VulnMeas' :  {F : Set -> Set} ->
               Functor F -> 
               (liftF : RelLift F) -> 
               (F⊑ : PreorderPreserving F liftF) -> 
               {V : Set} -> {_≤_ : V -> V -> Set} ->
               IsPreorder _≡_ _≤_ ->
               {W : Set}  -> {_⊑_ : W -> W -> Set} ->
               IsPreorder _≡_ _⊑_ ->
               (m : F V -> W) -> Set
  VulnMeas' {F} fF liftF F⊑ 
            {V} {_≤_} p≤ 
            {W} {_⊑_} p⊑
            m 
         = (liftF _≤_) ⇒ (_⊑_ on m) 
  --    (liftF _≤_) ⇒ (_⊑_ on m) 
  -- == forall xF yF. (liftF _≤_) xF yF   ->   (_⊑_ on m)  xF yF

  -- _on_ is from Function.agda
  --   many preservation laws are in Relation/Binary/On.agda


record SemiLattice  {A : Set}{_≤_ : A -> A -> Set}
                    (p≤ : IsPreorder _≡_ _≤_) : Set where
  field
    sup : A -> A -> A
    supComm : (a₁ a₂ : A) -> sup a₁ a₂ ≡ sup a₂ a₁
    supUpperBoundL : (a₁ a₂ : A) -> a₁ ≤ sup a₁ a₂
    supUpperBoundR : (a₁ a₂ : A) -> a₂ ≤ sup a₁ a₂
    supLowestUB : (a₁ a₂ a₃ : A) -> (a₁ ≤ a₃) -> (a₂ ≤ a₃) ->
                  (sup a₁ a₂ ≤ a₃)

  supMonL : (a₁ a₂ a₃ : A) -> (a₁ ≤ a₂) -> a₁ ≤ sup a₂ a₃
  supMonL a₁ a₂ a₃ a₁≤a₂ = trans≤ a₁≤a₂ (supUpperBoundL a₂ a₃)
                           where trans≤ = IsPreorder.trans p≤

  supMonR : (a₁ a₂ a₃ : A) -> (a₁ ≤ a₃) -> a₁ ≤ sup a₂ a₃
  supMonR a₁ a₂ a₃ a₁≤a₃ = trans≤ a₁≤a₃ (supUpperBoundR a₂ a₃)
                           where trans≤ = IsPreorder.trans p≤

  supMon : (a₁ a₂ : A) -> (a₁ ≤ a₂) -> 
           (a₃ a₄ : A) -> (a₃ ≤ a₄) ->
           sup a₁ a₃ ≤ sup a₂ a₄
  supMon a₁ a₂ a₁≤a₂ a₃ a₄ a₃≤a₄ =
    supLowestUB a₁ a₃ (sup a₂ a₄)
                (supMonL a₁ a₂ a₄ a₁≤a₂)
                (supMonR a₃ a₂ a₄ a₃≤a₄)

maximum : {A : Set} {_≤_ : A -> A -> Set} ->
          (p≤ : IsPreorder _≡_ _≤_) -> SemiLattice p≤ ->
          List A -> A
maximum p≤ sl [ a ]      = a
maximum p≤ sl (a :: as)  = sup a (maximum p≤ sl as)
  where sup = SemiLattice.sup sl

{-
maximum : {A : Set} {_≤_ : A -> A -> Set} ->
          IsPreorder _≡_ _≤_ -> Decidable _≤_ ->
          List A -> A
maximum p≤ dec [ a ]      = a
maximum p≤ dec (a :: as) with dec a (maximum p≤ dec as)
maximum p≤ dec (a :: as) | yes a≤max = maximum p≤ dec as
maximum p≤ dec (a :: as) | no  a⟩max = a
-}

maxMeas : {A : Set} {_≤_ : A -> A -> Set} ->
          (p≤ : IsPreorder _≡_ _≤_) ->
          (sl : SemiLattice p≤) ->
          VulnMeas FunctorList p≤ p≤ (maximum p≤ sl)
maxMeas p≤ sl f nd [ a ] = nd a
maxMeas p≤ sl f nd (a :: as) with maxMeas p≤ sl f nd as
... | m = supMon a (f a) (nd a) 
                 (maximum p≤ sl as) (maximum p≤ sl (map f as))
                 m
          where supMon = SemiLattice.supMon sl


maximum' : {A : Set} {_≤_ : A -> A -> Set} ->
           (p≤ : IsPreorder _≡_ _≤_) -> SemiLattice p≤ ->
           List A -> A
maximum' p≤ sl = fold (\ a -> a) sup
  where sup = SemiLattice.sup sl

IsMonotonous :  {A : Set} ->  {_≤A_ : A -> A -> Set}  ->  (pA : IsPreorder _≡_ _≤A_)     ->
                {B : Set} ->  {_≤B_ : B -> B -> Set}  ->  (pB : IsPreorder _≡_ _≤B_)     ->
                (A -> B)  ->
                Set
IsMonotonous {A}{_≤A_} pA {B}{_≤B_} pB f =
  (a₁ a₂ : A)  ->  (a₁ ≤A a₂)  ->  f a₁ ≤B f a₂

IsMonotonous₂ :  {A : Set}  -> {_≤A_ : A -> A -> Set}  -> (pA : IsPreorder _≡_ _≤A_)     ->
                 {B : Set}  -> {_≤B_ : B -> B -> Set}  -> (pB : IsPreorder _≡_ _≤B_)     ->
                 {C : Set}  -> {_≤C_ : C -> C -> Set}  -> (pC : IsPreorder _≡_ _≤C_)     ->
                 (A -> B -> C) ->
                 Set
IsMonotonous₂ {A}{_≤A_} pA {B}{_≤B_} pB {C}{_≤C_} pC f =
  (a₁ a₂ : A)  -> (a₁ ≤A a₂)  -> 
  (b₁ b₂ : B)  -> (b₁ ≤B b₂)  ->  f a₁ b₁  ≤C  f a₂ b₂

foldMeas :  {A : Set}  ->  {_≤A_ : A -> A -> Set} ->  (pA : IsPreorder _≡_ _≤A_) ->
            {B : Set}  ->  {_≤B_ : B -> B -> Set} ->  (pB : IsPreorder _≡_ _≤B_) ->
            (w : A -> B)        ->  IsMonotonous  pA pB w ->
            (c : A -> B -> B)   ->  IsMonotonous₂ pA pB pB c ->
            VulnMeas FunctorList pA pB (fold w c)
foldMeas pA pB  w monw  c mon₂c  i isInc  [ a ]      = monw a (i a) (isInc a)
{-
-- partially filled in: 
foldMeas pA pB  w monw  c mon₂c  i isInc  (a :: as)  = mon₂c ? ? ? ? ? ?
-- checked that Agsy (C-c C-a) fills in the holes up to this point:
foldMeas pA pB  w monw  c mon₂c  i isInc  (a :: as)  =
       mon₂c  a (i a) (isInc a) 
              (fold w c as) 
              (fold w c (fold (λ x → [ i x ]) (λ x → _::_ (i x)) as)) 
              ?
-}
foldMeas pA pB  w monw  c mon₂c  i isInc  (a :: as)  =
    mon₂c  a              (i a)                  (isInc a) 
           (fold w c as)  (fold w c (map i as))  (foldMeas pA pB  w monw  c mon₂c  i isInc  as)

maxMeas' :  {A : Set}  -> {_≤A_ : A -> A -> Set}  -> (pA : IsPreorder _≡_ _≤A_) ->
            (sl : SemiLattice pA) ->
            VulnMeas FunctorList pA pA (maximum' pA sl)
maxMeas' pA sl = foldMeas pA pA
     (\ a -> a) (\ a₁ a₂ a₁≤a₂ -> a₁≤a₂)
     (SemiLattice.sup sl) (SemiLattice.supMon sl)

avg' : List Float -> Float × ℕ
avg' = fold w c
  where  w : Float -> Float × ℕ
         w x = (x , 1)
         c : Float -> Float × ℕ -> Float × ℕ
         c x (sum , len) = (x +f sum) , (1 +n len)


primitive
  primNatToInteger : ℕ -> Int

nat2float : ℕ -> Float
nat2float n = primIntegerToFloat (primNatToInteger n)

_≤fn_ : Float × ℕ -> Float × ℕ -> Set
(x , m) ≤fn (y , n) = let  nf = nat2float n
                           mf = nat2float m
                      in
                          (x *f nf)  ≤f  (y *f mf)


sumList   :   List (Float × Int) -> Float × Int
sumList   =   fold id f
  where         f : Float × Int -> Float × Int -> Float × Int
                f (x , n) (x' , n')  =  (x +f x' , n +i n')

maxf         :   Float -> Float -> Float
maxf  x y    =   if x <f y then y else x

_<_                 :   ℕ -> ℕ -> Bool
zero     < n        =   false
(suc m) < zero      =   false
(suc m) < (suc n)   =   m < n

maxi         :   Int -> Int -> Int
maxi m n     =   if m <i n then n else m

supList   :   List (Float × Int) -> Float × Int
supList   =   fold id f
  where         f : Float × Int -> Float × Int -> Float × Int
                f (x , n) (x' , n')  = (maxf x x' , maxi n n')

postulate ≤fRefl    :   (x : Float) -> x ≤f x
postulate ≤fTrans   :   (x y z : Float) ->
                        x ≤f y -> y ≤f z -> x ≤f z

postulate +fmon     :   (x y x' y' : Float) ->
                        x ≤f x' -> y ≤f y'  ->
                        (x +f y) ≤f (x' +f y')
