module Cezar.Bool where

{-
data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL Bool   #-}
{-# BUILTIN TRUE true   #-}
{-# BUILTIN FALSE false #-}
-}
open import Data.Bool public
open import Cezar.Logic

lift : Bool -> Set
lift true  = True
lift false = False

lift1 : {A : Set} -> (A -> Bool) -> A -> Set
lift1 f a = lift (f a)

lift2 : {A B : Set} -> (A -> B -> Bool) -> A -> B -> Set
lift2 f a b = lift (f a b)

liftDec : (b : Bool) -> lift b ⋁ (lift b -> False)
liftDec true = inl *
liftDec false = inr contradiction

if_then_else : {A : Set} -> Bool -> A -> A -> A
if true  then a else a'  =  a
if false then a else a'  =  a'

_and_ : Bool -> Bool -> Bool
false and b = false
true  and b = b

_or_  :  Bool -> Bool -> Bool
false or b  =  b
true  or b  =  true

{-
not   :  Bool -> Bool
not false  =  true
not true   =  false
-}