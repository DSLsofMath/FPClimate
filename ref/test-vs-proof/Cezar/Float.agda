module Cezar.Float where

--open import Cezar.Bool
open import Data.Bool renaming (_∧_ to _and_)

open import Cezar.Int renaming (_+_ to _+i_ ;
                                _<_ to _<i_ )


postulate Float : Set

{-# BUILTIN FLOAT   Float  #-}

primitive

  primFloatPlus      : Float -> Float -> Float
  primFloatMinus     : Float -> Float -> Float
  primFloatTimes     : Float -> Float -> Float
  primFloatDiv       : Float -> Float -> Float
  primFloatLess      : Float -> Float -> Bool
  primExp            : Float -> Float
  primLog            : Float -> Float     -- partial
  primSin            : Float -> Float
  primIntegerToFloat : Int -> Float
  primRound          : Float -> Int
  primFloor          : Float -> Int
  primCeiling        : Float -> Int

_+_ : Float -> Float -> Float
_+_ = primFloatPlus

_-_ : Float -> Float -> Float
_-_ = primFloatMinus

_*_ : Float -> Float -> Float
_*_ = primFloatTimes

_/_ : Float -> Float -> Float
_/_ = primFloatDiv

exp : Float -> Float
exp = primExp

log : Float -> Float     -- partial
log = primLog

sin : Float -> Float
sin = primSin       

itof : Int -> Float     
itof = primIntegerToFloat

round : Float -> Int
round = primRound

floor : Float -> Int
floor = primFloor          

ceiling : Float -> Int
ceiling = primCeiling        

_<_ : Float -> Float -> Bool
_<_ = primFloatLess

_==_  : Float -> Float -> Bool
f1 == f2 = not (f1 < f2) and not (f2 < f1)

_<=_ : Float -> Float -> Bool
f1 <= f2 = not (f2 < f1)

_>=_ : Float -> Float -> Bool
f1 >= f2 = f2 <= f1

