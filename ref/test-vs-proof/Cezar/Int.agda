module Cezar.Int where

-- open import Cezar.Bool
open import Data.Bool

postulate Int : Set

{-# BUILTIN INTEGER Int    #-}

primitive
  primIntegerPlus     : Int -> Int -> Int
  primIntegerMinus    : Int -> Int -> Int
  primIntegerTimes    : Int -> Int -> Int
  primIntegerDiv      : Int -> Int -> Int  -- partial
  primIntegerMod      : Int -> Int -> Int  -- partial
  primIntegerEquality : Int -> Int -> Bool
  primIntegerLess     : Int -> Int -> Bool

_+_ : Int -> Int -> Int
_+_ = primIntegerPlus

_<_ : Int -> Int -> Bool
_<_ = primIntegerLess

