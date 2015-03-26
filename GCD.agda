
module GCD where

open import Data.Nat 
open import Data.Nat.Divisibility as Div
open import Relation.Binary
open import Data.Product
open import Induction
open import Induction.Nat
open import Function


module GCD where

  -- Specification of the greatest common divisor (gcd) of two natural
  -- numbers.

  record GCD (m n gcd : ℕ) : Set where
    constructor is
    field
      -- The gcd is a common divisor.
      commonDivisor : gcd ∣ m × gcd ∣ n

      -- All common divisors divide the gcd, i.e. the gcd is the
      -- greatest common divisor according to the partial order _∣_.
      greatest : ∀ {d} → d ∣ m × d ∣ n → d ∣ gcd



