open import Relation.Binary.PropositionalEquality

open import Data.Nat 
open import Data.Nat.Base 
open import Data.Nat.Properties using (+-suc)
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.Core
open import Data.Bool.Properties hiding (_≤?_;_<?_)




open import Data.Product renaming (_×_ to _∧_)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

open import Data.Bool hiding (_<_; _∧_; _≤_;_≤?_;_<?_)

open import Data.Unit hiding (_≤?_;_<?_;_≤_)


isSmaller : (m n : ℕ) -> Bool
isSmaller zero zero = false
isSmaller zero (suc n) = true
isSmaller (suc m) zero = false
isSmaller (suc m) (suc n) = isSmaller m n


--7.1 definition


{-# TERMINATING #-}

quot : (m n : ℕ)  -> (0 < n) -> ℕ 
quot m  (suc n) (s≤s p) with ( (suc n) ≤? m)
... | yes q = suc (quot (m ∸ (suc n))  (suc n)  (s≤s p))
... | no q = zero

{-# TERMINATING #-}

rem : (m n : ℕ) -> (0 < n) -> ℕ 
rem m  (suc n) (s≤s p) with ( (suc n) ≤? m)
rem m  (suc n) (s≤s p) | no q = m
rem m  (suc n) (s≤s p) | yes q = rem (m ∸ (suc n))  (suc n)  (s≤s p)

test52 : ℕ ∧ ℕ
test52 = quot 5 2 (s≤s z≤n) ,  rem 5 2 (s≤s z≤n)

--7.2 correctness

lm1 : (m n x : ℕ) -> (p : (suc n) ≤ m  ) -> (m ∸ (suc n)) ≡ x -> m ≡   suc(n + x) 
lm1 m n x p q =  trans (trans (trans (sym (m∸n+n≡m p)) (cong ((λ y → y + (suc n))) q)) (+-suc x n)) (cong suc (+-comm x n))


{-# TERMINATING #-}

-- I could not find a way to complete this, lm1 with a recursive call should be enough, but I couldn't figure out the syntax

div-corr : (m n : ℕ) -> (p : 0 < n) -> m ≡ (quot m n p) * n + (rem m n p)
div-corr m (suc n) (s≤s p)  with ( (suc n) ≤? m)
div-corr m (suc n) (s≤s p) | no _ = refl
div-corr m (suc n) (s≤s p) | yes q     with ( div-corr (m ∸ (suc n)) (suc n)  (s≤s p) )
div-corr m (suc n) (s≤s p) | yes q     | qq = {!!}


open import Relation.Nullary.Negation

{-# TERMINATING #-}

div' : (m n : ℕ) -> (0 < n) → Σ ℕ (λ q → Σ ℕ (λ r → (m ≡ n * q + r) ∧ (r < n)))
div' m (suc n) (s≤s p) with ( m <? suc n)
div' m (suc n) (s≤s p)  | yes q = zero , (m , (trans (+-identityˡ m) (cong (λ r → r + m) (sym (*-zeroʳ n))) , q))
div' m (suc n) (s≤s p) | no q  with div' (m ∸ (suc n)) (suc n) (s≤s p)
div' m (suc n) (s≤s p) | no q | quo , re , fst , snd = (suc quo) , (re , (trans (lm1 m n ( quo + n * quo + re) (≰⇒> (λ z → q (s≤s z))) fst) (cong suc (trans (sym (trans (cong (λ r → r + re) (trans (trans (sym ((+-assoc quo n (n * quo)))) (cong (λ r → r + n * quo) (+-comm  quo n))) (+-assoc n quo (n * quo)))) (+-assoc n (quo + n * quo) re ))) (cong (λ rr → quo + rr + re) (sym (*-suc n quo))))) , snd))




