data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false

_∨_ : Bool → Bool → Bool
true ∨ true = true
true ∨ false = true
false ∨ true = true
false ∨ false = false

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

-- Q 2.1

not-inv : (b : Bool) → not (not b) ≡ b
not-inv true = refl
not-inv false = refl

-- Q 2.2

conj-neg : (b : Bool) → (not b) ∧ b ≡ false
conj-neg true = refl
conj-neg false = refl
