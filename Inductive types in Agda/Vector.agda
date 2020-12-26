open import Data.List

--6.1 Warmup : Head can't be defined for the empty list

open import Data.Nat

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)


--6.3 Head and tail

hd : {A : Set} -> {n : ℕ}  -> Vec A (suc n) -> A
hd (x ∷ v) = x

tl : {A : Set} -> {n : ℕ}  -> Vec A (suc n) -> A
tl (x ∷ []) = x
tl (x ∷ (x₁ ∷ v)) = tl (x₁ ∷ v)

--6.4 Concatenation

cncat : {A : Set} -> {n m : ℕ} -> Vec A n -> Vec A m -> Vec A (n + m)
cncat [] v = v
cncat (x ∷ u) v = x ∷ (cncat u v)

--6.5 Reversal

snoc : {A : Set} -> {n : ℕ} -> Vec A n -> A -> Vec A (suc n)
snoc [] x = x ∷ []
snoc (x₁ ∷ l) x = x₁ ∷ ( snoc l x )

rev : {A : Set} -> {n : ℕ}  -> Vec A n -> Vec A n
rev [] = []
rev (x ∷ l) = snoc (rev l) x

--6.6 Accessing an element

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

ith : {A : Set} -> {n : ℕ}  -> Vec A n -> Fin n -> A
ith (x ∷ l) zero = x
ith (x ∷ l) (suc i) = ith l i

--6.7 Zipping


open import   Data.Product hiding (zip)

zipp : {A B : Set} -> {n : ℕ} -> Vec A n -> Vec B n -> Vec (A × B) n

zipp [] [] = []
zipp (x ∷ l) (x₁ ∷ t) = (x , x₁) ∷ (zipp l t)


--6.8 Associativity of concatenation


open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties using (+-assoc)


-- Without coercion, the two types of  (cncat (cncat l t) u and (cncat l (cncat t u)) are different, therefore equality can't be defined between elements of these types

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

lm1 : (A : Set) -> (n m o : ℕ) -> Vec A ((n + m) + o) ≡ Vec A (n + (m + o))
lm1  A n m o = cong (λ y → Vec A y) (+-assoc n m o)

lm2 : {A : Set} -> {n m  : ℕ} ->  (l : Vec A n) → (t : Vec A m) -> (p : n ≡ m) -> ( (coe (cong (λ y → Vec A y) p) l) ≡ t) -> (x : A) -> (coe (cong (λ y → Vec A  y) (cong suc p)) (x ∷ l)) ≡ (x ∷ t)
lm2   [] [] refl refl x = refl
lm2  (x₁ ∷ l) (.x₁ ∷ .l) refl refl x = refl

assoc_concat : {A : Set} → (n m o : ℕ) ->  (l : Vec A n) → (t : Vec A m) → (u : Vec A o) → (coe (lm1 A n m o) (cncat (cncat l t) u) ) ≡ (cncat l (cncat t u))
assoc_concat 0 m o  [] t u = refl
assoc_concat (suc n)  m o  (x ∷ l) t u = lm2 (cncat (cncat l t) u) (cncat l (cncat t u)) ((+-assoc n m o)) (assoc_concat n m o l t u) x

open import Relation.Binary.HeterogeneousEquality  renaming (cong to cong1)
open import Relation.Binary.HeterogeneousEquality

-- I can't get the congurence to work properly

assocconcat' : {A : Set} → {n m o : ℕ} ->  (l : Vec A n) → (t : Vec A m) → (u : Vec A o) →  (cncat (cncat l t) u) ≅ (cncat l (cncat t u))
assocconcat' [] t u = refl
assocconcat' (x ∷ l) t u = {!!}
