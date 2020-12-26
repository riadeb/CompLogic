data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

open import Data.Nat
open import Relation.Binary.PropositionalEquality



--4.1 Length

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

--4.2 Concatenation

concat :  {A : Set} → List A  → List A → List A
concat [] t = t
concat (x ∷ l) t = x ∷ (concat l t)

lenconcat : {A : Set} → (l : List A) → (t : List A) → length (concat l t) ≡ (length l + length t)
lenconcat [] t = refl
lenconcat (x ∷ l) t = cong suc (lenconcat l t)


assoc_concat : {A : Set} →  (l : List A) → (t : List A) → (u : List A) → (concat (concat l t) u) ≡ (concat l (concat t u))
assoc [] concat t u = refl
assoc x ∷ l concat t u = cong (λ y → x ∷ y) (assoc_concat l t u)

--4.3 List reversal

snoc : {A : Set} -> (l : List A) -> A -> List A
snoc [] x = x ∷ [] 
snoc (x₁ ∷ l) x = x₁ ∷ (snoc l x)

rev : {A : Set} -> List A ->  List A
rev [] = []
rev (x ∷ l) = snoc (rev l) x

--------

snoclen : {A : Set} -> (l : List A) -> (x : A) -> length (snoc l x) ≡ suc (length l)
snoclen [] x = refl
snoclen (x₁ ∷ l) x = cong suc (snoclen l x)

revlen : {A : Set} -> (l : List A) -> length (rev l) ≡ length l
revlen [] = refl
revlen (x ∷ l) = trans (snoclen (rev l) x) (cong suc (revlen l))

-------

snochd : {A : Set} ->(l : List A) -> (x : A) -> (y : A) -> x ∷ (snoc l y)  ≡  snoc (x ∷ l) y
snochd [] x y = refl
snochd (x₁ ∷ l) x y = cong (λ y → x ∷ y) refl

snocrev : {A : Set} -> (l : List A) -> (x : A) -> rev(snoc l x) ≡  x ∷ (rev l) 
snocrev [] x = refl
snocrev (x₁ ∷ l) x =  trans (trans (cong rev (snochd l x₁ x)) (trans (cong ((λ y → (snoc y x₁))) (snocrev l x)) (snochd (rev l) x x₁ ))) (trans (sym (snochd (rev l) x x₁)) (cong (λ y → x ∷ y) refl))

revrev : {A : Set} -> (l : List A) -> rev( rev (l)) ≡ l
revrev [] = refl
revrev (x ∷ l) = trans (snocrev (rev l) x) (cong (λ y → x ∷ y) (revrev l))


--4.4 Filtering

open import Data.Bool

filter : {A : Set} → (p : A → Bool) → (l : List A) → List A
filter p [] = []
filter p (x ∷ l) with p x
... | true = x ∷ (filter p l)
... | false = filter p l

filterf : {A : Set} -> (l : List A) -> (filter (λ y → false) l)  ≡ []
filterf [] = refl
filterf (x ∷ l) = filterf l

filtert :  {A : Set} -> (l : List A) -> (filter (λ y → true) l)  ≡ l
filtert [] = refl
filtert (x ∷ l) = cong (λ y → x ∷ y) (filtert l)



