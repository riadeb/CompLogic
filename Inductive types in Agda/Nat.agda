data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- 3.2

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

-- 3.3

_*_ : ℕ → ℕ → ℕ
zero * b = zero
suc a * b = b +(a * b)

data _≡_ {A : Set} (x : A) : (y : A) → Set where
  refl : x ≡ x

infix 4 _≡_

-- 3.4

suc-≡ : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡ refl = refl

-- Reasoning by case analysis forces m to be equal to n since there's only one refl in the only possible constructor of (m = n)

-- 3.5

zero+n : (n : ℕ ) → (zero + n ≡ n )
zero+n zero = refl
zero+n (suc n) = refl

n+zero : (n : ℕ ) → (n ≡ zero + n )
n+zero zero = refl
n+zero (suc n) = refl

+assoc : (m n p : ℕ) → (( (m + n) + p) ≡ ( m + (n + p)))
+assoc zero n p = refl
+assoc (suc m) n p = suc-≡ (+assoc m n p)

+assoc1 : (m n : ℕ) → ( suc(m + n) ) ≡ ( m + (suc(n)) )
+assoc1 zero n = refl
+assoc1 (suc m) n = suc-≡ (+assoc1 m n)

open import Relation.Nullary

zero_not_suc : (n : ℕ) → ¬ (zero ≡ (suc n) )
zero n not () suc

-- 3.6 : Recurrence principle

rec : {P : ℕ → Set} → P zero → ( (n : ℕ ) → P n → P (suc n) ) → (m : ℕ) → P m
rec  P0 r zero = P0
rec  P0 r (suc m) = r m (rec P0 r m)

-- Second proof of n + 0 = n

P : ℕ → Set
P  n  =  (n + zero) ≡ n 

P0 : P zero
P0 = refl

n+zero_reg :  ( (n : ℕ ) → P n → P (suc n) )
n+zero_reg n p = ( suc-≡ p )

n+zero' : (n : ℕ ) → ( n + zero )  ≡ n  
n+zero' = rec  P0  n+zero_reg

-- 3.7

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

suc-≡' : {m n : ℕ} → (m ≡ n) → (suc m ≡ suc n)
suc-≡'  = cong suc

-- 3.8  Commutativity of addition

comm+ : (m n : ℕ ) → m + n ≡ n + m
comm+ zero zero = refl
comm+ zero (suc n) = suc-≡ (comm+ zero n) 
comm+ (suc m) zero = suc-≡ (comm+ m zero)
comm+ (suc m) (suc n) = suc-≡ (trans (comm+ m (suc n)) (+assoc1 n m))

--3.9 Injectivity of successor

inj_suc : {m n : ℕ } → (suc m) ≡ (suc n) → m ≡ n
inj refl suc = refl


--3.10 Decidability of equality

open import Relation.Nullary
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)

dec≡ : (m n : ℕ) → (m ≡ n) ∨ ¬ (m ≡ n)
dec≡ zero zero = left refl
dec≡ zero (suc n) = right λ ()
dec≡ (suc m) zero = right (λ ())
dec≡ (suc m) (suc n) with dec≡ m n
... | left refl = left refl
... | right p = right (λ x → p (inj_suc x))


--3.11 Recurrence for equality

J : (A : Set) → (P : (x : A) → (y : A) → (p : x ≡ y) → Set) → (r : (x : A) → P x x refl) → (x : A) → (y : A) → (p : x ≡ y) → P x y p
J A P r x .x refl = r x

-- J means that in order to prove a property that uses the a proof that x=y for any x and y, it is enough to prove it for x = x (ie : refl)


--3.12 Properties of multiplication

n*zero : (n : ℕ) -> zero ≡ n * zero
n*zero zero = refl
n*zero (suc n) = cong ( λ y ->  zero + y) (n*zero n)

+-suc : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc m n = sym (+assoc1 m n)

fact : (n m : ℕ) -> (n * suc m) ≡ n + (n * m) 
fact zero zero = refl
fact (suc n) zero = cong suc (fact n zero)
fact zero (suc m) = refl
fact (suc n) (suc m) = cong suc (trans (cong suc (trans (cong (λ y → m + y) (fact n (suc m))) (trans (sym (+assoc m n (n * suc m))) (trans (cong (λ y → y + (n * suc m)) (comm+ m n)) (+assoc n m (n * suc m)))))) (sym (+-suc n (m + (n * suc m)))))


comm* : (m n : ℕ ) → m * n ≡ n * m
comm* zero n = n*zero n 
comm* (suc m) n = sym (trans (fact n m) (cong (λ y → n + y) (comm* n m)))

dist : (m n p : ℕ) -> (m + n) * p ≡ (m * p) + (n * p)
dist zero n p = refl
dist (suc m) n p = trans (cong (λ y → p + y) (dist m n p)) (sym (+assoc p (m * p) (n * p)))


assoc* : (m n p : ℕ) → (( (m * n) * p) ≡ ( m * (n * p)))
assoc* zero n p = refl
assoc* (suc m) n  p = trans (dist n (m * n) p) (cong (λ y → (n * p) + y) (assoc* m n p))


