open import Data.Product

×-comm : {A B : Set} → (A × B) → (B × A)
×-comm  (fst , snd) = snd , fst

-- Q 3

-- Q 3.1

K : {A B : Set} → A → B → A
K a b = a

-- Q 3.2

app : {A B : Set} → (A → B) → A → B
app f a = f a

-- Q 3.3

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a =  f a  b

-- Q 3.4
comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp f g = λ z → g (f z)

-- Q 3.5
S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g a = f a (g a)

-- Q4

open import Data.Product renaming (_×_ to _∧_)

-- Q 4.1

proj1 : {A B : Set} → (A ∧ B) → A
proj1 (fst , snd) = fst

proj2 : {A B : Set} → (A ∧ B) → B
proj2 (fst , snd) = snd

-- Q 4.2

diag : {A : Set} → A → (A ∧ A)
diag a = (a , a)

-- Q 4.3
comm : {A B : Set} → (A ∧ B) → (B ∧ A)
comm (a , b) = (b , a)

-- Q 4.4

curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f x y = f (x , y)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f (x , y) = f x y

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) ∧ (B → A)

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = curry1 , curry2

-- Q 4.5

distrib1 : {A B C : Set} → (A → (B ∧ C) ) →  ( (A → B) ∧ (A → C) )
distrib1 f = (λ x → proj1 (f x)) , λ x → proj2 (f x)

distrib2 : {A B C : Set} → ( (A → B) ∧ (A → C) ) → (A → (B ∧ C) )
distrib2 f x = ( (proj1 f) x) , ( (proj2 f) x)

distrib : {A B C : Set} → (A → (B ∧ C) ) ↔  ( (A → B) ∧ (A → C) )
distrib = distrib1 , distrib2

-- Q 5

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

-- Q 5.1

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left a) f g = f a
or-elim (right b) f g = g b

-- Q 5.2
comm_dis : {A B : Set} → (A ∨ B) → (B ∨ A)
comm_dis (left a) = right a
comm_dis (right b) = left b

-- Q 5.3
dist : {A B C : Set} → (A ∧ (B ∨ C)) → (A ∧ B) ∨ (A ∧ C)
dist (a , left b ) = left (a , b)
dist (a , right c ) = right (a , c)

-- Q 6
data ⊥ : Set where

-- Q 6.1

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Q 6.2

¬ : Set → Set
¬ A = A → ⊥

-- Q 6.3

contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr f x y = x (f y)

-- Q 6.4

non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (a , b) = b a 

-- Q 6.5

nni : {A : Set} → A → ¬ (¬ A)
nni a f = f a

-- Q 6.6

⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne f  = f (λ z → z)

-- Q 6.7

¬-elim : {A B : Set} → ¬ A → A → B
¬-elim x y = ⊥-elim (x y)

-- Q 6.8

nnlem : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
nnlem f = f (right (λ x → f (left x)))

-- Q 6.9

rp : {A : Set} → (A → ¬ A) → (¬ A → A) → ⊥
rp f g = f (g (λ z → f z z)) (g (λ z → f z z))

-- Q 7.1

data ⊤ : Set where
  tt : ⊤

-- Q 7.2

ti : {A : Set} → (⊤ → A) → A
ti f = f tt

-- Q 7.3

dmnt : ¬ ⊤ → ⊥
dmnt f = f tt

dmtn : ⊥ → ¬ ⊤
dmtn a  = λ x → a

-- Q 8.1

lem : Set₁
lem = (A : Set) → A ∨ (¬ A)

nne : Set₁
nne = (A : Set) → ¬ (¬ A) → A

nne-lem : nne → lem
nne-lem f A  = f (A ∨ ((x : A) → ⊥)) nnlem

lem-nne' : (A : Set) → (A ∨ ¬ A) → ¬ (¬ A) → A
lem-nne' A (left x) g = x
lem-nne' A (right x) g = ⊥-elim( g x )

lem-nne : lem → nne
lem-nne f A nnA = lem-nne' A (f A) nnA

-- Q 8.2

--I couldn't find a way keeping the arguments implicit because I need access to types A and B in the proof of  nne → pierce

pierce : Set₁
pierce = (A B : Set) → ((A → B) → A) → A 

pierce-nne : pierce → nne
pierce-nne p A nnA = p A ⊥ λ (x : ¬ A)  → ⊥-elim( nnA x )

¬-elim' : (A B : Set) → ¬ A → A → B
¬-elim' A B x y = ⊥-elim (x y)

nne-pierce : nne → pierce
nne-pierce f A B g =  f A (λ (x : ¬ A) → x (g (λ (z : A)  → (¬-elim' A B x z)   ) ) )



