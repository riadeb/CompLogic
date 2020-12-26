open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n


--1.1 Compatibility with successor

≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s p) = p

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc p = s≤s p

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = ≤-suc (≤s n)

-- 1.2 Reflexivity

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = ≤-suc (≤-refl n)

--1.3 Transitivity

≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n r = z≤n
≤-trans (s≤s q) (s≤s r) = ≤-suc (≤-trans q r)

--1.4 Totality

_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
suc m ≤? zero = right z≤n
suc m ≤? suc n with m ≤? n
... | left x = left (≤-suc x)
... | right y = right (≤-suc y)

--2.1 Insertion

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ [] 
insert x (y ∷ l) with x ≤? y
... | left x₁ = x  ∷ (y ∷ l)
... | right y₁ = y ∷ (insert x l)

--2.2 Sorting

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ l) = insert x (sort l)

test : List ℕ
test = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

--2.3 The bounded below predicate

_≤*_ : (x : ℕ) → (l : List ℕ) → Set
x ≤* [] = ⊤
x ≤* (y ∷ l) =  (x ≤ y ) ∧ (x ≤* l)

--2.4 The sorted predicate

sorted : (l : List ℕ) → Set
sorted [] = ⊤
sorted (x ∷ l) = (x ≤* l ) ∧ (sorted l)

--2.5 Insert is sorting

≤*-trans : {x y : ℕ } -> ( l : List ℕ ) -> (y ≤* l ) -> (x ≤ y) -> (x ≤* l)
≤*-trans  [] p q = tt
≤*-trans  (x₁ ∷ l) p q = (≤-trans q (fst p)) , (≤*-trans  l (snd p) q)

≤*-trans' : {x y : ℕ } -> ( l : List ℕ ) -> (y ≤* l ) -> (y ≤ x) -> (y ≤* (insert x l))
≤*-trans' [] p q = q , tt
≤*-trans' { x } (z ∷ l) p q with  x ≤? z
... | left x₁ = q , ((≤-trans q x₁) , snd p)
... | right y = (fst p) , ≤*-trans' l (snd p) q



insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] tt = tt , tt
insert-sorting x (y ∷ l) (fst , snd) with x ≤? y
... | left p = (p , ≤*-trans l fst p) , fst , snd
... | right p = ≤*-trans' l fst p , insert-sorting x l snd

--2.6 Sort is sorting

sort-corr : (l : List ℕ) -> sorted (sort l)
sort-corr [] = tt
sort-corr (x ∷ l) = insert-sorting x (sort l) (sort-corr l)

--2.7 The problem of specification

f : List ℕ → List ℕ
f l = []

f-sorting : (l : List ℕ) → sorted (f l)
f-sorting l = tt

--Sorted does not inforce the fact that sort(l) should contain the same elements as l, only that it is A sorted list 

--2.8 Intrinsic approach

--To define Sorted, we need access to the top element to compare with the new element in the second constructor

mutual
  data Sorted : Set where
    nil : Sorted
    cons : (x : ℕ) -> (l : Sorted) -> (x ≤ head (suc x) l ) -> Sorted 

  head : ℕ → Sorted → ℕ
  head d nil = d
  head d (cons x l x₁) = x


mutual
  insert' : (x : ℕ) → Sorted → Sorted
  insert' x nil = cons x nil (≤s x)
  insert' x (cons y l z) with (x ≤? y)
  ... | left x₁ = cons x ((cons y l z)) x₁
  ... | right y₁ = cons y (insert' x l) (hd-trans l y₁ z)

  hd-trans : {x y : ℕ} -> (l : Sorted ) -> y ≤ x -> y ≤ head (suc y) l -> y ≤ head (suc y) (insert' x l)
  hd-trans nil p q = p
  hd-trans { x } (cons a l z) p q with x ≤? a
  ... | left x₁ = p
  ... | right y = q


sort' : (l : List ℕ) → Sorted
sort' [] = nil
sort' (x ∷ l) = insert' x (sort' l)



--3 Preservation of elements

-- 3.1 Permutations

data _∼_ {A : Set} : List A → List A → Set where
  ∼-nil : [] ∼ []
  ∼-drop : (x : A) {l l' : List A} → l ∼ l' → (x ∷ l) ∼ (x ∷ l')
  ∼-swap : (x y : A) (l : List A) → (x ∷ y ∷ l) ∼ (y ∷ x ∷ l)
  ∼-trans : {l l' l'' : List A} → l ∼ l' → l' ∼ l'' → l ∼ l''

--3.2 Properties

∼-refl : {A : Set} {l : List A} → l ∼ l
∼-refl {l = []} = ∼-nil
∼-refl {l = x ∷ l} = ∼-drop x (∼-refl)

∼-sym : {A : Set} {l l' : List A} → l ∼ l' → l' ∼ l
∼-sym ∼-nil = ∼-nil
∼-sym (∼-drop x p) = ∼-drop x (∼-sym p)
∼-sym (∼-swap x y l) = (∼-swap  y x  l)
∼-sym (∼-trans p q) = ∼-trans (∼-sym q) (∼-sym p)

--3.3 Insertion and permutation

insert-∼ : (x : ℕ) (l : List ℕ) → (x ∷ l) ∼ (insert x l)
insert-∼ x [] = ∼-refl
insert-∼ x (y ∷ l) with x ≤? y
... | left z =  ∼-refl
... | right z = ∼-trans (∼-swap x y l) (∼-drop y (insert-∼ x l))

∼-insert : (x : ℕ) {l l' : List ℕ} → l ∼ l' → insert x l ∼ insert x l'
∼-insert  x {l} {l'} p = ∼-trans (∼-sym (∼-trans (∼-drop x (∼-sym p)) (insert-∼ x l))) (insert-∼ x l')

--3.4 Sorting and permutation
sort-∼ : (l : List ℕ) → l ∼ (sort l)
sort-∼ [] = ∼-nil
sort-∼ (x ∷ l) = ∼-trans (insert-∼ x l) (∼-insert x  (sort-∼ l))


--4 Merge sort


--4.1 Splitting

split : {A : Set} → List A → List A × List A
split [] = [] , []
split (x ∷ []) = (x ∷ []) , []
split (x ∷ x₁ ∷ l) with (split l)
... | f , s = x ∷ f ,  x₁ ∷ s

test1 : List ℕ ×  List ℕ
test1 = split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])



--4.2 Merging

{-# TERMINATING #-}
merge : (l m : List ℕ) → List ℕ
merge [] m = m
merge (x ∷ l) [] = x ∷ l
merge (x ∷ l) (y ∷ m) with x ≤? y
... | left z = x ∷ (merge l (y ∷ m) )
... | right z = y ∷ (merge (x ∷ l)  m )




--4.3 Sorting

{-# TERMINATING #-}
mergesort' : List ℕ → List ℕ
mergesort' [] = []
mergesort' (x ∷ []) = x ∷ []
mergesort' l with split l
... | f , s = merge (mergesort' f) (mergesort' s)

test-merge' : List ℕ
test-merge' = mergesort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

--4.4 Splitting is decreasing


data _<_ : ℕ → ℕ → Set where
  n<m : {n m : ℕ} -> (suc n ≤ m) -> n < m

lleq : {m n : ℕ} -> (m < n) -> (m  ≤ n)
lleq {m} (n<m x) = ≤-trans (≤s m) x

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

lensplit : {A : Set} (l : List A)  -> (length (fst(split l)) ≤ length l)
lensplit [] = z≤n
lensplit (x ∷ []) = s≤s z≤n
lensplit (x ∷ x₁ ∷ l) = ≤-suc (≤-trans (lensplit l) (≤s (length l)))

lensplit' : {A : Set} (l : List A)  -> (length (snd(split l)) ≤ length l)
lensplit' [] = z≤n
lensplit' (x ∷ []) = z≤n
lensplit' (x ∷ x₁ ∷ l) =  ≤-suc (≤-trans (lensplit' l) (≤s (length l)))

lensplit1 : {A : Set} (l : List A) -> (2 ≤ length l) -> (length (fst(split l)) < length l)
lensplit1 (x ∷ y ∷ l) (s≤s p) = n<m (≤-suc (≤-suc (lensplit l)))

lensplit2 : {A : Set} (l : List A) -> (1 ≤ length l) -> (length (snd(split l)) < length l)
lensplit2 (x ∷ []) (s≤s p) = n<m (s≤s p)
lensplit2 (x ∷ x₁ ∷ l) (s≤s p) = n<m (≤-suc (≤-suc (lensplit' l)))

--4.5 The fuel definition of merge

mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel n [] p = []
mergesort-fuel n (x ∷ []) p = (x ∷ [])
mergesort-fuel (suc n) (x ∷ x₁ ∷ l) (s≤s p) = merge (mergesort-fuel n (fst(split (x ∷ x₁ ∷ l))) (≤-trans (≤-suc (lensplit l)) p)) ((mergesort-fuel n (snd(split (x ∷ x₁ ∷ l))) (≤-trans (≤-suc (lensplit' l)) p)))

mergesort : (l : List ℕ) → List ℕ
mergesort l = mergesort-fuel (length l) l (≤-refl (length l))


test-merge : List ℕ
test-merge = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

--4.6 Merge sort is sorting : Intrisinc approach

-- Terminating tag is necessary here for the same reason as it was in merge function before

{-# TERMINATING #-}
mutual 
  mergeint : (l m : Sorted) → Sorted
  mergeint nil m = m
  mergeint (cons x l x₁) nil = (cons x l x₁)
  mergeint (cons x l x₁) (cons y m x₃) with x ≤? y 
  ... | left x₂ = cons x (mergeint l (cons y m x₃)) (hdtrans' l (cons y m x₃) x₁ x₂)
  ... | right y₁ = cons y (mergeint (cons x l x₁) m ) (hdtrans' (cons x l x₁) m y₁ x₃)

  hdtrans' : {x  : ℕ} -> (l m : Sorted) -> x ≤ (head (suc x) l) -> x ≤( head (suc x) m) -> x ≤ (head (suc x) (mergeint l m))
  hdtrans' nil m p1 p2 = p2
  hdtrans' (cons x l x₁) nil p1 p2 = p1
  hdtrans' (cons x l x₁) (cons y m x₃) p1 p2 with x ≤? y
  ... | left x₂ = p1
  ... | right y₁ = p2


mergesort-fuel-int : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → Sorted
mergesort-fuel-int n [] p = nil
mergesort-fuel-int n (x ∷ []) p = cons x nil (≤s x)
mergesort-fuel-int (suc n) (x ∷ x₁ ∷ l) (s≤s p) = mergeint (mergesort-fuel-int n (fst(split (x ∷ x₁ ∷ l))) (≤-trans (≤-suc (lensplit l)) p)) ((mergesort-fuel-int n (snd(split (x ∷ x₁ ∷ l))) (≤-trans (≤-suc (lensplit' l)) p)))


mergesort-sorting : (l : List ℕ) → Sorted
mergesort-sorting l = mergesort-fuel-int (length l) l (≤-refl (length l))


--5 Well-founded definition of merge sort

--5.1 Basic definitions

Rel : (A : Set) → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (_<_ : Rel A) → Set
WellFounded {A} _<_ = (x : A) → Acc _<_ x



--5.3 Auxiliary lemmas

≤-< : {m n : ℕ} → (m ≤ n) → m ≡ n ∨ m < n
≤-< {n = zero} z≤n = left refl
≤-< {n = suc n} z≤n = right (n<m (s≤s z≤n))
≤-< {m = suc m} {n = suc n} (s≤s p) with (≤-< p)
... | left x = left (cong suc x)
... | right (n<m x) =  right (n<m (≤-suc x))

<-last : {m n : ℕ} → (m < suc n) → m ≡ n ∨ m < n
<-last (n<m x) = ≤-< (≤-pred x)

mutual
  rec : (n y  : ℕ) → y <  n → Acc _<_ y
  rec (suc n) y (n<m x) with <-last (n<m x)
  ... | left refl = wfNat n
  ... | right z = rec n y z

  wfNat : WellFounded _<_
  wfNat y = acc (rec y)


--5.2 Definition of merge sort


mergesortw :(l : List ℕ) → Acc _<_ (length l) -> List ℕ
mergesortw [] (acc x) = []
mergesortw (x ∷ []) (acc z) = x ∷ []
mergesortw (x ∷ y ∷ l) (acc z) = merge (mergesortw (fst(split(x ∷ y ∷ l))) (z (suc (length (fst (split l)))) (n<m (≤-suc (≤-suc (lensplit l)))))) ((mergesortw (snd(split(x ∷ y ∷ l))) (z (suc (length (snd (split l)))) (n<m (≤-suc (≤-suc (lensplit' l)))))))

msortw :  (l : List ℕ) → List ℕ
msortw l = mergesortw l (wfNat (length l))
