
open import Data.Nat
open import Data.Nat.Properties
open import Function.Base

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

open import useful
open import fin

--------------------------------------------------------------------------------
-- Fin duality

-- λ (k : Fin  n) -> (n - 1 - k)
-- λ (_ : Fin  0) ()
fdual : {n : Nat} -> Fin n -> Fin n
fdual {suc n₁} fzero     = fn n₁
fdual {suc n₁} (fsuc k₁) = finj (fdual {n₁} k₁)

-- λ (k : Fin₁ n) -> (n - k)
-- we give different name to `fdual` and this specialization to avoid confusion
-- (the type signature, and role of `n` is different!)
n-minus : (n : Nat) -> Fin₁ n -> Fin₁ n
n-minus n k = fdual {suc n} k

fdual-finj : {n : Nat} -> (k : Fin n) -> fdual (finj k) ≡ fsuc (fdual k)
fdual-finj {_}      fzero     = refl
fdual-finj {suc n₁} (fsuc k₁) = cong finj (fdual-finj {n₁} k₁)

n-minus-fn-is-0 : (n : Nat) -> n-minus n (fn n) ≡ fzero
n-minus-fn-is-0 zero     = refl
n-minus-fn-is-0 (suc n₁) = cong finj (n-minus-fn-is-0 n₁)

fdual-is-involution : {n : Nat} -> (k : Fin n) -> fdual (fdual k) ≡ k
fdual-is-involution {suc n₁} fzero     = (n-minus-fn-is-0 n₁)
fdual-is-involution {suc n₁} (fsuc k₁)
  rewrite (fdual-finj (fdual k₁)) | fdual-is-involution k₁ = refl

k+fdual[k] : {n : Nat} -> (k : Fin₁ n) -> finToNat k + finToNat (fdual k) ≡ n
k+fdual[k] {n}      fzero     rewrite (finToNat-fn n) = refl
k+fdual[k] {suc n₁} (fsuc k₁) rewrite finToNat-finj (fdual k₁) = cong suc (k+fdual[k] {n₁} k₁) 

fdual[k]+k : {n : Nat} -> (k : Fin₁ n) -> finToNat (fdual k) + finToNat k ≡ n
fdual[k]+k {n} k = trans (+-comm (finToNat (fdual k)) (finToNat k)) (k+fdual[k] {n} k)

--------------------------------------------------------------------------------
-- more facts about n-minus

[n+1]-[k+1] : (n : Nat) (k : Fin₁ n) -> finj (n-minus n k) ≡ n-minus (suc n) (fsuc k)
[n+1]-[k+1] n k with n-minus n k
... | n-k = refl

[n-k≡0]=>[k≡n] : {n : Nat} {k : Fin₁ n} -> n-minus n k ≡ fzero -> k ≡ fn n
[n-k≡0]=>[k≡n] {zero  } {fzero}   _  = refl
[n-k≡0]=>[k≡n] {suc n₁} {fsuc k₁} eq rewrite [n+1]-[k+1] n₁ k₁
  = cong fsuc ([n-k≡0]=>[k≡n] {n₁} {k₁} (finj≡fzero eq))

[n-k≡n]=>[k≡0] : {n : Nat} {k : Fin₁ n} -> n-minus n k ≡ fn n -> k ≡ fzero
[n-k≡n]=>[k≡0] {n} {k} eq with cong (n-minus n) eq
... | eq₂ rewrite (fdual-is-involution {suc n} k) | n-minus-fn-is-0 n = eq₂

--------------------------------------------------------------------------------
-- incrementing and decrementing in the same `Fin₁ n`

data FinPred (n : Nat) (k : Fin₁ n) : Set where
  Pred0 : k ≡ fzero -> FinPred n k
  Pred+ : (l : Fin₁ n) -> finj k ≡ fsuc l -> FinPred n k

-- safely subtracting 1, keeping n
fin-1 : {n : Nat} -> (x : Fin₁ n) -> FinPred n x
fin-1 fzero    = Pred0 refl
fin-1 (fsuc k) = Pred+ (finj k) refl

data FinSucc (n : Nat) (k : Fin₁ n) : Set where
  SuccN : k ≡ fn n -> FinSucc n k
  Succ< : (l : Fin₁ n) -> finj l ≡ fsuc k -> FinSucc n k

-- safely adding 1, keeping n
fin+1 : {n : Nat} -> (x : Fin₁ n) -> FinSucc n x
fin+1 {zero  } fzero     = SuccN refl
fin+1 {suc n₁} fzero     = Succ< f1 refl 
fin+1 {suc n₁} (fsuc k₁) with (fin+1 {n₁} k₁)
... | SuccN prf    = SuccN (cong fsuc prf)
... | Succ< res eq = Succ< (fsuc res) (cong fsuc eq)

--------------------------------------------------------------------------------
-- insert / remove the given element from `{0,1,2...n}`

Fin-insert : {n : Nat} -> (x : Fin (suc n)) -> Fin n -> Fin (suc n)
Fin-insert fzero     y         = fsuc y
Fin-insert (fsuc x₁) fzero     = fzero
Fin-insert (fsuc x₁) (fsuc y₁) = fsuc (Fin-insert x₁ y₁)

Fin-insert[x]≢x : {n : Nat} -> (x : Fin (suc n)) -> (y : Fin n) -> x ≢ Fin-insert x y
Fin-insert[x]≢x fzero     y         = fzero≢fsuc
Fin-insert[x]≢x (fsuc x₁) fzero     = fsuc≢fzero
Fin-insert[x]≢x (fsuc x₁) (fsuc y₁) = (Fin-insert[x]≢x x₁ y₁) ∘ unfsuc

Fin-remove
  :  {n : Nat} -> (x : Fin (suc n))
  -> (y : Fin (suc n)) -> (x ≡ y) ⊎ Fin n 
Fin-remove {zero}   fzero     fzero     = inj₁ refl
Fin-remove {suc n₁} fzero     fzero     = inj₁ refl
Fin-remove {suc n₁} (fsuc x₁) fzero     = inj₂ fzero
Fin-remove {suc n₁} fzero     (fsuc y₁) = inj₂ y₁
Fin-remove {suc n₁} (fsuc x₁) (fsuc y₁) with Fin-remove {n₁} x₁ y₁
... | inj₁ eq = inj₁ (cong fsuc eq)
... | inj₂ z  = inj₂ (fsuc z)

Fin-remove[x]≡inj₁refl : {n : Nat} -> (x : Fin (suc n)) -> Fin-remove x x ≡ inj₁ refl
Fin-remove[x]≡inj₁refl {zero  } fzero     = refl
Fin-remove[x]≡inj₁refl {suc n₁} fzero     = refl
Fin-remove[x]≡inj₁refl {suc n₁} (fsuc y₁) with Fin-remove[x]≡inj₁refl {n₁} y₁
... | eq₁ with Fin-remove y₁ y₁
... | z₁ rewrite eq₁ = refl

-- Agda go home, you are drunk!
Fin-remove-fzero≢fsuc
  :  {n : Nat} (x : Fin₁ (suc n)) (y : Fin n)
  -> Fin-remove x fzero ≢ inj₂ (fsuc y)
Fin-remove-fzero≢fsuc  {suc n₁} fzero     fzero     eq = ⊥-elim (inj₁≢inj₂ eq)
Fin-remove-fzero≢fsuc  {suc n₁} fzero     (fsuc y₁) eq = ⊥-elim (inj₁≢inj₂ eq)
Fin-remove-fzero≢fsuc  {suc n₁} (fsuc x₁) fzero     eq = fzero≢fsuc (uninj₂≡ eq)
Fin-remove-fzero≢fsuc  {suc n₁} (fsuc x₁) (fsuc y₁) eq = fzero≢fsuc (uninj₂≡ eq)

Fin-insert-remove
  :  {n : Nat} -> (x : Fin (suc n))
  -> (y : Fin n) -> Fin-remove x (Fin-insert x y) ≡ inj₂ y
Fin-insert-remove fzero     fzero     = refl
Fin-insert-remove (fsuc x₁) fzero     = refl
Fin-insert-remove fzero     (fsuc y₁) = refl
Fin-insert-remove {suc n₁} (fsuc x₁) (fsuc y₁) with Fin-insert-remove x₁ y₁
... | eq with Fin-remove {n₁} x₁ (Fin-insert x₁ y₁)
...    | either with either
...       | inj₁ bad = ⊥-elim (Fin-insert[x]≢x _ _ bad)
...       | inj₂ z₁  = cong (inj₂ ∘ fsuc) (uninj₂≡ eq)

Fin-remove-insert
  :  {n : Nat} -> (x : Fin₁ n)
  -> (y : Fin₁ n) -> [ const x , Fin-insert x ]′ (Fin-remove x y) ≡ y
Fin-remove-insert {zero}   fzero     fzero     = refl
Fin-remove-insert {suc n₁} fzero     fzero     = refl
Fin-remove-insert {suc n₁} fzero     (fsuc y₁) = refl
Fin-remove-insert {suc n₁} (fsuc x₁) fzero     with Fin-remove {suc n₁} (fsuc x₁) fzero
... | inj₂ fzero     = refl
... | inj₂ (fsuc y₂) = refl
... | inj₁ bad       = ⊥-elim (fsuc≢fzero bad)
Fin-remove-insert {suc n₁} (fsuc x₁) (fsuc y₁) with Fin-remove-insert {n₁} x₁ y₁
... | eq with Fin-remove {n₁} x₁ y₁
...    | inj₁ _  = cong fsuc eq
...    | inj₂ z₁ = cong fsuc eq

--------------------------------------------------------------------------------

