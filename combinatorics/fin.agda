
-- The sets {0,1,...,n-1} 

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec.Base

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )

open import Relation.Binary.PropositionalEquality

open import useful

--------------------------------------------------------------------------------

-- The set {0,1,2...,n-1}
data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

-- The set {0,1,2...,n}
Fin₁ : Nat -> Set
Fin₁ n = Fin (suc n)

--------------------------------------------------------------------------------

-- embedding of `Fin n` into `Fin (n+1)`
finj : {n : Nat} -> Fin n -> Fin (suc n)
finj fzero    = fzero
finj (fsuc f) = fsuc (finj f)

{-# INJECTIVE finj #-}

-- n ∈ {0,...,n}
fn : (n : Nat) -> Fin₁ n
fn zero    = fzero
fn (suc m) = fsuc (fn m)

--------------------------------------------------------------------------------

unfsuc : {n : Nat} {x y : Fin n} -> fsuc x ≡ fsuc y -> x ≡ y
unfsuc refl = refl

fzero≢fsuc : {n : Nat} {k : Fin n} -> fzero ≡ fsuc k -> ⊥
fzero≢fsuc ()

fsuc≢fzero : {n : Nat} {k : Fin n} -> fsuc k ≡ fzero -> ⊥
fsuc≢fzero ()

finj≡fzero : {n : Nat} {k : Fin₁ n} -> finj k ≡ fzero -> k ≡ fzero
finj≡fzero {n} {fzero} refl = refl

finj≢fn : {n : Nat} (k : Fin n) -> finj k ≢ fn n
finj≢fn {suc n₁} fzero     = fzero≢fsuc 
finj≢fn {suc n₁} (fsuc k₁) = λ eq -> finj≢fn {n₁} k₁ (unfsuc eq)

--------------------------------------------------------------------------------

-- predecessor (n decreases!)
fpred : {n : Nat} -> (x : Fin (suc n)) -> (x ≡ fzero) ⊎ Fin n
fpred fzero    = inj₁ refl
fpred (fsuc k) = inj₂ k

-- projecting down `Fin (n+1)` onto `Fin n`
fproj : {n : Nat} -> (k : Fin (suc n)) -> (k ≡ fn n) ⊎ Fin n 
fproj {zero}   fzero     = inj₁ refl
fproj {suc n₁} fzero     = inj₂ fzero
fproj {suc n₁} (fsuc k₁) with fproj {n₁} k₁
... | inj₂ k₂ = inj₂ (fsuc k₂)
... | inj₁ eq = inj₁ (cong fsuc eq)

fpred-fsuc : {n : Nat} -> (k : Fin n) -> fpred (fsuc k) ≡ inj₂ k
fpred-fsuc k = refl

fproj-finj : {n : Nat} -> (k : Fin n) -> fproj (finj k) ≡ inj₂ k
fproj-finj fzero     = refl
fproj-finj (fsuc k₁) with fproj (finj k₁) | inspect fproj (finj k₁)
... | inj₁ bad | _      = ⊥-elim (finj≢fn k₁ bad)
... | inj₂ k₂  | [ eq ] with fproj-finj k₁
...   | prf = cong inj₂ (cong fsuc (uninj₂≡ (sym eq ∙ prf)))

--------------------------------------------------------------------------------

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero    = zero
finToNat (fsuc f) = suc (finToNat f)

finToNat-finj : {n : Nat} -> (k : Fin n) -> finToNat (finj k) ≡ finToNat k
finToNat-finj {n}      fzero     = refl
finToNat-finj {suc n₁} (fsuc k₁) rewrite finToNat-finj k₁ = refl

finToNat-fn : (n : Nat) -> finToNat (fn n) ≡ n
finToNat-fn zero     = refl
finToNat-fn (suc n₁) = cong suc (finToNat-fn n₁)

--------------------------------------------------------------------------------
-- enumerating finite sets

-- | Enumerates all elements of `Fin n`
enumerateFin : (n : Nat) -> Vec (Fin n) n
enumerateFin zero    = []
enumerateFin (suc n) = fzero ∷ map fsuc (enumerateFin n)

enumerateFin₁ : (n : Nat) -> Vec (Fin₁ n) (suc n)
enumerateFin₁ n = enumerateFin (suc n)

--------------------------------------------------------------------------------
-- `Fin 0` is empty and `Fin 1` is unit

Fin₀-elim : {A : Set} -> Fin 0 -> A
Fin₀-elim ()

Fin₁-singleton : (f : Fin 1) -> f ≡ fzero
Fin₁-singleton fzero = refl

--------------------------------------------------------------------------------
-- some concrete numbers (useful for trying out things)

f0 : {n : Nat} -> Fin (suc n)
f1 : {n : Nat} -> Fin (suc (suc n))
f2 : {n : Nat} -> Fin (suc (suc (suc n)))
f3 : {n : Nat} -> Fin (suc (suc (suc (suc n))))
f4 : {n : Nat} -> Fin (suc (suc (suc (suc (suc n)))))

f0 = fzero  
f1 = fsuc f0
f2 = fsuc f1
f3 = fsuc f2
f4 = fsuc f3

--------------------------------------------------------------------------------
-- heterogeneous equality for Fin

data _~_ : {n m : Nat} -> Fin n -> Fin m -> Set where
  ~zero : {n m : Nat} -> fzero {n} ~ fzero {m}
  ~suc  : {n m : Nat} {x : Fin n} {y : Fin m} -> x ~ y -> fsuc x ~ fsuc y 

~inj : {n m : Nat} {x : Fin n} {y : Fin m} -> x ~ y -> finj x ~ finj y 
~inj ~zero      = ~zero
~inj (~suc heq) = ~suc (~inj heq)

~unsuc : {n m : Nat} {a : Fin n} {b : Fin m} -> fsuc a ~ fsuc b -> a ~ b
~unsuc (~suc heq) = heq

x~finjx : {n : Nat} -> (x : Fin n) -> x ~ finj x
x~finjx fzero    = ~zero
x~finjx (fsuc x) = ~suc (x~finjx x)

~fzero=>≡fzero : {n m : Nat} {k : Fin₁ n} -> (k ~ fzero {m}) -> (k ≡ fzero {n})
~fzero=>≡fzero ~zero = refl

--------------------------------------------------------------------------------

~⇒≡Fin : {n : Nat} {x y : Fin n} -> x ~ y -> x ≡ y
~⇒≡Fin ~zero      = refl
~⇒≡Fin (~suc heq) = cong fsuc (~⇒≡Fin heq)

~⇒≡Nat : {n m : Nat} {x : Fin n} {y : Fin m} -> x ~ y -> finToNat x ≡ finToNat y
~⇒≡Nat ~zero      = refl
~⇒≡Nat (~suc heq) = cong suc (~⇒≡Nat heq)

--------------------------------------------------------------------------------
-- out-of-bound with heterogeneous equality

-- k < n, meaning that it cannot be equal to n.
~contra : {A : Set} {n : Nat} {k : Fin n} -> k ~ (fn n) -> A
~contra (~suc heq) = ~contra heq

-- k <= n meaning that it cannot be equal to (n+1)
~contra₁ : {A : Set} {n : Nat} {k : Fin₁ n} -> k ~ fsuc (fn n) -> A
~contra₁ {A} {n} {k} heq = ~contra {A} {suc n} {k} heq

--------------------------------------------------------------------------------
