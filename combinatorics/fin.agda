
{-# OPTIONS --rewriting #-}

-- The sets {0,1,...,n-1} 

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec.Base

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product  using ( Σ ; _,_ )

open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

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

finj≡fsuc : {n : Nat} {k l : Fin₁ n} -> finj k ≡ fsuc l -> Σ (Fin n) (λ k₁ -> finj k₁ ≡ l)
finj≡fsuc {n} {fsuc k₁} refl = (k₁ , refl)

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
-- partitioning {0..n} into two parts

-- `(a,b)` pairs with the equality `a + b ≡ n`
data [A+B]≡ : Nat -> Set where
  z+z  : [A+B]≡ zero
  sucA : {n : Nat} -> [A+B]≡ n -> [A+B]≡ (suc n)
  sucB : {n : Nat} -> [A+B]≡ n -> [A+B]≡ (suc n)

postulate
  sucA∘sucB≡sucB∘sucA : {n : Nat} -> {ab : [A+B]≡ n} -> sucA (sucB ab) ≡ sucB (sucA ab)  

{-# REWRITE sucA∘sucB≡sucB∘sucA #-}

πA : {n : Nat} -> [A+B]≡ n -> Nat
πA z+z       = zero
πA (sucA ab) = suc (πA ab)
πA (sucB ab) =      πA ab 

πB : {n : Nat} -> [A+B]≡ n -> Nat
πB z+z       = zero
πB (sucA ab) =      πB ab 
πB (sucB ab) = suc (πB ab) 

[A+B]-proof : {n : Nat} -> (ab : [A+B]≡ n) -> πA ab + πB ab ≡ n
[A+B]-proof {n} z+z        = refl
[A+B]-proof {n} (sucA ab₁) = cong suc ([A+B]-proof ab₁) 
[A+B]-proof {n} (sucB ab₁) = n+suc _ _ ∙ cong suc ([A+B]-proof ab₁)

--------------------------------------------------------------------------------

[N+0] : (n : Nat) -> [A+B]≡ n
[N+0] zero     = z+z
[N+0] (suc n₁) = sucA ([N+0] n₁)

[0+N] : (n : Nat) -> [A+B]≡ n
[0+N] zero     = z+z
[0+N] (suc n₁) = sucB ([0+N] n₁)

--------------------------------------------------------------------------------
-- pairs vs Fin

πA′ : {n : Nat} -> [A+B]≡ n -> Fin₁ n
πA′ z+z       = fzero
πA′ (sucA ab) = fsuc (πA′ ab)
πA′ (sucB ab) = finj (πA′ ab) 

πB′ : {n : Nat} -> [A+B]≡ n -> Fin₁ n
πB′ z+z       = fzero
πB′ (sucA ab) = finj (πB′ ab) 
πB′ (sucB ab) = fsuc (πB′ ab) 

--------------------------------------------------------------------------------

-- maps k to a
Fin₁⇒[A+B] : {n : Nat} -> Fin₁ n -> [A+B]≡ n
Fin₁⇒[A+B] {n}      fzero     = [0+N] n
Fin₁⇒[A+B] {suc n₁} (fsuc k₁) = sucA (Fin₁⇒[A+B] {n₁} k₁)

finj⇒[A+B] : {n : Nat} -> (k : Fin₁ n) -> Fin₁⇒[A+B] (finj k) ≡ sucB (Fin₁⇒[A+B] k)
finj⇒[A+B] {zero  } fzero     = refl
finj⇒[A+B] {suc n₁} fzero     = refl
finj⇒[A+B] {suc n₁} (fsuc k₁) with finj⇒[A+B] {n₁} k₁
... | prf₁ rewrite prf₁ = refl                -- we use the rewrite rule here!!!
 
-- maps a to k
[A+B]⇒Fin₁ : {n : Nat} -> [A+B]≡ n -> Fin₁ n
[A+B]⇒Fin₁ = πA′

Fin₁⟲[A+B] : {n : Nat} -> (x : Fin₁ n) -> [A+B]⇒Fin₁ (Fin₁⇒[A+B] x) ≡ x
Fin₁⟲[A+B] {zero  } fzero     = refl
Fin₁⟲[A+B] {suc n₁} fzero     = cong finj (Fin₁⟲[A+B] {n₁} fzero)
Fin₁⟲[A+B] {suc n₁} (fsuc k₁) = cong fsuc (Fin₁⟲[A+B] {n₁} k₁   )

[A+B]⟲Fin₁ : {n : Nat} -> (ab : [A+B]≡ n) -> Fin₁⇒[A+B] ([A+B]⇒Fin₁ ab) ≡ ab
[A+B]⟲Fin₁ {zero  } z+z        = refl
[A+B]⟲Fin₁ {suc n₁} (sucA ab₁) = cong sucA ([A+B]⟲Fin₁ {n₁} ab₁) 
[A+B]⟲Fin₁ {suc n₁} (sucB ab₁) with [A+B]⟲Fin₁ {n₁} ab₁
... | prf₁ = finj⇒[A+B] (πA′ ab₁) ∙ cong sucB prf₁

--------------------------------------------------------------------------------
