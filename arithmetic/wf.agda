
-- Well-founded recursion and induction for Nat

open import Data.Empty
open import Data.Sum     using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )

open import Relation.Binary.PropositionalEquality
-- open import Induction.WellFounded

open import nat

--------------------------------------------------------------------------------
-- A different definition of ordering

-- This is more convenient for proving well-foundedness.
-- Note: this is \' and not '. 
data _≤′_ : Nat -> Nat -> Set where
  n≤′n : {n   : Nat} -> n ≤′ n
  n≤′S : {n m : Nat} -> n ≤′ m -> n ≤′ suc m

_<′_ : Nat -> Nat -> Set
_<′_ n m = suc n ≤′ m

≤′-suc : {n m : Nat} -> n ≤′ m -> suc n ≤′ suc m 
≤′-suc (n≤′n {n}) = n≤′n {suc n}
≤′-suc (n≤′S le ) = n≤′S (≤′-suc le)

--------------------------------------------------------------------------------
-- the new ordering is equivalent to the old one

≤⇒≤′ : {n m : Nat} -> n ≤ m -> n ≤′ m
≤⇒≤′ (0≤n  zero   ) = n≤′n {zero}
≤⇒≤′ (0≤n (suc n₁)) = n≤′S (≤⇒≤′ (0≤n n₁))
≤⇒≤′ (S≤S le      ) = ≤′-suc (≤⇒≤′ le)

≤′⇒≤ : {n m : Nat} -> n ≤′ m -> n ≤ m
≤′⇒≤ (n≤′n {n}) = n≤n n
≤′⇒≤ (n≤′S le ) = ≤S (≤′⇒≤ le)

--------------------------------------------------------------------------------
-- the notion of well-foundedness

-- a relation
Rel : Set -> Set₁
Rel A = A -> A -> Set

-- accessibility:
-- `x` is accessible if all smaller elements are accessible
data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : (forall y -> y < x -> Acc _<_ y) -> Acc _<_ x

-- well-foundedness
WellFounded : {A : Set} -> Rel A -> Set
WellFounded {A} _<_ = (x : A) -> Acc _<_ x

--------------------------------------------------------------------------------
-- Nat with _<′_ is well-founded, meaning there is no infinite decreasing chain.
-- constructive version: `n` is accessible if all smaller elements are accessible.
-- 

Nat-wf : WellFounded _<′_
Nat-wf n = acc (access n) where
  access : (n : Nat) -> (y : Nat) -> y <′ n -> Acc _<′_ y 
  access (suc n₁) .n₁  n≤′n      = acc (access n₁)
  access (suc n₁)  y₁ (n≤′S le₁) = access n₁ y₁ le₁

--------------------------------------------------------------------------------
-- well-founded recursion for Nat

-- a single recursive call on Nat (it can use anything smaller)
RecCall : Set -> Nat -> Set
RecCall A n = (y : Nat) -> y <′ n -> A

-- well-founded recursion on Nat
-- (the user can use the recursive call as many times as they want)
Nat-wfrec : {A : Set} -> ((n : Nat) -> RecCall A n -> A) -> Nat -> A 
Nat-wfrec {A} user n = go n (Nat-wf n) where
  go : (n : Nat) -> Acc _<′_ n -> A
  go n (acc β) = user n (λ y prf -> go y (β y prf))

{-
unfold-Nat-wfrec
 :  {A : Set} -> (user : (x : Nat) -> RecCall A x -> A) -> (n : Nat)
 -> Nat-wfrec user n ≡ user n (λ y _ -> Nat-wfrec user y)
unfold-Nat-wfrec user n with Nat-wf n
... | acc β = ?
-}

--------------------------------------------------------------------------------
-- well-founded induction for Nat

-- dependent version of the above
IndCall : (Nat -> Set) -> Nat -> Set
IndCall P n = (y : Nat) -> y <′ n -> P y

-- well-founded induction on nat
Nat-wfind : {P : Nat -> Set} -> ((n : Nat) -> IndCall P n -> P n) -> (m : Nat) -> P m 
Nat-wfind {P} user n = go n (Nat-wf n) where
  go : (n : Nat) -> Acc _<′_ n -> P n
  go n (acc β) = user n (λ y prf -> go y (β y prf))

--------------------------------------------------------------------------------

