
-- divisibility, divMod

open import Data.Empty
open import Data.Sum     using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )

open import Relation.Binary.PropositionalEquality

open import Induction.WellFounded

open import nat

--------------------------------------------------------------------------------
-- DIVISIBILITY

-- NB: this is \| and not | (the latter is already used in Agda syntax)
record _∣_ (k n : Nat) : Set where
  constructor mkDivBy
  field
    quotient : Nat
    proof    : k * quotient ≡ n
    
n∣0 : (n : Nat) -> n ∣ zero
n∣0 n = mkDivBy 0 (n*0 n)

n∣n : (n : Nat) -> n ∣ n
n∣n n = mkDivBy 1 (n*1 n)

[n/n]≡1 : {n : Nat} -> (n > 0) -> (div : n ∣ n) -> _∣_.quotient div ≡ 1
[n/n]≡1 {n} pos (mkDivBy q eq) with eq ∙ sym (n*1 n)
... | eq₂ = *-cancel-l pos eq₂

div-refl : (n : Nat) -> n ∣ n
div-refl = n∣n

div-trans : {a b c : Nat} -> a ∣ b -> b ∣ c -> a ∣ c
div-trans {a} {b} {c} (mkDivBy q₁ eq₁) (mkDivBy q₂ eq₂) = mkDivBy q₃ eq₃ where
  q₃  = q₁ * q₂
  eq₃ = sym (*-assoc {a} {q₁} {q₂}) ∙ (≡* q₂ eq₁) ∙ eq₂

div-antisym : {n m : Nat} -> n ∣ m -> m ∣ n -> n ≡ m
div-antisym {zero  } {zero  } _    _    = refl
div-antisym {suc n₁} {suc m₁} div₁ div₂ = proof where
  div₃ = div-trans div₁ div₂
  prf  = [n/n]≡1 (0<S n₁) div₃
  q₁ = _∣_.quotient div₁
  q₂ = _∣_.quotient div₂
  proof : suc n₁ ≡ suc m₁
  proof with (*≡1 {q₁} {q₂} prf)
  ... | (q₁≡1 , q₂≡1) with _∣_.proof div₁
  ... | eq rewrite q₁≡1 | (n*1 n₁) = eq

div⇒≤ : {a b : Nat} -> a ∣ b -> (b ≡ 0) ⊎ (a ≤ b)
div⇒≤ {a} {zero} _ = inj₁ refl
div⇒≤ {a} {b} (mkDivBy q eq) rewrite sym eq with a≤a*b a q
... | inj₁ eq₀ rewrite eq₀ = inj₁ (n*0 a) 
... | inj₂ ineq            = inj₂ ineq

div-+ : {a b d : Nat} -> d ∣ a -> d ∣ b -> d ∣ (a + b)
div-+ {a} {b} {d} (mkDivBy a₁ prf₁) (mkDivBy a₂ prf₂)
  = mkDivBy (a₁ + a₂) (*+-distrib {d} {a₁} {a₂} ∙ (prf₁ ⊕ prf₂))

div-*n : {a d : Nat} -> (n : Nat) -> d ∣ a -> d ∣ (a * n)
div-*n {a} {d} n (mkDivBy q prf) 
  = mkDivBy (q * n) (sym (*-assoc {d} {q} {n}) ∙ (≡* n prf))

div-n* : {a d : Nat} -> (n : Nat) -> d ∣ a -> d ∣ (n * a)
div-n* {a} {d} n div with div-*n n div
... | mkDivBy q prf = mkDivBy q (prf ∙ *-comm {a} {n})

div-minus : {a b d : Nat} -> (ge : a ≥ b) -> d ∣ a -> d ∣ b -> d ∣ minus a b ge
div-minus {a} {b} {d} ge (mkDivBy a₁ prf₁) (mkDivBy b₁ prf₂) with Nat-case d
... | inj₁ dzero rewrite dzero | sym prf₁ | sym prf₂ = n∣0 0
... | inj₂ dpos  with difference a b ge
...   | a-b , eq rewrite sym prf₁ | sym prf₂ with *-≤-cancel-l dpos ge
...     | ge₁ with difference a₁ b₁ ge₁
...     | a₁-b₁ , eq₁ with *≡ d eq₁
...     | h₁ rewrite *+-distrib {d} {b₁} {a₁-b₁} with sym h₁ ∙ eq
...     | h₂ =  mkDivBy a₁-b₁ (+-cancel-l {d * b₁} h₂)

div-unplus : {a b d : Nat} -> d ∣ (a + b) -> d ∣ b -> d ∣ a
div-unplus {a} {b} {d} div₁ div₂ with [a+b-b]≡a a b
... | eq with div-minus {a + b} {b} {d} (b≤a+b a b) div₁ div₂
... | div₃ rewrite eq = div₃

--------------------------------------------------------------------------------
-- * MODULO

-- The specification of `divMod a n`.
-- First component is the quotient, second is the remainder + we have proofs.
DivMod : Nat -> Nat -> Set
DivMod a n = Σ (Nat × Nat) (λ qr -> (proj₂ qr < n) × (a ≡ proj₂ qr + proj₁ qr * n)) 

DivMod₁ : Nat -> Nat -> Set
DivMod₁ a n₁ = DivMod a (suc n₁)

record DivModStep₁ (a n₁ : Nat) : Set where
  constructor DMS
  field
    q : Nat
    r : Nat
    c : Nat
    r+c : r + c ≡ n₁
    eq  : a ≡ r + q * suc n₁

fromDivModStep₁ : (a n₁ : Nat) -> DivModStep₁ a n₁ -> DivMod₁ a n₁
fromDivModStep₁ a n₁ (DMS q r c eq₁ eq₂) = ( (q , r) , (S≤S (a≤a+b r c ≤∙≡ eq₁) , eq₂ ))

divmod-step : (b n₁ : Nat) -> DivModStep₁ b n₁ -> DivModStep₁ (suc b) n₁
divmod-step b n₁ (DMS q r zero     r+c eq) rewrite (n+0 r) | r+c
                                           = DMS (suc q)     0  n₁ refl                     (cong suc eq)
divmod-step b n₁ (DMS q r (suc c₁) r+c eq) = DMS      q (suc r) c₁ (sym (n+suc r c₁) ∙ r+c) (cong suc eq)

-- a modulo (suc n₁)
divMod-helper : (a n₁ : Nat) -> DivModStep₁ a n₁
divMod-helper a n₁ = go a 0 (sym (n+0 a)) (DMS 0 0 n₁ refl refl) where
  go : (a↓ a↑ : Nat) -> a ≡ a↓ + a↑ -> DivModStep₁ a↑ n₁ -> DivModStep₁ a n₁
  go zero a↑     eq dms rewrite eq = dms
  go (suc a↓) a↑ eq dms = go a↓ (suc a↑) (eq ∙ sym (n+suc a↓ a↑)) (divmod-step a↑ n₁ dms)

divMod₊w/proof : (a n : Nat) -> (n > 0) -> DivMod a n
divMod₊w/proof a n pos with (pos⇒suc {n} pos)
... | (n₁ , eq) rewrite eq = fromDivModStep₁ a n₁ (divMod-helper a n₁)

mod₊w/proof : (a n : Nat) -> (n > 0) -> Σ Nat (λ r -> r < n)
mod₊w/proof a n pos with divMod₊w/proof a n pos
... | ((q , r) , (prf , _)) = (r , prf)

divMod₊ : (a n : Nat) -> (n > 0) -> Nat × Nat
divMod₊ a n pos = proj₁ (divMod₊w/proof a n pos)

div₊ : (a n : Nat) -> (n > 0) -> Nat
div₊ a n pos = proj₁ (divMod₊ a n pos)

mod₊ : (a n : Nat) -> (n > 0) -> Nat
mod₊ a n pos = proj₂ (divMod₊ a n pos)

-- there shouldn't be any need for this in theory
-- (as you can see from the fact that the proofs are trivial),
-- but practice says different...
divMod₊w/proof′
  : (a n : Nat) -> (pos : n > 0)
  -> Σ (DivMod a n) (λ dm -> div₊ a n pos ≡ proj₁ (proj₁ dm) × mod₊ a n pos ≡ proj₂ (proj₁ dm))
divMod₊w/proof′ a n pos = (divMod₊w/proof a n pos , (refl , refl) )

divMod : Nat -> Nat -> Nat × Nat
divMod a zero     = (zero , zero)
divMod a (suc n₁) = divMod₊ a (suc n₁) (0<S n₁)

div : Nat -> Nat -> Nat
div a zero     = zero
div a (suc n₁) = div₊ a (suc n₁) (0<S n₁)

mod : Nat -> Nat -> Nat
mod a zero     = zero
mod a (suc n₁) = mod₊ a (suc n₁) (0<S n₁)

infix 7 _%_
_%_ : Nat -> Nat -> Nat
_%_ = mod

--------------------------------------------------------------------------------
