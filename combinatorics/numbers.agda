

open import Data.Nat
open import Data.Nat.Properties

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product  using ( Σ ; _,_ )

open import Relation.Binary.PropositionalEquality

open import useful
open import fin
open import fin-extras

--------------------------------------------------------------------------------
-- The binomial coefficients (based on Pascal's triangle)

-- The symmetric version: `binomial₂ a b = binomial (a+b) b`
-- This is much easier to work with than the asymmetric version 
binomial₂ : (a b : Nat)  -> Nat
binomial₂ zero     _        = 1
binomial₂ _        zero     = 1
binomial₂ (suc a₁) (suc b₁) = binomial₂ (suc a₁) b₁ + binomial₂ a₁ (suc b₁)

--------------------------------------------------------------------------------
-- asymmetric version

-- | note: this actually an extremely slow implementation
-- (because of the exploding recursion)
binomial : (n : Nat) -> (k : Fin₁ n) -> Nat
binomial zero    _          = 1
binomial (suc _ ) fzero     = 1
binomial (suc n₁) (fsuc k₁) with fin+1 k₁
... | SuccN prf   = binomial n₁ k₁
... | Succ< k₂ _  = binomial n₁ k₁ + binomial n₁ k₂

n-choose-0 : (n : Nat) -> binomial n fzero ≡ 1
n-choose-0 zero    = refl
n-choose-0 (suc _) = refl

n-choose-n : (n : Nat) -> binomial n (fn n) ≡ 1
n-choose-n zero     = refl
n-choose-n (suc n₁) with fin+1 (fn n₁)
... | SuccN prf   = n-choose-n n₁
... | Succ< _ eq with finj≡fsuc eq
...    | (l₁ , eq₁) = ⊥-elim (finj≢fn l₁ eq₁)

--------------------------------------------------------------------------------

-- the usual factorial
factorial : Nat -> Nat
factorial zero    = 1
factorial (suc m) = (suc m) * factorial m

--------------------------------------------------------------------------------
-- the rising factorial

-- the rising factorial
risingFac : Nat -> Nat -> Nat
risingFac a zero    = 1
risingFac a (suc m) = a * risingFac (suc a) m

risingFac-1 : (a : Nat) -> risingFac a 1 ≡ a
risingFac-1 a = *-identityʳ a

risingFac-append : (a n m : Nat) -> risingFac a n * risingFac (a + n) m ≡ risingFac a (n + m)
risingFac-append a zero     m rewrite +-identityʳ a | +-identityʳ (risingFac a m) = refl
risingFac-append a (suc n₁) m
  rewrite *-assoc a (risingFac (suc a) n₁) (risingFac (a + suc n₁) m)
  with risingFac-append (suc a) n₁ m
... | eq rewrite n+suc a n₁ = cong (λ b -> a * b) eq 

risingFac-suc-right : (a n : Nat) -> risingFac a (suc n) ≡ risingFac a n * (a + n)
risingFac-suc-right a n
  = cong (risingFac a) (sym (n+1 n))
  ∙ sym (risingFac-append a n 1)
  ∙ cong (λ r -> risingFac a n * r) (*-identityʳ (a + n))

risingFac-suc-left : (a n : Nat) -> risingFac a (suc n) ≡ a * risingFac (suc a) n 
risingFac-suc-left a n = refl

risingFac-suc-lr : (a n : Nat) -> a * risingFac (suc a) n ≡ risingFac a n * (a + n)
risingFac-suc-lr a n
  = sym (risingFac-suc-left a n)
  ∙ risingFac-suc-right a n

risingFac1≡factorial : (n : Nat) -> risingFac 1 n ≡ factorial n
risingFac1≡factorial zero     = refl
risingFac1≡factorial (suc n₁)
  = risingFac-suc-right 1 n₁
  ∙ cong (λ l -> l * suc n₁) (risingFac1≡factorial n₁)  
  ∙ *-comm (factorial n₁) (suc n₁)

[a+b]!/b! : Nat -> Nat -> Nat
[a+b]!/b! a b = risingFac (suc b) a

[a+b]!/a! : Nat -> Nat -> Nat
[a+b]!/a! a b = risingFac (suc a) b

n!/k! : (n : Nat) -> (k : Fin₁ n) -> Nat
n!/k! n k = risingFac (suc (finToNat k)) (finToNat (n-minus n k))

n!/n!≡1 : (n : Nat) -> n!/k! n (fn n) ≡ 1
n!/n!≡1 zero     = refl
n!/n!≡1 (suc n₁) rewrite n-minus-fn-is-0 n₁ = refl

--------------------------------------------------------------------------------
-- the falling factorial

fallingFac : (n : Nat) -> (k : Fin₁ n) -> Nat
fallingFac _        fzero     = 1
fallingFac (suc n₁) (fsuc k₁) = suc n₁ * fallingFac n₁ k₁

fallingFac≡n!/[n-k]! : (n : Nat) -> (k : Fin₁ n) -> fallingFac n k ≡ n!/k! n (n-minus n k)
fallingFac≡n!/[n-k]! n        fzero     = sym (n!/n!≡1 n) 
fallingFac≡n!/[n-k]! (suc n₁) (fsuc k₁)
  rewrite fallingFac≡n!/[n-k]! n₁ k₁
        | fdual-finj (fdual k₁)
        | fdual-is-involution k₁
        | finToNat-finj (fdual k₁)
        | *-comm (suc n₁) (risingFac (suc (finToNat (fdual k₁))) (finToNat k₁))
   = cong (λ r -> risingFac (suc (finToNat (fdual k₁))) (finToNat k₁) * suc r) (sym (fdual[k]+k {n₁} k₁))
   ∙ (sym (risingFac-suc-lr (suc (finToNat (fdual k₁))) (finToNat k₁)))

--------------------------------------------------------------------------------
