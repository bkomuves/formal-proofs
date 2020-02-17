

open import Data.Nat
open import Data.Nat.Properties

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

-- just a shorthand for composing equalities
infixr 3 _∙_
_∙_ : {A : Set} -> {a b c : A} -> (a ≡ b) -> (b ≡ c) -> (a ≡ c)
_∙_ = trans

--------------------------------------------------------------------------------

Nat : Set
Nat = ℕ

n+0 : (n : Nat) -> n + 0 ≡ n
n+0 n = +-identityʳ n

n+1 : (n : Nat) -> n + 1 ≡ suc n
n+1 n = +-suc n 0 ∙ cong suc (n+0 n)  

n+suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
n+suc = +-suc

--------------------------------------------------------------------------------

uninj₁≡ : {A B : Set} -> {a₁ a₂ : A} -> _≡_ {A = A ⊎ B} (inj₁ a₁) (inj₁ a₂) -> a₁ ≡ a₂
uninj₁≡ refl = refl

uninj₂≡ : {A B : Set} -> {b₁ b₂ : B} -> _≡_ {A = A ⊎ B} (inj₂ b₁) (inj₂ b₂) -> b₁ ≡ b₂
uninj₂≡ refl = refl

inj₁≢inj₂ : {A B : Set} -> {a : A} -> {b : B} -> inj₁ a ≢ inj₂ b
inj₁≢inj₂ ()


--------------------------------------------------------------------------------
