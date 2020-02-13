

open import Data.Nat
open import Data.Nat.Properties

open import Data.Empty    using ( ⊥ ; ⊥-elim )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ )

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

Nat : Set
Nat = ℕ

-- just a shorthand for composing equalities
infixr 3 _∙_
_∙_ : {A : Set} -> {a b c : A} -> (a ≡ b) -> (b ≡ c) -> (a ≡ c)
_∙_ = trans

--------------------------------------------------------------------------------

uninj₁≡ : {A B : Set} -> {a₁ a₂ : A} -> _≡_ {A = A ⊎ B} (inj₁ a₁) (inj₁ a₂) -> a₁ ≡ a₂
uninj₁≡ refl = refl

uninj₂≡ : {A B : Set} -> {b₁ b₂ : B} -> _≡_ {A = A ⊎ B} (inj₂ b₁) (inj₂ b₂) -> b₁ ≡ b₂
uninj₂≡ refl = refl

inj₁≢inj₂ : {A B : Set} -> {a : A} -> {b : B} -> inj₁ a ≢ inj₂ b
inj₁≢inj₂ ()
