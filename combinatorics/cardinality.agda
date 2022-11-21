
-- cardinality of finite sets

open import Data.Bool using ( Bool; false; true)
import Data.Bool 

open import Data.Nat
open import Data.Nat.Properties

open import Data.Vec.Base

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum.Base  using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product   using ( _×_ ; _,_ ; proj₁ ; proj₂ ; Σ )
 
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import useful
open import fin
open import fin-extras
open import bijection

--------------------------------------------------------------------------------

hasSize : Set -> Nat -> Set
hasSize A n = A ⇔ Fin n

infix 2 _⊢_
_⊢_ : Set -> Nat -> Set
A ⊢ n = hasSize A n

⇔-size : {A B : Set} -> {n : Nat} -> (A ⇔ B) -> A ⊢ n -> B ⊢ n
⇔-size φ ψ = flip⇔ φ ⊙ ψ

-- enumerate finite sets
enumerate : {A : Set} -> {n : Nat} -> A ⊢ n -> Vec A n
enumerate {A} {n} φ = Data.Vec.Base.map (Iso.g φ) (enumerateFin n)

--------------------------------------------------------------------------------
-- cardinality is well-defined 

Fin-subst-Iso : {n m : Nat} -> n ≡ m -> Fin n ⇔ Fin m
Fin-subst-Iso {n} {m} refl = isoRefl

-- the isomorphism which maps 0 to y₀, and otherwise leaves the rest untouched
Fin-insert-Iso : {n : Nat} -> Fin₁ n -> Fin₁ n ⇔ Fin₁ n
Fin-insert-Iso {n} y₀ = mkIso f g prf₁ prf₂ where
  f : Fin₁ n -> Fin₁ n
  g : Fin₁ n -> Fin₁ n
  prf₁ : {x : Fin₁ n} -> g (f x) ≡ x
  prf₂ : {y : Fin₁ n} -> f (g y) ≡ y

  f fzero     = y₀
  f (fsuc x₁) = Fin-insert y₀ x₁

  g y with Fin-remove y₀ y
  ... | inj₁ _ = fzero
  ... | inj₂ x = fsuc x

  prf₁ {fzero  } rewrite Fin-remove[x]≡inj₁refl y₀ = refl
  prf₁ {fsuc x₁} with Fin-insert-remove y₀ x₁
  ... | prf with Fin-remove y₀ (Fin-insert y₀ x₁)
  ...   | inj₁ _ = ⊥-elim (inj₁≢inj₂ prf)
  ...   | inj₂ x = cong fsuc (uninj₂≡ prf)

  prf₂ {y} with Fin-remove-insert y₀ y
  ... | prf with Fin-remove y₀ y
  ...   | inj₁ eq = eq
  ...   | inj₂ z  = prf

-- a small lemmas
Fin-insert-Iso-y₀ : {n : Nat} -> (y₀ : Fin₁ n) -> Iso.g (Fin-insert-Iso {n} y₀) y₀ ≡ fzero
Fin-insert-Iso-y₀ {n} y₀ with Fin-remove[x]≡inj₁refl y₀
... | prf with Fin-remove y₀ y₀
...   | inj₁ refl = refl

-- we can remove zero if the isomorphism leaves it invariant
unsuc-Fin-iso-v1 : {n m : Nat}
  -> (φ : Fin (suc n) ⇔ Fin (suc m))
  -> (Iso.f φ fzero ≡ fzero)
  -> Fin n ⇔ Fin m
unsuc-Fin-iso-v1 {n} {m} φ z→z = mkIso f g prf₁ prf₂ where

  z←z : Iso.g φ fzero ≡ fzero
  z←z with cong (Iso.g φ) z→z
  ... | eq rewrite Iso.prf₁ φ {fzero} = sym eq

  s→s : (a : Fin n) -> Iso.f φ (fsuc a) ≢ fzero
  s→s a eq with cong (Iso.g φ) eq
  ... | eq₂ rewrite z←z | Iso.prf₁ φ {fsuc a} = fsuc≢fzero eq₂

  s←s : (b : Fin m) -> Iso.g φ (fsuc b) ≢ fzero
  s←s b eq with cong (Iso.f φ) eq
  ... | eq₂ rewrite z→z | Iso.prf₂ φ {fsuc b} = fsuc≢fzero eq₂

  f : Fin n -> Fin m
  g : Fin m -> Fin n
  prf₁ : {x : Fin n} -> g (f x) ≡ x
  prf₂ : {y : Fin m} -> f (g y) ≡ y

  f x with Iso.f φ (fsuc x) | inspect (Iso.f φ) (fsuc x)
  ... | fsuc y | _     = y
  ... | fzero  | [ p ] = ⊥-elim (s→s x p)
  g y with Iso.g φ (fsuc y) | inspect (Iso.g φ) (fsuc y)
  ... | fsuc x | _     = x
  ... | fzero  | [ p ] = ⊥-elim (s←s y p)

  prf₁ {x} with Iso.f φ (fsuc x) | inspect (Iso.f φ) (fsuc x)
  ... | fzero  | [ p ] = ⊥-elim (s→s x p)
  ... | fsuc y | [ p ] rewrite p with Iso.g φ (fsuc y) | inspect (Iso.g φ) (fsuc y)
  ...     | fzero  | [ q ] = ⊥-elim (s←s y q)
  ...     | fsuc w | [ q ] rewrite sym p | Iso.prf₁ φ {fsuc x} = sym (unfsuc q) 
  
  prf₂ {y} with Iso.g φ (fsuc y) | inspect (Iso.g φ) (fsuc y)
  ... | fzero  | [ p ] = ⊥-elim (s←s y p)
  ... | fsuc x | [ p ] rewrite p with Iso.f φ (fsuc x) | inspect (Iso.f φ) (fsuc x)
  ...     | fzero  | [ q ] = ⊥-elim (s→s x q)
  ...     | fsuc w | [ q ] rewrite sym p | Iso.prf₂ φ {fsuc y} = sym (unfsuc q) 

-- we can remove a singleton from an isomorphism
unsuc-Fin-iso : {n m : Nat} -> Fin (suc n) ⇔ Fin (suc m) -> Fin n ⇔ Fin m
unsuc-Fin-iso {n} {m} φ = unsuc-Fin-iso-v1 θ prf→ where
  y₀ : Fin (suc m)
  y₀ = Iso.f φ fzero
  ψ : Fin (suc m) ⇔ Fin (suc m)
  ψ = Fin-insert-Iso {m} y₀
  θ : Fin (suc n) ⇔ Fin (suc m)
  θ = φ ⊙ (flip⇔ ψ)

  eq₁ : Iso.f (flip⇔ ψ) y₀ ≡ fzero
  eq₁ = Fin-insert-Iso-y₀ {m} y₀

  prf→ : Iso.f θ fzero ≡ fzero
  prf→ = eq₁

--------------------------------------------------------------------------------
-- now finally we can prove what we wanted:

Fin-size-invariant : {n m : Nat} -> Fin n ⇔ Fin m -> n ≡ m
Fin-size-invariant {zero}   {zero  } _   = refl
Fin-size-invariant {zero}   {suc m₁} iso = Fin₀-elim (Iso.g iso fzero)
Fin-size-invariant {suc n₁} {zero}   iso = Fin₀-elim (Iso.f iso fzero)
Fin-size-invariant {suc n₁} {suc m₁} iso = cong suc (Fin-size-invariant {n₁} {m₁} (unsuc-Fin-iso iso)) 

size-is-well-defined : {A : Set} -> {n m : Nat} -> A ⊢ n -> A ⊢ m -> n ≡ m
size-is-well-defined φ ψ = Fin-size-invariant (flip⇔ φ ⊙ ψ)

size-is-invariant : {A B : Set} -> {n m : Nat} -> A ⊢ n -> B ⊢ m -> A ⇔ B -> n ≡ m
size-is-invariant φ ψ θ = size-is-well-defined φ (θ ⊙ ψ)

--------------------------------------------------------------------------------
-- Fin vs. pairs

{-
Fin⇔[A+B] : {n : Nat} -> Fin n ⇔ [A+B]≡ n
Fin⇔[A+B] {n} = mkIso Fin⇒[A+B] [A+B]⇒Fin prf₁ prf₂ where
  prf₁ : {x : Fin n} -> [A+B]⇒Fin (Fin⇒[A+B]
-}

--------------------------------------------------------------------------------
-- zero and one

⊥-size : ⊥ ⊢ 0
⊥-size = mkIso ⊥-elim Fin₀-elim (λ {x} -> ⊥-elim x) (λ {y} -> Fin₀-elim y)

⊤-size : ⊤ ⊢ 1
⊤-size = mkIso f g p₁ p₂ where
  f : ⊤ -> Fin 1
  g : Fin 1 -> ⊤
  p₁ : {x : ⊤}     -> g (f x) ≡ x  
  p₂ : {y : Fin 1} -> f (g y) ≡ y  
  f _ = fzero
  g _ = tt
  p₁ {tt}    = refl
  p₂ {fzero} = refl

Fin₀-is-⊥ : Fin 0 ⇔ ⊥
Fin₀-is-⊥ = flip⇔ ⊥-size

Fin₁-is-⊤ : Fin 1 ⇔ ⊤
Fin₁-is-⊤ = flip⇔ ⊤-size

--------------------------------------------------------------------------------

⊤⊎Fin : {n : Nat} -> ⊤ ⊎ Fin n ⇔ Fin (suc n)
⊤⊎Fin {n} = mkIso f g p q where
  f : ⊤ ⊎ Fin n -> Fin (suc n)
  g : Fin (suc n) -> ⊤ ⊎ Fin n
  p : {x : ⊤ ⊎ Fin n}   -> g (f x) ≡ x
  q : {y : Fin (suc n)} -> f (g y) ≡ y  
  f (inj₁ _) = fzero
  f (inj₂ f) = fsuc f
  g fzero    = inj₁ tt
  g (fsuc f) = inj₂ f
  p {inj₁ _} = refl
  p {inj₂ _} = refl
  q {fzero } = refl
  q {fsuc _} = refl
  
--------------------------------------------------------------------------------
-- arithmetic on Fin

+-Fin : {n m : Nat} -> Fin n ⊎ Fin m ⇔ Fin (n + m)
+-Fin {zero  } {m}
  = (flip⇔ ⊥-size ⊕ id⇔)
  ⊙ ⊎-left-unit
+-Fin {suc n₁} {m}
  = (flip⇔ (⊤⊎Fin {n₁}) ⊕ id⇔)
  ⊙ ⊎-assoc
  ⊙ (id⇔ ⊕ (+-Fin {n₁} {m}))
  ⊙ (⊤⊎Fin {n₁ + m})
  
*-Fin : {n m : Nat} -> Fin n × Fin m ⇔ Fin (n * m)
*-Fin {zero  } {m}
  = (Fin₀-is-⊥ ⊗ id⇔)
  ⊙ ×-left-annihilator
  ⊙ ⊥-size
*-Fin {suc n₁ } {m}
  = (flip⇔ (⊤⊎Fin {n₁}) ⊗ id⇔)
  ⊙ ⊎×-distrib-right
  ⊙ (×-left-unit ⊕ (*-Fin {n₁} {m}))
  ⊙ (+-Fin {m} {n₁ * m})

--------------------------------------------------------------------------------

Fin-suc : {n : Nat} -> Fin (suc n) ⊢ suc n
Fin-suc {n} 
  = flip⇔ (⊤⊎Fin {n})  
  ⊙ (flip⇔ Fin₁-is-⊤ ⊕ isoRefl)
  ⊙ (+-Fin {1} {n})

--------------------------------------------------------------------------------
-- size of sum and product

⊎-size : {A B : Set} -> {n m : Nat} -> A ⊢ n -> B ⊢ m -> (A ⊎ B) ⊢ (n + m)
⊎-size φ ψ = (φ ⊕ ψ) ⊙ +-Fin

×-size : {A B : Set} -> {n m : Nat} -> A ⊢ n -> B ⊢ m -> (A × B) ⊢ (n * m)
×-size φ ψ = (φ ⊗ ψ) ⊙ *-Fin

--------------------------------------------------------------------------------
-- two

Bool-size : Bool ⊢ 2
Bool-size = Bool⇔⊤⊎⊤ ⊙ (⊎-size ⊤-size ⊤-size) 

Fin₂-is-Bool : Fin 2 ⇔ Bool
Fin₂-is-Bool = flip⇔ Bool-size 

--------------------------------------------------------------------------------
-- dependent sums

private

  sum[] : sum [] ≡ 0
  sum[] = refl 

  λsuc : {A : Set} {n : Nat} -> (Fin₁ n -> A) -> (Fin n -> A)
  λsuc f = λ k -> f (fsuc k)

  -- this should be in the standard library somewhere...
  map-map
    :  {A B C : Set} {n : Nat} (g : B -> C) (f : A -> B)
    -> (v : Vec A n) -> map g (map f v) ≡ map (g ∘ f) v
  map-map g f [] = refl
  map-map g f (x ∷ xs) rewrite map-map g f xs = refl

  sum-lemma
    :  {n : Nat} -> (f : Fin₁ n -> Nat)
    -> sum (map (λsuc f)    (enumerateFin n)) ≡
       sum (map f (map fsuc (enumerateFin n)))
  sum-lemma {zero  } f = refl
  sum-lemma {suc n₁} f
    rewrite sum-lemma {n₁} (λsuc f)
          | map-map f fsuc (map fsuc (enumerateFin n₁)) = refl
  
Σ-fin
  : {n : Nat} -> (f : Fin n -> Nat)
  -> Σ (Fin n) (λ k -> Fin (f k)) ⇔ Fin (sum (map f (enumerateFin n)))
Σ-fin {zero  } f rewrite sum[]
  = Σ⇔ Fin₀-is-⊥ (λ {x} -> Fin₀-elim x)
  ⊙ Σ⊥⇔⊥ {⊥-elim}
  ⊙ flip⇔ Fin₀-is-⊥
Σ-fin {suc n₁} f
  = Σ⇔fst (flip⇔ ⊤⊎Fin)
  ⊙ Σ⊎⇔
  ⊙ (Σ⊤⇔ ⊕ Σ-fin {n₁} (λ k -> f (fsuc k)))
  ⊙ ⊎-size isoRefl (Fin-subst-Iso (sum-lemma {n₁} f))

Σ-size
  : {A : Set} -> {B : A -> Set}
  -> (n : Nat) -> (f : Fin n -> Nat)
  -> (isoA : A ⊢ n) -> ({x : A} -> B x ⊢ f (Iso.f isoA x))
  -> Σ A B ⊢ sum (Data.Vec.Base.map f (enumerateFin n))
Σ-size {A} {B} n f isoA isoB = Σ⇔ isoA isoB ⊙ Σ-fin {n} f

--------------------------------------------------------------------------------
