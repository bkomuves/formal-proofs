
-- bijections between finite sets

open import Data.Bool using ( Bool; false; true)
import Data.Bool 

open import Data.Nat
open import Data.Nat.Properties
open import Data.List

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum.Base
open import Data.Product
 
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import fin

--------------------------------------------------------------------------------
-- definition of bijection, and proof that it is an equivalence relation

record Iso (A B : Set) : Set where
  constructor mkIso
  field
    f : A -> B
    g : B -> A
    prf₁ : {x : A} -> g (f x) ≡ x
    prf₂ : {y : B} -> f (g y) ≡ y

isoRefl : {A : Set} -> Iso A A
isoRefl = mkIso id id refl refl

isoSym : {A B : Set} -> Iso A B -> Iso B A
isoSym φ = mkIso (Iso.g φ) (Iso.f φ) (Iso.prf₂ φ) (Iso.prf₁ φ)

isoComp : {A B C : Set} -> Iso B C -> Iso A B -> Iso A C
isoComp {A} {B} {C} ψ φ = mkIso f g p₁ p₂ where
  f = Iso.f ψ ∘ Iso.f φ
  g = Iso.g φ ∘ Iso.g ψ
  p₁ : {x : A} -> g (f x) ≡ x
  p₁ {x} rewrite (Iso.prf₁ ψ {Iso.f φ x}) = Iso.prf₁ φ {x}
  p₂ : {z : C} -> f (g z) ≡ z
  p₂ {z} rewrite (Iso.prf₂ φ {Iso.g ψ z}) = Iso.prf₂ ψ {z}

--------------------------------------------------------------------------------
-- notation for bijections

infix 0 _⇔_
_⇔_ : Set -> Set -> Set
A ⇔ B = Iso A B

infixr 7 _⊙_ 
_⊙_ : {A B C : Set} -> (A ⇔ B) -> (B ⇔ C) -> (A ⇔ C)
ψ ⊙ φ = isoComp φ ψ 

id⇔ : {A : Set} -> A ⇔ A
id⇔ = isoRefl

flip⇔ : {A B : Set} -> (A ⇔ B) -> (B ⇔ A)
flip⇔ = isoSym

--------------------------------------------------------------------------------
-- component-wise bijection for sum and product

⊎⟨_,_⟩ : {A B C D : Set} -> (A -> C) -> (B -> D) -> A ⊎ B -> C ⊎ D
⊎⟨ f , g ⟩ = Data.Sum.Base.map f g

infixl 5 _⊕_
_⊕_ : {A₁ A₂ B₁ B₂ : Set} -> (A₁ ⇔ A₂) -> (B₁ ⇔ B₂) -> (A₁ ⊎ B₁ ⇔ A₂ ⊎ B₂)
_⊕_ {A₁} {A₂} {B₁} {B₂} φ₁ φ₂ = mkIso f g prf₁ prf₂ where
  f = ⊎⟨ Iso.f φ₁ , Iso.f φ₂ ⟩
  g = ⊎⟨ Iso.g φ₁ , Iso.g φ₂ ⟩
  prf₁ : {x : A₁ ⊎ B₁} -> g (f x) ≡ x
  prf₂ : {y : A₂ ⊎ B₂} -> f (g y) ≡ y
  prf₁ {inj₁ x₁} = cong inj₁ (Iso.prf₁ φ₁ {x₁})
  prf₁ {inj₂ x₂} = cong inj₂ (Iso.prf₁ φ₂ {x₂})
  prf₂ {inj₁ y₁} = cong inj₁ (Iso.prf₂ φ₁ {y₁})
  prf₂ {inj₂ y₂} = cong inj₂ (Iso.prf₂ φ₂ {y₂})

×⟨_,_⟩ : {A B C D : Set} -> (A -> C) -> (B -> D) -> A × B -> C × D
×⟨ f , g ⟩ = Data.Product.map f g

infixl 6 _⊗_
_⊗_ : {A₁ A₂ B₁ B₂ : Set} -> (A₁ ⇔ A₂) -> (B₁ ⇔ B₂) -> (A₁ × B₁ ⇔ A₂ × B₂)
_⊗_ {A₁} {A₂} {B₁} {B₂} φ₁ φ₂ = mkIso f g prf₁ prf₂ where
  f = ×⟨ Iso.f φ₁ , Iso.f φ₂ ⟩
  g = ×⟨ Iso.g φ₁ , Iso.g φ₂ ⟩
  prf₁ : {x : A₁ × B₁} -> g (f x) ≡ x
  prf₂ : {y : A₂ × B₂} -> f (g y) ≡ y
  prf₁ {x₁ , x₂} = cong₂ _,′_ (Iso.prf₁ φ₁ {x₁}) (Iso.prf₁ φ₂ {x₂})
  prf₂ {y₁ , y₂} = cong₂ _,′_ (Iso.prf₂ φ₁ {y₁}) (Iso.prf₂ φ₂ {y₂})

--------------------------------------------------------------------------------
-- commutativity of sum and product

⊎-swap : {A B : Set} -> A ⊎ B ⇔ B ⊎ A
⊎-swap {A} {B} = mkIso f g p q where
  f : A ⊎ B -> B ⊎ A
  g : B ⊎ A -> A ⊎ B 
  p : {x : A ⊎ B} -> g (f x) ≡ x 
  q : {y : B ⊎ A} -> f (g y) ≡ y 
  f (inj₁ x) = inj₂ x
  f (inj₂ x) = inj₁ x
  g (inj₁ y) = inj₂ y
  g (inj₂ y) = inj₁ y
  p {inj₁ x} = refl
  p {inj₂ x} = refl
  q {inj₁ y} = refl
  q {inj₂ y} = refl

×-swap : {A B : Set} -> A × B ⇔ B × A
×-swap {A} {B} = mkIso f g p q where
  f : A × B -> B × A
  g : B × A -> A × B 
  p : {x : A × B} -> g (f x) ≡ x 
  q : {y : B × A} -> f (g y) ≡ y 
  f (a , b) = (b , a)
  g (b , a) = (a , b)
  p = refl
  q = refl
  
--------------------------------------------------------------------------------
-- associativity of sum and product

⊎-assoc : {A B C : Set} -> (A ⊎ B) ⊎ C ⇔ A ⊎ (B ⊎ C)
⊎-assoc {A} {B} {C} = mkIso f g p q where
  f : (A ⊎ B) ⊎ C -> A ⊎ (B ⊎ C)
  g : A ⊎ (B ⊎ C) -> (A ⊎ B) ⊎ C   
  p : {x : (A ⊎ B) ⊎ C} -> g (f x) ≡ x 
  q : {y : A ⊎ (B ⊎ C)} -> f (g y) ≡ y 

  f (inj₁ (inj₁ a)) = inj₁ a
  f (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
  f (inj₂       c ) = inj₂ (inj₂ c)

  g (inj₁        a) = inj₁ (inj₁ a)
  g (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
  g (inj₂ (inj₂ c)) = inj₂ c

  p {inj₁ (inj₁ _)} = refl
  p {inj₁ (inj₂ _)} = refl
  p {inj₂ _} = refl
  
  q {inj₁ _} = refl
  q {inj₂ (inj₁ _)} = refl
  q {inj₂ (inj₂ _)} = refl

×-assoc : {A B C : Set} -> (A × B) × C ⇔ A × (B × C)
×-assoc {A} {B} {C} = mkIso f g p q where
  f : (A × B) × C -> A × (B × C)
  g : A × (B × C) -> (A × B) × C   
  p : {x : (A × B) × C} -> g (f x) ≡ x 
  q : {y : A × (B × C)} -> f (g y) ≡ y 
  f ((a , b) , c) = (a , (b , c))
  g (a , (b , c)) = ((a , b) , c)
  p = refl
  q = refl

--------------------------------------------------------------------------------
-- distributivity

⊎×-distrib-right : {A B C : Set} -> (A ⊎ B) × C ⇔ (A × C) ⊎ (B × C)
⊎×-distrib-right {A} {B} {C} = mkIso f g p q where
  f : (A ⊎ B) × C       -> (A × C) ⊎ (B × C)
  g : (A × C) ⊎ (B × C) -> (A ⊎ B) × C
  p : {x : (A ⊎ B) × C}       -> g (f x) ≡ x 
  q : {y : (A × C) ⊎ (B × C)} -> f (g y) ≡ y
  f (inj₁ a , c) = inj₁ (a , c)
  f (inj₂ b , c) = inj₂ (b , c)
  g (inj₁ (a , c)) = (inj₁ a , c)
  g (inj₂ (b , c)) = (inj₂ b , c)
  p {inj₁ _ , _} = refl
  p {inj₂ _ , _} = refl
  q {inj₁ _} = refl
  q {inj₂ _} = refl

⊎×-distrib-left : {A B C : Set} -> A × (B ⊎ C) ⇔ (A × B) ⊎ (A × C)
⊎×-distrib-left = ×-swap ⊙ ⊎×-distrib-right ⊙ (×-swap ⊕ ×-swap)

--------------------------------------------------------------------------------
-- left and right unit for sum

⊎-left-unit : {A : Set} -> ⊥ ⊎ A ⇔ A
⊎-left-unit {A} = mkIso f g p q where
  f : ⊥ ⊎ A -> A
  g : A -> ⊥ ⊎ A
  p : {x : ⊥ ⊎ A} -> g (f x) ≡ x
  q : {y :     A} -> f (g y) ≡ y 
  f (inj₂ x) = x
  g y = inj₂ y
  p {inj₂ x} = refl
  q {y} = refl
 
⊎-right-unit : {A : Set} -> A ⊎ ⊥ ⇔ A
⊎-right-unit = ⊎-swap ⊙ ⊎-left-unit  

--------------------------------------------------------------------------------
-- left and right unit for product

×-left-unit : {A : Set} -> ⊤ × A ⇔ A
×-left-unit {A} = mkIso f g p q where
  f : ⊤ × A -> A
  g : A -> ⊤ × A
  p : {x : ⊤ × A} -> g (f x) ≡ x
  q : {y :     A} -> f (g y) ≡ y 
  f (_ , x) = x
  g y = (tt , y)
  p {(_ , x)} = refl
  q {y} = refl
 
×-right-unit : {A : Set} -> A × ⊤ ⇔ A
×-right-unit = ×-swap ⊙ ×-left-unit

--------------------------------------------------------------------------------
-- left and right annihilator for product

×-left-annihilator : {A : Set} -> ⊥ × A ⇔ ⊥
×-left-annihilator {A} = mkIso f g p q where
  f : ⊥ × A -> ⊥
  g : ⊥ -> ⊥ × A
  p : {x : ⊥ × A} -> g (f x) ≡ x
  q : {y :     ⊥} -> f (g y) ≡ y 
  f (bot , _) = ⊥-elim bot
  g bot       = ⊥-elim bot
  p {(bot , _)} = ⊥-elim bot
  q {bot}       = ⊥-elim bot
  
×-right-annihilator : {A : Set} -> A × ⊥ ⇔ ⊥
×-right-annihilator = ×-swap ⊙ ×-left-annihilator

--------------------------------------------------------------------------------

Bool⇔⊤⊎⊤ : Bool ⇔ (⊤ ⊎ ⊤)
Bool⇔⊤⊎⊤ = mkIso f g p q where
  f : Bool -> ⊤ ⊎ ⊤
  g : ⊤ ⊎ ⊤ -> Bool
  p : {x : Bool } -> g (f x) ≡ x
  q : {y : ⊤ ⊎ ⊤} -> f (g y) ≡ y
  f false = inj₁ tt
  f true  = inj₂ tt
  g (inj₁ tt) = false
  g (inj₂ tt) = true
  p {false} = refl
  p {true } = refl
  q {inj₁ tt} = refl
  q {inj₂ tt} = refl
  
⊤⊎⊤⇔Bool : (⊤ ⊎ ⊤) ⇔ Bool  
⊤⊎⊤⇔Bool = flip⇔ Bool⇔⊤⊎⊤

--------------------------------------------------------------------------------
-- isomorphisms of dependent sums

cong₂-dep
  :  {A : Set} -> {B : A -> Set} -> {C : Set}
  -> (f : (a : A) -> (b : B a) -> C) 
  -> {x y : A} {u : B x} {v : B y}
  -> (e : x ≡ y)
  -> subst B e u ≡ v
  -> f x u ≡ f y v
cong₂-dep f refl refl = refl

Σ-cong₂ 
  :  {A : Set} -> {B : A -> Set}
  -> {a₁ a₂ : A}
  -> {b₁ : B a₁} {b₂ : B a₂}
  -> (e : a₁ ≡ a₂)
  -> (f : subst B e b₁ ≡ b₂)
  -> (a₁ , b₁) ≡ (a₂ , b₂)
Σ-cong₂ {A} {B} e f = cong₂-dep _,_ e f

----------------------------------------

Σ⇔snd : {A : Set} -> {B₁ : A -> Set} -> {B₂ : A -> Set}
    -> (isoB : {a : A} -> B₁ a ⇔ B₂ a) 
    -> Σ A B₁ ⇔ Σ A B₂
Σ⇔snd {A} {B₁} {B₂} isoB = mkIso f g prf₁ prf₂ where  
  f : Σ A B₁ -> Σ A B₂
  g : Σ A B₂ -> Σ A B₁ 
  prf₁ : {x : Σ A B₁} -> g (f x) ≡ x 
  prf₂ : {y : Σ A B₂} -> f (g y) ≡ y
  f (a , b₁) = (a , Iso.f (isoB {a}) b₁)
  g (a , b₂) = (a , Iso.g (isoB {a}) b₂)
  prf₁ {a , b₁} = Σ-cong₂ refl (Iso.prf₁ (isoB {a}) {b₁})
  prf₂ {a , b₂} = Σ-cong₂ refl (Iso.prf₂ (isoB {a}) {b₂})

----------------------------------------

Σ⇔fst : {A₁ A₂ : Set} -> {B₁ : A₁ -> Set}
    -> (isoA : A₁ ⇔ A₂) 
    -> Σ A₁ B₁ ⇔ Σ A₂ (λ a₂ -> B₁ (Iso.g isoA a₂))
Σ⇔fst {A₁} {A₂} {B₁} isoA = mkIso f g prf₁ prf₂ where

  f : Σ A₁ B₁ -> Σ A₂ (λ a₂ -> B₁ (Iso.g isoA a₂))
  g : Σ A₂ (λ a₂ -> B₁ (Iso.g isoA a₂)) -> Σ A₁ B₁ 
  prf₁ : {x : Σ A₁ B₁} -> g (f x) ≡ x 
  prf₂ : {y : Σ A₂ (λ a₂ -> B₁ (Iso.g isoA a₂))} -> f (g y) ≡ y

  -- NB: doing this with in some other oreder does not work!
  -- i have no idea what's going on... :(
  f (a₁ , b₁) with Iso.prf₁ isoA {a₁}
  ... | eq with Iso.f isoA a₁
  ... | a₂ with eq
  ... | refl = ( a₂ , b₁ )

  --  f (a₁ , b₁) with sym (Iso.prf₁ isoA {a₁})
  --  ... | eq rewrite eq = (Iso.f isoA a₁ , b₁)

  g (a₂ , b₂) = (Iso.g isoA a₂ , b₂)
  
  prf₁ {a₁ , b₁} with Iso.prf₁ isoA {a₁}
  ... | eq with  Iso.f isoA a₁
  ... | a₂ with eq
  ... | refl = refl

  prf₂ {a₂ , b₂} with Iso.prf₂ isoA {a₂}
  ... | eq₂ with Iso.prf₁ isoA {Iso.g isoA a₂}
  ... | eq₁ rewrite eq₂ with eq₁
  ... | refl = refl

----------------------------------------

Σ⇔ : {A₁ A₂ : Set} -> {B₁ : A₁ -> Set} -> {B₂ : A₂ -> Set}
    -> (isoA : A₁ ⇔ A₂)
    -> (isoB : {x : A₁} -> B₁ x ⇔ B₂ (Iso.f isoA x))
    -> Σ A₁ B₁ ⇔ Σ A₂ B₂
Σ⇔ {A₁} {A₂} {B₁} {B₂} isoA isoB with Σ⇔fst {A₂} {A₁} {B₂} (flip⇔ isoA)
... | Θ = Σ⇔snd isoB ⊙ (flip⇔ Θ)  

--------------------------------------------------------------------------------

Σ⊥⇔⊥ : {B : ⊥ -> Set} -> Σ ⊥ B ⇔ ⊥
Σ⊥⇔⊥ {B} = mkIso f g p₁ p₂ where
  f : Σ ⊥ B -> ⊥
  g : ⊥ -> Σ ⊥ B
  p₁ : {x : Σ ⊥ B} -> g (f x) ≡ x
  p₂ : {y :   ⊥  } -> f (g y) ≡ y
  f  (bot , _) = ⊥-elim bot
  g   bot      = ⊥-elim bot
  p₁ {bot , _} = ⊥-elim bot
  p₂ {bot    } = ⊥-elim bot

Σ⊤⇔ : {B : ⊤ -> Set} -> Σ ⊤ B ⇔ (B tt)
Σ⊤⇔ {B} = mkIso f g p₁ p₂ where
  f : Σ ⊤ B -> B tt
  g : B tt -> Σ ⊤ B
  p₁ : {x : Σ ⊤ B} -> g (f x) ≡ x
  p₂ : {y : B tt } -> f (g y) ≡ y
  f  (tt , b) = b
  g   b       = (tt , b)
  p₁ {tt , b} = refl
  p₂ {b     } = refl

--------------------------------------------------------------------------------

Σ⊎⇔ : {A₁ A₂ : Set} {B : A₁ ⊎ A₂ -> Set}
  -> Σ (A₁ ⊎ A₂) B ⇔ Σ A₁ (B ∘ inj₁) ⊎ Σ A₂ (B ∘ inj₂) 
Σ⊎⇔ {A₁} {A₂} {B} = mkIso f g prf₁ prf₂ where
  B₁ : A₁ -> Set
  B₂ : A₂ -> Set
  B₁ = B ∘ inj₁
  B₂ = B ∘ inj₂
  f : Σ (A₁ ⊎ A₂) B -> Σ A₁ (B ∘ inj₁) ⊎ Σ A₂ (B ∘ inj₂)
  g : Σ A₁ (B ∘ inj₁) ⊎ Σ A₂ (B ∘ inj₂) -> Σ (A₁ ⊎ A₂) B
  prf₁ : {x : Σ (A₁ ⊎ A₂) B} -> g (f x) ≡ x
  prf₂ : {y : Σ A₁ (B ∘ inj₁) ⊎ Σ A₂ (B ∘ inj₂)} -> f (g y) ≡ y
  
  f (inj₁ a₁ , b) = inj₁ (a₁ , b)
  f (inj₂ a₂ , b) = inj₂ (a₂ , b)

  g (inj₁ (a₁ , b)) = (inj₁ a₁ , b)
  g (inj₂ (a₂ , b)) = (inj₂ a₂ , b)

  prf₁ {inj₁ a₁ , b} = refl
  prf₁ {inj₂ a₂ , b} = refl
  
  prf₂ {inj₁ (a₁ , b)} = refl
  prf₂ {inj₂ (a₂ , b)} = refl

--------------------------------------------------------------------------------


