
open import Data.Nat
open import Data.Nat.Properties

open import Data.Bool using ( Bool ; false ; true )
open import Data.Vec.Base

open import Data.Empty
open import Data.Unit.Base
open import Data.Sum.Base
open import Data.Product
 
open import Relation.Binary.PropositionalEquality

open import useful
open import fin
open import bijection
open import cardinality

--------------------------------------------------------------------------------

BitVec : Nat -> Set
BitVec n = Vec Bool n

subst-BitVec : {n m : Nat} -> n ≡ m -> BitVec n -> BitVec m
subst-BitVec eq bv = subst BitVec eq bv 

--------------------------------------------------------------------------------

replicate-false : (n : Nat) -> BitVec n
replicate-false n = replicate {n = n} false

replicate-true : (n : Nat) -> BitVec n
replicate-true n = replicate {n = n} true

invert-BitVec : {n : Nat} -> BitVec n -> BitVec n
invert-BitVec [] = []
invert-BitVec (true  ∷ bs) = false ∷ invert-BitVec bs
invert-BitVec (false ∷ bs) = true  ∷ invert-BitVec bs

first-k-true-BitVec : (n : Nat) -> (k : Fin₁ n) -> BitVec n
first-k-true-BitVec n        fzero     = replicate-false n
first-k-true-BitVec (suc n₁) (fsuc k₁) = true ∷ first-k-true-BitVec n₁ k₁

--------------------------------------------------------------------------------

BitVec₀-is-⊤ : BitVec 0 ⇔ ⊤
BitVec₀-is-⊤ = mkIso f g p q where
  f : BitVec 0 -> ⊤
  g : ⊤ -> BitVec 0
  p : {x : BitVec 0} -> g (f x) ≡ x
  q : {y : ⊤} -> f (g y) ≡ y
  f [] = tt
  g tt = []
  p {[]} = refl
  q {tt} = refl
  
uncons-BitVec : (n : Nat) -> BitVec (suc n) ⇔ Bool × BitVec n
uncons-BitVec n = mkIso f g p q where
  f : BitVec (suc n)  -> Bool × BitVec n
  g : Bool × BitVec n -> BitVec (suc n)
  p : {x : BitVec (suc n) } -> g (f x) ≡ x
  q : {y : Bool × BitVec n} -> f (g y) ≡ y
  f (b ∷ bs) = (b , bs)
  g (b , bs) = b ∷ bs
  p { b ∷ bs } = refl
  q {(b , bs)} = refl
  
cons-BitVec : (n : Nat) -> Bool × BitVec n ⇔ BitVec (suc n)
cons-BitVec n = flip⇔ (uncons-BitVec n)

--------------------------------------------------------------------------------

BitVec-size : (n : Nat) -> BitVec n ⊢ (2 ^ n)
BitVec-size zero     = BitVec₀-is-⊤ ⊙ ⊤-size  
BitVec-size (suc n₁) = (uncons-BitVec n₁) ⊙ (×-size Bool-size (BitVec-size n₁))

--------------------------------------------------------------------------------

count-trues : {n : Nat} -> BitVec n -> Fin₁ n
count-trues []           = fzero
count-trues (false ∷ bs) = finj (count-trues bs)
count-trues (true  ∷ bs) = fsuc (count-trues bs)

-- Note: A = number of trues, B = number of falses
count-true-false : {n : Nat} -> BitVec n -> [A+B]≡ n
count-true-false []           = z+z
count-true-false (true  ∷ bs) = sucA (count-true-false bs)
count-true-false (false ∷ bs) = sucB (count-true-false bs)

{-
ex1 = enumerate (BitVec-size 3)
ex2 = Data.Vec.Base.map count-trues ex1
-}

--------------------------------------------------------------------------------
