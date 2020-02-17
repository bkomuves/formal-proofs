
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
open import numbers
open import bitvectors using ( BitVec ; BitVec-size ; count-trues ; count-true-false )

--------------------------------------------------------------------------------

-- `Combination₂ a b` is the type of bit-vectors of
-- length (a+b) with `a` true-s and `b` false-s.
--
-- This symmetric definitions should be much easier
-- to work with than the assymetric one
data Combination₂ : Nat -> Nat -> Set where
  cnil   : Combination₂ 0 0
  ctrue  : {a b : Nat} -> Combination₂ a b -> Combination₂ (suc a)      b
  cfalse : {a b : Nat} -> Combination₂ a b -> Combination₂      a  (suc b)

-- Comb₂[A+B] : {n : Nat} -> [A+B]≡ n -> Set
-- Comb₂[A+B] ab = Combination₂ (πA ab) (πB ab)

concatenate
  :  {a₁ b₁ a₂ b₂ : Nat} -> Combination₂ a₁ b₁ -> Combination₂ a₂ b₂
  -> Combination₂ (a₁ + a₂) (b₁ + b₂)
concatenate cnil        d = d
concatenate (ctrue  c₁) d = ctrue  (concatenate c₁ d)
concatenate (cfalse c₁) d = cfalse (concatenate c₁ d)

invert-Comb₂ : {a b : Nat} -> Combination₂ a b -> Combination₂ b a 
invert-Comb₂  cnil       = cnil
invert-Comb₂ (ctrue  c₁) = cfalse (invert-Comb₂ c₁)
invert-Comb₂ (cfalse c₁) = ctrue  (invert-Comb₂ c₁)

--------------------------------------------------------------------------------

replicate-false : (n : Nat) -> Combination₂ 0 n
replicate-false zero     = cnil
replicate-false (suc n₁) = cfalse (replicate-false n₁)

replicate-true : (n : Nat) -> Combination₂ n 0
replicate-true zero     = cnil
replicate-true (suc n₁) = ctrue (replicate-true n₁)

first-a-true : (a b : Nat) -> Combination₂ a b
first-a-true a b with concatenate (replicate-true a) (replicate-false b)
... | c rewrite (n+0 a) = c

--------------------------------------------------------------------------------

comb₂ToBitVec : {a b : Nat} -> Combination₂ a b -> BitVec (a + b)
comb₂ToBitVec cnil          = []
comb₂ToBitVec (ctrue  comb) = true ∷ comb₂ToBitVec comb
comb₂ToBitVec {a} {suc b₁} (cfalse comb) rewrite n+suc a b₁
                            = false ∷ comb₂ToBitVec comb
{-
bitVecToComb₂
  :  {n : Nat} 
  -> (bs : BitVec n)
  -> Comb₂[A+B] (count-true-false bs)
bitVecToComb₂ []            = cnil
bitVecToComb₂ (true  ∷ bs₁) = ctrue  (bitVecToComb₂ bs₁) 
bitVecToComb₂ (false ∷ bs₁) = cfalse (bitVecToComb₂ bs₁)
-}

count-trues-Comb₂ :  {a b : Nat} 
  -> (c : Combination₂ a b) -> finToNat (count-trues (comb₂ToBitVec c)) ≡ a
count-trues-Comb₂ cnil        = refl
count-trues-Comb₂ (ctrue  c₁) = cong suc (count-trues-Comb₂ c₁)
count-trues-Comb₂ {a} {suc b₁} (cfalse c₁) rewrite n+suc a b₁ with count-trues-Comb₂ c₁
... | eq₁ = (finToNat-finj _) ∙ eq₁

--------------------------------------------------------------------------------
-- The isomorphism between bit vectors and the sum of k-combinations (for k=0..n)

{-
-- dependent pair of `a+b=n` and `Combination₂ a b`
k-Comb₂ : (n : Nat) -> Set
k-Comb₂ n = Σ ([A+B]≡ n) Comb₂[A+B]

ktrue : {n : Nat} -> k-Comb₂ n -> k-Comb₂ (suc n)
ktrue (ab , c) = (sucA ab , ctrue c)

kfalse : {n : Nat} -> k-Comb₂ n -> k-Comb₂ (suc n)
kfalse (ab , c) = (sucB ab , cfalse c)

BitVec⇔k-Comb₂ : {n : Nat} -> BitVec n ⇔ k-Comb₂ n
BitVec⇔k-Comb₂ = mkIso f g p q where
  f : {n : Nat} -> BitVec n  -> k-Comb₂ n
  g : {n : Nat} -> k-Comb₂ n -> BitVec n
  p : {n : Nat} {x : BitVec  n} -> g (f x) ≡ x
  q : {n : Nat} {y : k-Comb₂ n} -> f (g y) ≡ y

  f bv = (count-true-false bv , bitVecToComb₂ bv)
  g (ab , c) with comb₂ToBitVec c
  ... | bv rewrite [A+B]-proof ab = bv
  
  p {zero  } {[]} = refl
  p {suc n₁} {true ∷ bv₁} with f bv₁
  ... | (ab₁ , c₁) with comb₂ToBitVec c₁
  ... | bv₂ with p {n₁} {bv₁}
  ... | p₁ rewrite [A+B]-proof ab₁ = {!!}
-}

--------------------------------------------------------------------------------

comb₂[0,n]⇒false : {n : Nat} -> (c : Combination₂ 0 n) -> c ≡ replicate-false n
comb₂[0,n]⇒false {zero  } cnil        = refl
comb₂[0,n]⇒false {suc n₁} (cfalse c₁) = cong cfalse (comb₂[0,n]⇒false c₁)

comb₂[n,0]⇒true : {n : Nat} -> (c : Combination₂ n 0) -> c ≡ replicate-true n
comb₂[n,0]⇒true {zero  } cnil       = refl
comb₂[n,0]⇒true {suc n₁} (ctrue c₁) = cong ctrue (comb₂[n,0]⇒true c₁)

--------------------------------------------------------------------------------

Pascal-left-edge : {n : Nat} -> Combination₂ n 0 ⇔ ⊤
Pascal-left-edge {n} = mkIso f g p q where
  f : Combination₂ n 0 -> ⊤
  g : ⊤ -> Combination₂ n 0  
  p : {x : Combination₂ n 0} -> g (f x) ≡ x
  q : {y : ⊤} -> f (g y) ≡ y
  f cnil      = tt
  f (ctrue c) = tt 
  g tt = replicate-true n
  p {c} rewrite comb₂[n,0]⇒true c = refl
  q {tt} = refl

Pascal-right-edge : {n : Nat} -> Combination₂ 0 n ⇔ ⊤
Pascal-right-edge {n} = mkIso f g p q where
  f : Combination₂ 0 n -> ⊤
  g : ⊤ -> Combination₂ 0 n  
  p : {x : Combination₂ 0 n} -> g (f x) ≡ x
  q : {y : ⊤} -> f (g y) ≡ y
  f cnil       = tt
  f (cfalse c) = tt 
  g tt = replicate-false n
  p {c} rewrite comb₂[0,n]⇒false c = refl
  q {tt} = refl

--------------------------------------------------------------------------------

Pascal⇔rev
  :  {a b : Nat}
  -> Combination₂ (suc a) b ⊎ Combination₂ a (suc b) ⇔ Combination₂ (suc a) (suc b)
Pascal⇔rev {a} {b} = mkIso f g prf₁ prf₂ where
  f : Combination₂ (suc a) b ⊎ Combination₂ a (suc b) -> Combination₂ (suc a) (suc b)
  g : Combination₂ (suc a) (suc b) -> Combination₂ (suc a) b ⊎ Combination₂ a (suc b)
  prf₁ : {x : Combination₂ (suc a) b ⊎ Combination₂ a (suc b)} -> g (f x) ≡ x
  prf₂ : {y : Combination₂ (suc a) (suc b)} -> f (g y) ≡ y
  f (inj₁ c) = cfalse c
  f (inj₂ c) = ctrue  c
  g (cfalse c) = inj₁ c
  g (ctrue  c) = inj₂ c
  prf₁ {inj₁ c}   = refl
  prf₁ {inj₂ c}   = refl
  prf₂ {cfalse c} = refl
  prf₂ {ctrue  c} = refl

Pascal⇔
  :  {a b : Nat}
  -> Combination₂ (suc a) (suc b) ⇔ Combination₂ (suc a) b ⊎ Combination₂ a (suc b)
Pascal⇔ = flip⇔ Pascal⇔rev

--------------------------------------------------------------------------------

comb₂-size : (a b : Nat) -> Combination₂ a b ⊢ binomial₂ a b
comb₂-size zero _            = Pascal-right-edge ⊙ ⊤-size
comb₂-size (suc a₁) zero     = Pascal-left-edge  ⊙ ⊤-size
comb₂-size (suc a₁) (suc b₁) = Pascal⇔ ⊙ (comb₂-size _ _ ⊕ comb₂-size _ _) ⊙ +-Fin

--------------------------------------------------------------------------------
