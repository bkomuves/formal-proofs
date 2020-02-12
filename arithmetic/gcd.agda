
-- greatest common divisor

open import Data.Empty
open import Data.Sum     using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )

open import Relation.Binary.PropositionalEquality

open import Induction.WellFounded

open import nat
open import div
open import wf

--------------------------------------------------------------------------------

-- just a visually nicer notation for "logical and"
-- note: this is \and
_∧_ : Set -> Set -> Set
_∧_ = _×_

pattern _&_ x y = _,_ x y

--------------------------------------------------------------------------------
-- common divisors

-- `is common divisor of` relation
isCD : Nat -> Nat × Nat -> Set
isCD d (n , m) = (d ∣ n) ∧ (d ∣ m)

isCD-comm : {d n m : Nat} -> isCD d (n , m) -> isCD d (m , n)
isCD-comm = swap

{-
CommonDivisor : Nat -> Nat -> Set
CommonDivisor n m = Σ Nat (λ d -> isCD d (n , m))

-- shorthand
CD : Nat -> Nat -> Set
CD = CommonDivisor

CD-comm : {n m : Nat} -> CD n m -> CD m n
CD-comm (d , proof) = (d , swap proof)
-}

-- a common divisor of a and b also divides mod a b
cd∣mod : {a b c : Nat} -> (pos : b > 0) -> (c ∣ a) -> (c ∣ b) -> c ∣ (mod₊ a b pos)
cd∣mod {a} {b} {c} bpos div-a div-b
    with divMod₊w/proof a b bpos
... | ((q , r) , (_ , refl)) = div-unplus div-a (div-n* q div-b)

--------------------------------------------------------------------------------
-- definition of GCD, take one

-- classical definition of GCD
-- NB: with this definition, gcd(0,0) is not defined!
record isGCD (gcd n m : Nat) : Set where
  constructor mkGCD
  field
    is-cd : isCD gcd (n , m)
    proof : (c : Nat) -> isCD c (n , m) -> c ≤ gcd

GCD-comm : {d n m : Nat} -> isGCD d n m -> isGCD d m n
GCD-comm (mkGCD cd proof) = mkGCD (swap cd) (λ c p -> proof c (swap p))

GCD-unique : {d₁ d₂ n m : Nat} -> (isGCD d₁ n m) -> (isGCD d₂ n m) -> d₁ ≡ d₂
GCD-unique {d₁} {d₂} (mkGCD cd₁ prf₁) (mkGCD cd₂ prf₂) = ≤-antisym d₁≤d₂ d₂≤d₁ where
  d₁≤d₂ = prf₂ d₁ cd₁
  d₂≤d₁ = prf₁ d₂ cd₂

GCD[n,0] : (n : Nat) -> (n > 0) -> isGCD n n 0 
GCD[n,0] n pos = mkGCD cd prf where
  cd   = (n∣n n) & (n∣0 n)
  prf : (c : Nat) -> isCD c (n , 0) -> c ≤ n
  prf c (div₁ & _) with div⇒≤ div₁
  ... | inj₂ le = le
  ... | inj₁ eq rewrite eq = ⊥-elim (n≮0 pos)
  
--------------------------------------------------------------------------------
-- definition of GCD, take two

-- alternative, better behaved definition of GCD
-- (with this definition, gcd(0,0) both exists and is well-defined)
record isGCD′ (gcd n m : Nat) : Set where
  constructor mkGCD′ 
  field
    is-cd : isCD gcd (n , m)
    proof : (c : Nat) -> isCD c (n , m) -> c ∣ gcd

GCD′-comm : {d n m : Nat} -> isGCD′ d n m -> isGCD′ d m n
GCD′-comm (mkGCD′ cd proof) = mkGCD′ (swap cd) (λ c p -> proof c (swap p))

GCD′-unique : {d₁ d₂ n m : Nat} -> isGCD′ d₁ n m -> isGCD′ d₂ n m -> d₁ ≡ d₂
GCD′-unique {d₁} {d₂} (mkGCD′ cd₁ prf₁) (mkGCD′ cd₂ prf₂) = div-antisym d₁∣d₂ d₂∣d₁ where
  d₁∣d₂ = prf₂ d₁ cd₁
  d₂∣d₁ = prf₁ d₂ cd₂

GCD′[n,0] : (n : Nat) -> isGCD′ n n 0
GCD′[n,0] n = mkGCD′ cd prf where
  cd   = (n∣n n) & (n∣0 n)
  prf : (c : Nat) -> isCD c (n , 0) -> c ∣ n
  prf c (div₁ & _) = div₁

GCD′-plus : {d a b q : Nat} -> isGCD′ d a b -> isGCD′ d (a + q * b) b
GCD′-plus {d} {a} {b} {q} (mkGCD′ (div-a & div-b) prf) = mkGCD′ cd₂ prf₂ where
  cd₂  = (div-+ div-a (div-n* q div-b)) & div-b
  prf₂ : (c : Nat) -> isCD c (a + q * b , b) -> c ∣ d
  prf₂ c (c∣a+ & c∣b) with div-unplus c∣a+ (div-n* q c∣b)
  ... | c∣a = prf c (c∣a & c∣b) 
  
GCD′-mod : {d n m : Nat} -> (pos : m > 0) -> isGCD′ d n m -> isGCD′ d m (mod₊ n m pos)
GCD′-mod {d} {n} {m} pos (mkGCD′ cd prf) = mkGCD′ cd₂ prf₂ where
  cd₂  = proj₂ cd & cd∣mod pos (proj₁ cd) (proj₂ cd)
  prf₂ : (c : Nat) -> isCD c (m , mod₊ n m pos) -> c ∣ d
  prf₂ c (c∣m & c∣r) with divMod₊w/proof n m pos
  ... | ((q , r) , (_ , eq)) with div-+ c∣r (div-n* q c∣m)
  ... | c∣n rewrite (sym eq) = prf c (c∣n & c∣m)

GCD′-mod-rev : {d n m : Nat} -> (pos : m > 0) -> isGCD′ d m (mod₊ n m pos) -> isGCD′ d n m 
GCD′-mod-rev {d} {n} {m} pos (mkGCD′ (d∣m & d∣r) prf) with divMod₊w/proof n m pos
... | ((q , r) , (_ , eq)) rewrite eq = mkGCD′ 
            (div-+ d∣r (div-n* q d∣m)  & d∣m)
            (λ c cd -> let (c∣n & c∣m) = cd
                       in  prf c (c∣m , div-unplus c∣n (div-n* q c∣m)))
    
--------------------------------------------------------------------------------
-- connecting the two definitions

GCD′⇒GCD : {n a b : Nat} -> (n > 0) -> isGCD′ n a b -> isGCD n a b
GCD′⇒GCD {n} {a} {b} pos (mkGCD′ cd prf′) = mkGCD cd prf where
  prf : (c : Nat) -> isCD c (a , b) -> c ≤ n
  prf c cd with div⇒≤ (prf′ c cd)
  ... | inj₁ refl = ⊥-elim (n≮0 pos)
  ... | inj₂ le   = le 

--------------------------------------------------------------------------------
-- Euclid's algorithm

-- Euclid's algorithm (and now even Agda accepts it!)
euclid : Nat -> Nat -> Nat
euclid a b = Nat-wfrec worker b a where
  -- the "opened up" version of the Euclid's algorithm 
  worker : (b : Nat) -> (RecCall (Nat -> Nat) b) -> (a : Nat) -> Nat
  worker zero     _   a = a
  worker (suc b₁) rec a with mod₊w/proof a (suc b₁) (0<S b₁)
  ... | (r , prf) = rec r (≤⇒≤′ prf) (suc b₁)  

{-
-- it works, but it's very slow 
-- (of course, the modulo algorithm is *very* inefficient!)
ex1 = euclid (24 * 11 * 3) (24 * 4  * 7)
ex2 = euclid (24 * 4  * 7) (24 * 11 * 3) 
-}

--------------------------------------------------------------------------------
-- Euclid's algorithm with built-in proof

-- the predicate used in the induction
P : Nat -> Set
P b = (a : Nat) -> Σ Nat (λ g -> isGCD′ g a b)

-- Euclid's algorithm interleaved with proofs
euclid-w/proof : (a b : Nat) -> Σ Nat (λ g -> isGCD′ g a b)
euclid-w/proof a b = Nat-wfind worker b a where
  worker : (b : Nat) -> (IndCall P b) -> P b
  worker zero     _   a = (a , GCD′[n,0] a)
  worker (suc b₁) rec a with (0<S b₁)
  ... | pos with divMod₊w/proof′ a (suc b₁) pos 
  ... | (((q , r) , (prf , eq)) , (_ , modeq)) with rec r (≤⇒≤′ prf) (suc b₁)  
  ... | (g , gcd-prf)  rewrite (sym modeq) = g , GCD′-mod-rev pos gcd-prf

--------------------------------------------------------------------------------

