
-- home-grown natural numbers

open import Data.Empty
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

id : {A : Set} -> A -> A
id x = x

-- just a shorthand for composing equalities
infixr 3 _∙_
_∙_ : {A : Set} -> {a b c : A} -> (a ≡ b) -> (b ≡ c) -> (a ≡ c)
_∙_ = trans

--------------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

suc-injective : {n m : Nat} -> suc m ≡ suc n -> m ≡ n
suc-injective refl = refl

0≢suc : (a : Nat) -> 0 ≡ suc a -> ⊥
0≢suc _ ()

suc≢0 : (a : Nat) -> suc a ≡ 0 -> ⊥
suc≢0 _ ()

--------------------------------------------------------------------------------
-- ADDITION

infixl 5 _+_
_+_ : Nat -> Nat -> Nat
_+_ zero     m = m
_+_ (suc n₁) m = suc (n₁ + m)

≡+ : {a b : Nat} -> (c : Nat) -> (a ≡ b) -> (a + c ≡ b + c)
≡+ c eq = cong (\n -> n + c) eq

+≡ : {b c : Nat} -> (a : Nat) -> (b ≡ c) -> (a + b ≡ a + c)
+≡ a eq = cong (\n -> a + n) eq

n+0 : (n : Nat) -> n + 0 ≡ n
n+0 zero     = refl
n+0 (suc n₁) = cong suc (n+0 n₁)

n+suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
n+suc zero     m = refl
n+suc (suc n₁) m = cong suc (n+suc n₁ m)

+-assoc : {a b c : Nat} -> (a + b) + c ≡ a + (b + c)
+-assoc {zero  } {b} {c} = refl 
+-assoc {suc a₁} {b} {c} = cong suc (+-assoc {a₁} {b} {c})

+-comm : {n m : Nat} -> n + m ≡ m + n
+-comm {zero}   {m} = sym (n+0 m)
+-comm {suc n₁} {m} = cong suc (+-comm {n₁} {m}) ∙ sym (n+suc m n₁)

+-cancel-l : {a b c : Nat} -> (a + b ≡ a + c) -> b ≡ c
+-cancel-l {zero  } {b} {c} refl = refl
+-cancel-l {suc a₁} {b} {c} eq   = +-cancel-l (suc-injective eq)

+-cancel-r : {a b c : Nat} -> (a + c ≡ b + c) -> a ≡ b
+-cancel-r {a} {b} {c} eq = +-cancel-l (+-comm {c} {a} ∙ eq ∙ +-comm {b} {c})

+-cancel-l-0 : {a b : Nat} -> (a ≡ a + b) -> b ≡ 0
+-cancel-l-0 {a} {b} eq = sym (+-cancel-l {a} {0} {b} (n+0 a ∙ eq))

+≡0 : {a b : Nat} -> a + b ≡ 0 -> (a ≡ 0) × (b ≡ 0)
+≡0 {zero} {zero} refl = (refl , refl)

_⊕_ : {a b c d : Nat} -> (a ≡ c) -> (b ≡ d) -> a + b ≡ c + d
_⊕_ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

--------------------------------------------------------------------------------
-- MULTIPLICATION

infixl 6 _*_
_*_ : Nat -> Nat -> Nat
_*_ zero    m = zero
_*_ (suc n) m = m + n * m

≡* : {a b : Nat} -> (c : Nat) -> (a ≡ b) -> (a * c ≡ b * c)
≡* c eq = cong (\n -> n * c) eq

*≡ : {b c : Nat} -> (a : Nat) -> (b ≡ c) -> (a * b ≡ a * c)
*≡ a eq = cong (\n -> a * n) eq

n*0 : (n : Nat) -> n * 0 ≡ 0
n*0 zero     = refl
n*0 (suc n₁) = n*0 n₁

n*0≢suc : (n a : Nat) -> (n * 0) ≢ (suc a)
n*0≢suc n a rewrite (n*0 n) = 0≢suc a

n*1 : (n : Nat) -> n * 1 ≡ n
n*1 zero     = refl
n*1 (suc n₁) = cong suc (n*1 n₁)

1*n : (n : Nat) -> 1 * n ≡ n
1*n zero     = refl
1*n (suc n₁) = cong suc (1*n n₁)

n*suc : (n m : Nat) -> n * (suc m) ≡ n + n * m 
n*suc zero     m = refl
n*suc (suc n₁) m = cong suc
  ( +≡ m (n*suc n₁ m)
  ∙ sym (+-assoc {m} {n₁})
  ∙ ≡+ (n₁ * m) (+-comm {m} {n₁})
  ∙ +-assoc {n₁} {m}
  )

+*-distrib : {a b c : Nat} -> (a + b) * c ≡ a * c + b * c
+*-distrib {zero  } {b} {c} = refl
+*-distrib {suc a₁} {b} {c}
  = +≡ c (+*-distrib {a₁} {b} {c})
  ∙ sym (+-assoc {c})

*+-distrib : {a b c : Nat} -> a * (b + c) ≡ a * b + a * c
*+-distrib {a} {zero  } {c} = cong (\n -> n + a * c) (sym (n*0 a))
*+-distrib {a} {suc b₁} {c}
  = n*suc a (b₁ + c)
  ∙ +≡ a (*+-distrib {a} {b₁} {c})
  ∙ sym (+-assoc {a} {a * b₁} {_})
  ∙ ≡+ _ (sym (n*suc a b₁)) 
  
*-assoc : {a b c : Nat} -> (a * b) * c ≡ a * (b * c)
*-assoc {zero  } {b} {c} = refl 
*-assoc {suc a₁} {b} {c}
  = +*-distrib {b} {a₁ * b} {c}
  ∙ +≡ (b * c) (*-assoc {a₁} {b} {c})

*-comm : {n m : Nat} -> n * m ≡ m * n
*-comm {zero}   {m} = sym (n*0 m)
*-comm {suc n₁} {m} = +≡ m (*-comm {n₁} {m}) ∙ sym (n*suc m n₁)

*≡0 : {a b : Nat} -> a * b ≡ 0 -> (a ≡ 0) ⊎ (b ≡ 0)
*≡0 {zero} {_   } _ = inj₁ refl
*≡0 {_   } {zero} _ = inj₂ refl

*≡1 : {a b : Nat} -> a * b ≡ 1 -> (a ≡ 1) × (b ≡ 1)
*≡1 {suc a₁} {zero  } eq = ⊥-elim (n*0≢suc a₁ 0 eq)
*≡1 {suc a₁} {suc b₁} eq with suc-injective eq
... | eq₁ with +≡0 {b₁} {a₁ * suc b₁} eq₁
... | eq₂ , eq₃ with *≡0 {a₁} {suc b₁} eq₃
... | inj₁ eq₄ = cong suc eq₄ , cong suc eq₂

_⊗_ : {a b c d : Nat} -> (a ≡ c) -> (b ≡ d) -> a * b ≡ c * d
_⊗_ eq₁ eq₂ rewrite eq₁ | eq₂ = refl

--------------------------------------------------------------------------------
-- COMPARISON

infix 3 _≤_
infix 3 _≥_

data _≤_ : Nat -> Nat -> Set where
  0≤n : (n : Nat) -> 0 ≤ n
  S≤S : {n m : Nat} -> n ≤ m -> suc n ≤ suc m

_≥_ : Nat -> Nat -> Set
_≥_ b a = a ≤ b

n≤n : (n : Nat) -> n ≤ n
n≤n zero     = 0≤n zero
n≤n (suc n₁) = S≤S (n≤n n₁)

≤-unsuc : {n m : Nat} -> suc n ≤ suc m -> n ≤ m
≤-unsuc (S≤S ineq) = ineq

≤S : {n m : Nat} -> n ≤ m -> n ≤ suc m
≤S {zero  } {m}      _          = 0≤n (suc m)
≤S {suc n₁} {suc m₁} (S≤S ineq) = S≤S (≤S {n₁} {m₁} ineq)

n≤Sn : (n : Nat) -> n ≤ suc n
n≤Sn n = ≤S (n≤n n)

≤-refl : (n : Nat) -> n ≤ n
≤-refl = n≤n

≤-trans : {n m p : Nat} -> n ≤ m -> m ≤ p -> n ≤ p
≤-trans {n} {m} {p} (0≤n _) _ = 0≤n p
≤-trans {suc n₁} {suc m₁} {suc p₁} (S≤S ineq₁) (S≤S ineq₂) = S≤S (≤-trans ineq₁ ineq₂)

infixr 2 _∙≤_
_∙≤_ : {n m p : Nat} -> n ≤ m -> m ≤ p -> n ≤ p
_∙≤_ = ≤-trans

≤-antisym : {n m : Nat} -> n ≤ m -> m ≤ n -> n ≡ m
≤-antisym {zero  } {zero  } _ _ = refl
≤-antisym {suc n₁} {suc n₂} (S≤S ineq₁) (S≤S ineq₂) = cong suc (≤-antisym ineq₁ ineq₂)

Nat₊ : Set
Nat₊ = Σ Nat (λ n -> n ≥ 1)

pos≢0 : {a : Nat} -> a ≥ 1 -> a ≢ 0
pos≢0 {a} (S≤S {n} {m} _) = suc≢0 m

pos⇒suc : {a : Nat} -> a ≥ 1 -> Σ Nat (λ a₁ -> a ≡ suc a₁)
pos⇒suc {zero  } pos = ⊥-elim (pos≢0 {zero} pos refl)
pos⇒suc {suc a₁} _   = ( a₁ , refl )

-- If we do pattern matching, Agda automatically rewrites `n` to `suc n₁`.
-- This is often inconvenient, hence this helper function
Nat-case : (a : Nat) -> (a ≡ 0) ⊎ (a ≥ 1)
Nat-case zero     = inj₁ refl
Nat-case (suc a₁) = inj₂ (S≤S (0≤n a₁))

_≡∙≤_ : {n m p : Nat} -> n ≡ m -> m ≤ p -> n ≤ p
_≡∙≤_ refl le = le

_≤∙≡_ : {n m p : Nat} -> n ≤ m -> m ≡ p -> n ≤ p
_≤∙≡_ le refl = le

--------------------------------------------------------------------------------

infix 3 _<_
infix 3 _>_

_<_ : Nat -> Nat -> Set
_<_ n m = suc n ≤ m

_>_ : Nat -> Nat -> Set
_>_ b a = a < b

0<S : (n : Nat) -> 0 < suc n 
0<S n = S≤S (0≤n n)

n<Sn : (n : Nat) -> n < suc n
n<Sn n = ≤-refl (suc n)

-- suc n ≤ m ; suc m ≤ p ; 
<-trans : {n m p : Nat} -> n < m -> m < p -> n < p
<-trans ineq₁ ineq₂ = ineq₁ ∙≤ n≤Sn _ ∙≤ ineq₂ where

infixr 2 _∙<_
_∙<_ : {n m p : Nat} -> n < m -> m < p -> n < p
_∙<_ = <-trans

<-unsuc : {n m : Nat} -> suc n < suc m -> n < m
<-unsuc = ≤-unsuc

n≮0 : {n : Nat} -> n < 0 -> ⊥
n≮0 {zero}   () 
n≮0 {suc n₁} prf = n≮0 (<-trans (n<Sn n₁) prf)

n≮n : {n : Nat} -> n < n -> ⊥
n≮n {zero  } ()
n≮n {suc n₁} bad = n≮n {n₁} (≤-unsuc bad)

<⇒≤ : {a b : Nat} -> a < b -> a ≤ b
<⇒≤ {a} {suc b₁} ineq = ≤S (≤-unsuc ineq)

≡⇒≤ : {a b : Nat} -> a ≡ b -> a ≤ b
≡⇒≤ {a} {b} eq rewrite eq = n≤n b

le-gt-contra : {n m : Nat} -> (n ≤ m) -> (n > m) -> ⊥
le-gt-contra {zero  } {_}      le gt = n≮0 gt
le-gt-contra {suc n₁} {suc m₁} le gt = le-gt-contra (≤-unsuc le) (<-unsuc gt)

--------------------------------------------------------------------------------
-- decidable comparison with witness

data Ord : (n m : Nat) -> Set where
  LT : {n m : Nat} -> n < m -> Ord n m
  EQ : {n m : Nat} -> n ≡ m -> Ord n m
  GT : {n m : Nat} -> n > m -> Ord n m

suc-Ord : {n m : Nat} -> Ord n m -> Ord (suc n) (suc m)
suc-Ord (LT prf) = LT (S≤S prf)
suc-Ord (GT prf) = GT (S≤S prf)
suc-Ord (EQ prf) = EQ (cong suc prf)

compare : (n m : Nat) -> Ord n m
compare zero     zero     = EQ refl
compare zero     (suc m₁) = LT (0<S m₁)
compare (suc n₁) zero     = GT (0<S n₁)
compare (suc n₁) (suc m₁) = suc-Ord (compare n₁ m₁)

≤-dec : {n m : Nat} -> n ≤ m -> (n < m) ⊎ (n ≡ m)
≤-dec {n} {m} le with compare n m
... | LT lt = inj₁ lt
... | EQ eq = inj₂ eq
... | GT gt = ⊥-elim (le-gt-contra le gt)

--------------------------------------------------------------------------------
-- SUBTRACTION

difference : (a b : Nat) -> a ≥ b -> Σ Nat (λ k -> a ≡ b + k) 
difference a        zero     _    = a , refl
difference (suc a₁) (suc b₁) ineq with difference a₁ b₁ (≤-unsuc ineq)
... | k , prf = k , cong suc prf

minus : (a b : Nat) -> (a ≥ b) -> Nat
minus a b ge = proj₁ (difference a b ge)

--------------------------------------------------------------------------------
-- multiplicative cancellation (we need the ordering for this)

*-cancel-l-≤ : {a b c : Nat} -> (a > 0) -> (b ≤ c) -> (a * b ≡ a * c) -> b ≡ c
*-cancel-l-≤ {a} {b} {c} pos ineq eq with difference c b ineq
... | d , H rewrite H | *+-distrib {a} {b} {d} with +-cancel-l-0 {a * b} {a * d} eq
... | eq₂ with *≡0 {a} {d} eq₂ 
...      | inj₁ eq₃ = ⊥-elim (pos≢0 pos eq₃)
...      | inj₂ eq₃ rewrite eq₃ = sym (n+0 b)

*-cancel-l : {a b c : Nat} -> (a > 0) -> (a * b ≡ a * c) -> b ≡ c
*-cancel-l {a} {b} {c} pos eq with compare b c
... | EQ prf = prf
... | LT prf =      *-cancel-l-≤ {a} {b} {c} pos (<⇒≤ prf) eq
... | GT prf = sym (*-cancel-l-≤ {a} {c} {b} pos (<⇒≤ prf) (sym eq))

*-cancel-l-suc : {a b c : Nat} -> (suc a * b ≡ suc a * c) -> b ≡ c
*-cancel-l-suc {a} {b} {c} eq = *-cancel-l {suc a} {b} {c} (0<S a) eq

*-cancel-r : {a b c : Nat} -> (c > 0) -> (a * c ≡ b * c) -> a ≡ b
*-cancel-r {a} {b} {c} pos eq with (*-comm {c} {a} ∙ eq ∙ *-comm {b} {c})
... | eq₁ = *-cancel-l {c} {a} {b} pos eq₁

--------------------------------------------------------------------------------
-- interplay of arithmetic and comparison

a≤a+b : (a b : Nat) -> a ≤ a + b
a≤a+b a zero     rewrite (n+0   a   ) = n≤n a
a≤a+b a (suc b₁) rewrite (n+suc a b₁) = ≤S (a≤a+b a b₁)

b≤a+b : (a b : Nat) -> b ≤ a + b
b≤a+b a b = (a≤a+b b a) ≤∙≡ (+-comm {b} {a})

[a+b-b]≡a : (a b : Nat) -> minus (a + b) b (b≤a+b a b) ≡ a
[a+b-b]≡a a b with difference (a + b) b (b≤a+b a b)
... | b' , prf = sym (+-cancel-r {_} {_} {b} (prf ∙ +-comm {b} {b'}))

a≤a*b : (a b : Nat) -> (b ≡ 0) ⊎ (a ≤ a * b)
a≤a*b a zero     = inj₁ refl
a≤a*b a (suc b₁) rewrite (n*suc a b₁) = inj₂ (a≤a+b a (a * b₁))

b≤a*b : (a b : Nat) -> (a ≡ 0) ⊎ (b ≤ a * b)
b≤a*b a b with a≤a*b b a
... | inj₁ eq = inj₁ eq
... | inj₂ le = inj₂ (le ≤∙≡ (*-comm {b} {a}))

--------------------------------------------------------------------------------

+≤ : {a b : Nat} -> (c : Nat) -> (a ≤ b) -> (c + a ≤ c + b)
+≤ {a} {b} zero     ineq = ineq
+≤ {a} {b} (suc c₁) ineq = S≤S (+≤ {a} {b} c₁ ineq) 

≤+ : {a b : Nat} -> (c : Nat) -> (a ≤ b) -> (a + c ≤ b + c)
≤+ {a} {b} c ineq = (+-comm {a} {c} ≡∙≤ (+≤ c ineq)) ≤∙≡ +-comm {c} {b}

_⊕≤_ : {a b c d : Nat} -> (a ≤ c) -> (b ≤ d) -> (a + b ≤ c + d)
_⊕≤_ {a} {b} {c} {d} ineq₁ ineq₂ = (≤+ b ineq₁) ∙≤ (+≤ c ineq₂)

*≤ : {a b : Nat} -> (c : Nat) -> (a ≤ b) -> (c * a ≤ c * b)
*≤ {a} {b} zero     _    = n≤n 0
*≤ {a} {b} (suc c₁) ineq with *≤ {a} {b} c₁ ineq
... | ineq₁ = ineq ⊕≤ ineq₁

*< : {a b : Nat} -> (c : Nat) -> (c > 0) -> (a < b) -> (c * a < c * b)
*< {a} {b} c cpos ineq with pos⇒suc cpos
... | c₁ , eq rewrite eq with *≤ c₁ ineq
... | ineq₂ rewrite (n*suc c₁ a) = ineq ⊕≤ (b≤a+b c₁ (c₁ * a) ∙≤ ineq₂)

*-≤-cancel-l : {a b c : Nat} -> (c > 0) -> (c * a ≤ c * b) -> a ≤ b
*-≤-cancel-l {a} {b} {c} cpos ineq with compare a b
... | LT lt = (<⇒≤ lt)
... | EQ eq = (≡⇒≤ eq) 
... | GT gt with *< c cpos gt
...   | bad = ⊥-elim (le-gt-contra ineq bad)

--------------------------------------------------------------------------------
