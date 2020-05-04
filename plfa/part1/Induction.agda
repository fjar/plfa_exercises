module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


-- Exercise operators

-- Logical 'and' and logical 'or' have an identity, are associative,
-- commutative and 'and' distributes over 'or'.
-- Matrix multiplication has an identity and is associative but it is not commutative.


-- Exercise finite-+-assoc

-- In the beginning, we know nothing

-- On the first day, we know zero
-- 0 : ℕ

-- On the second day, we know one and associativity of 0
-- 0 : ℕ
-- 1 : ℕ   (0 + 0) + 0 = 0 + (0 + 0)

-- On the third day, we know two and associativity of 0 and 1
-- 0 : ℕ
-- 1 : ℕ   (0 + 0) + 0 = 0 + (0 + 0)
-- 2 : ℕ   (0 + 1) + 0 = 0 + (1 + 0)  (0 + 0) + 1 = 0 + (0 + 1)

-- On the fourth day, we know tree and associativity of 0, 1 and 2
-- 0 : ℕ
-- 1 : ℕ   (0 + 0) + 0 = 0 + (0 + 0)
-- 2 : ℕ   (1 + 0) + 0 = 1 + (0 + 0)  (0 + 1) + 0 = 0 + (1 + 0)  (0 + 0) + 1 = 0 + (0 + 1)
--         (1 + 1) + 0 = 1 + (1 + 0)  (1 + 0) + 1 = 1 + (0 + 1)  (0 + 1) + 1 = 0 + (1 + 1)
--         (1 + 1) + 1 = 1 + (1 + 1)
-- 3 : ℕ   (2 + 0) + 0 = 2 + (0 + 0)  (0 + 2) + 0 = 0 + (2 + 0)  (0 + 0) + 2 = 0 + (0 + 2)
--         (2 + 1) + 0 = 2 + (1 + 0)  (2 + 0) + 1 = 2 + (0 + 1)  (1 + 2) + 0 = 1 + (2 + 0)  (0 + 2) + 1 = 0 + (2 + 1)  (1 + 0) + 2 = 1 + (0 + 2)  (0 + 1) + 2 = 0 + (1 + 2)
--         (2 + 1) + 1 = 2 + (1 + 1)  (1 + 2) + 1 = 1 + (2 + 1)  (1 + 1) + 2 = 1 + (1 + 2)
--         (2 + 2) + 0 = 2 + (2 + 0)  (2 + 0) + 2 = 2 + (0 + 2)  (0 + 2) + 2 = 0 + (2 + 2)
--         (2 + 2) + 1 = 2 + (2 + 1)  (2 + 1) + 2 = 2 + (1 + 2)  (1 + 2) + 2 = 1 + (2 + 2)
--         (2 + 2) + 2 = 2 + (2 + 2)


-- Exercise +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc′ m n p)  ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm′ m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc′ n m p ⟩
    n + (m + p)
  ∎


-- Exercise *-distrib-+
*-distrib : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib zero n p = refl
*-distrib (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc′ p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎


-- Exercise *-assoc
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    suc m * n * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib n (m * n) p ⟩
    n * p + m * n * p
  ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ≡⟨⟩
    suc m * (n * p)
  ∎


-- Excercise *-comm
*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc m) rewrite *-zeroʳ m = refl

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡  m + m * n
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n rewrite *-comm m n | *-suc n m = refl


-- Exercise 0∸n≡0
0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl


-- Exercise ∸-+-assoc
lemma-∸ : ∀ ( m n p : ℕ) → m ∸ n ∸ suc p ≡ m ∸ suc (n + p)
lemma-∸ zero zero p = refl
lemma-∸ zero (suc n) p = refl
lemma-∸ (suc m) zero p = refl
lemma-∸ (suc m) (suc n) p rewrite lemma-∸ m n p = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc m (suc n) zero rewrite +-identity′ n = refl
∸-+-assoc zero (suc n) (suc p) = refl
∸-+-assoc (suc m) (suc n) (suc p) rewrite ∸-+-assoc m n p | +-suc′ n p | lemma-∸ m n p = refl


-- Exercise +*^
^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity′ (m ^ p)  = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

*-swap : ∀ ( m n p : ℕ) → m * (n * p)  ≡ n * (m * p)
*-swap m n p =
  begin
    m * (n * p)
  ≡⟨ sym (*-assoc m n p) ⟩
    m * n * p
  ≡⟨ cong (_* p) (*-comm m n) ⟩
    n * m * p
  ≡⟨ *-assoc n m p ⟩
    n * (m * p)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p =
  begin
    m * n * ((m ^ p) * (n ^ p))
  ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩
    m * (n * ((m ^ p) * (n ^ p)))
  ≡⟨ cong (m *_) (*-swap n (m ^ p) (n ^ p)) ⟩
    m * ((m ^ p) * (n * (n ^ p)))
  ≡⟨ sym ( *-assoc m (m ^ p) (n * (n ^ p))) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ∎

lemma-^ : ∀ (m : ℕ) → 1 ^ m ≡ 1
lemma-^ zero = refl
lemma-^ (suc m) rewrite lemma-^ m | +-identity′ 1 = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p rewrite lemma-^ p = refl
^-*-assoc m (suc n) p rewrite ^-distribʳ-* m (m ^ n) p | ^-*-assoc m n p | sym (^-distribˡ-+-* m p (n * p)) = refl
{-
^-*-assoc m (suc n) p =
  begin
    (m ^ suc n) ^ p
  ≡⟨⟩
    (m * (m ^ n)) ^ p
  ≡⟨  ^-distribʳ-* m (m ^ n) p ⟩
    (m ^ p) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ p) *_) (^-*-assoc m n p) ⟩
    (m ^ p) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m p (n * p)) ⟩
    m ^ (p + n * p)
  ≡⟨⟩
    m ^ (suc n * p)
  ∎
-}


-- Excersice Bin-laws

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * from b
from (b I) = 2 * from b + 1

bin-law-1 : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-law-1 ⟨⟩ = refl
bin-law-1 (b O) rewrite +-identity′ (from b) | +-comm′ (from b + from b) 1 = refl
bin-law-1 (b I) rewrite bin-law-1 b | +-identity′ (from b) | +-comm′ 1 (from b) | +-assoc′ (from b) (from b) 1 = refl
    
-- bin-law-2 : ∀ (b : Bin) → to (from b) ≡ b
-- to (from ⟨⟩) = ⟨⟩ O

bin-law-3 : ∀ (n : ℕ) → from (to n) ≡ n
bin-law-3 zero = refl
bin-law-3 (suc n) rewrite bin-law-1 (to n) | bin-law-3 n = refl
