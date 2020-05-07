import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm; +-suc)


-- Exercise orderings
-- preorder, not partial:
--    comparison of strings by length, ≤ₛ
--    i.e. s1 ≤ₛ s2 iif len(s1) ≤ len(s2)
--    For two diferent strings of the same length, we have
--    s1 ≤ₛ s2 and s2 ≤ₛ s1, but s1 ≢ s2
--
-- partial order, not total:
--    in a tree of nodes, ≤ₜ
--    where n1 ≤ₜ n2 if we find n1 in the path that goes from
--    the root node to n2.
--    For nodes n1 and n2 in different branches, we cannot
--    say neither n1 ≤ₜ n2 nor n2 ≤ₜ n1.


data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_


≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


-- Exercise ≤-antisym-cases
-- In a proof of ≤-antisym m≤n n≤m, if an argument is z≤n, i.e type 0 ≤ n
-- then the other argument must be of type n ≤ 0, i.e. 0 ≤ 0, so it is also z≤n.
-- Thus, either both arguments are z≤n or both are s≤s.

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero _ _ p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


-- Exercise *-mono-≤
*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n
    

-- Excercise <-trans
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)



data _>_ : ℕ → ℕ → Set where

  s>z : ∀ {n : ℕ}
      ------------
    → suc n > zero

  s>s : ∀ {m n : ℕ}
    → m > n
      -------------
    → suc m > suc n


data Trychotomy (m n : ℕ) : Set where

  frwd :
      m < n
      ---------
    → Trychotomy m n

  equl :
      m ≡ n
      ---------
    → Trychotomy m n
    
  flip :
      m > n
      ---------
    → Trychotomy m n


-- Exercise tricothomy
<-weak-trychotomy : ∀ (m n : ℕ) → Trychotomy m n
<-weak-trychotomy zero zero = equl refl
<-weak-trychotomy zero (suc n) = frwd z<s
<-weak-trychotomy (suc m) zero = flip s>z
<-weak-trychotomy (suc m) (suc n) with <-weak-trychotomy m n
...                                  | frwd m<n = frwd (s<s m<n)
...                                  | equl m≡n = equl (cong suc m≡n)
...                                  | flip m>n = flip (s>s m>n)


-- Exercise +-mono-<
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
  ----------
  → n + p < n + q
+-monoʳ-< zero _ _ p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  ----------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)


-- Excercise ≤-iff-<
≤-if-< : ∀ {m n : ℕ}
  → m < n
  -----------
  → suc m ≤ n
≤-if-< {zero}  {suc n}      m<n  = s≤s z≤n
≤-if-< {suc m} {suc n} (s<s m<n) = s≤s (≤-if-< m<n)

<-if-≤ : ∀ {m n : ℕ}
  → suc m ≤ n
  -----------
  → m < n
<-if-≤ {zero}  {suc n}      m≤n  = z<s
<-if-≤ {suc m} {suc n} (s≤s m≤n) = s<s (<-if-≤ m≤n)


-- Exercise <-trans-revisited
lemma-< : ∀ {m n : ℕ}
  → suc m < n
  -----------
  → m < n
lemma-< {zero}  {suc n}      m+1<n  = z<s
lemma-< {suc m} {suc n} (s<s m+1<n) = s<s (lemma-< m+1<n)

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans-revisited m<n n<p = lemma-< (<-if-≤ (≤-trans (s≤s (≤-if-< m<n)) (≤-if-< n<p)))



data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
  
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)


-- Exercise o+o≡e
e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----------
  → even (m + n)

e+o≡o zero     on = on
e+o≡o (suc em) on = suc (o+o≡e em on)

o+o≡e (suc em) on = suc (e+o≡o em on)



data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl
_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl
_ : inc (⟨⟩ I O) ≡  ⟨⟩ I I
_ = refl
_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = from b + from b
from (b I) = from b + from b + 1

-- Excercise Bin-predicates

data One : Bin → Set where

  Ï   :
    -----------
    One (⟨⟩ I)


  _Ô : ∀ {b : Bin}
    → One b
    -----------
    → One (b O)

  _Î : ∀ {b : Bin}
    → One b
    -----------
    → One (b I)


one-inc : ∀ {b : Bin}
  → One b
  -------------
  → One (inc b)
  
one-inc Ï = Ï Ô
one-inc (b Ô) = b Î
one-inc (b Î) = (one-inc b) Ô


data Can : Bin → Set where

  Ô   :
    ----------
    Can (⟨⟩ O)

  I⋯ : ∀ {b : Bin}
    → One b
    ----------
    → Can b


can-inc : ∀ {b : Bin}
  → Can b
  -------------
  → Can (inc b)
can-inc Ô = I⋯ Ï
can-inc (I⋯ b) = I⋯ (one-inc b)

can-to : ∀ (n : ℕ)
  ------------
  → Can (to n)
can-to zero = Ô
can-to (suc n) = can-inc (can-to n)

can-id : ∀ {b : Bin}
  → Can b
  -----------------
  → to (from b) ≡ b
can-id cb = {!!}  -- pending
