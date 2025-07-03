<!--
```agda
{-# OPTIONS --without-K --safe #-}

module merge-sort where

open import prelude
open import isomorphisms
open import List-functions
open import iso-utils
open import strict-total-order
open import sorting
open import natural-numbers-functions

```
-->

## Merge sort


```agda

data Tree (X : Type) : Type where
 leaf : X → Tree X
 fork : Tree X → Tree X → Tree X

l : List ℕ
l = 1 :: 2 :: 4 :: 7 :: 3 :: []

evens odds : {X : Type} → List X → List X

evens [] = []
evens (x :: xs) = x :: odds xs

odds [] = []
odds (x :: xs) = evens xs


interleave : {X : Type} → List X → List X → List X
interleave [] ys = ys
interleave (x :: xs) ys = x :: interleave ys xs

flatten : {X : Type} → Tree X → List X
flatten (leaf x)   = x :: []
flatten (fork l r) = interleave (flatten l) (flatten r)

eoi : {X : Type} (xs : List X) → interleave (evens xs) (odds xs)  ≡ xs
eoi []        = refl []
eoi (x :: xs) = goal
 where
  IH : interleave (evens xs) (odds xs) ≡ xs
  IH = eoi xs

  goal : x :: interleave (evens xs) (odds xs) ≡ x :: xs
  goal = ap (x ::_) IH

eol : {X : Type} (xs : List X) → length (evens xs) + length (odds xs) ≡ length xs
eol []        = refl 0
eol (x :: xs) = goal
 where
  IH : length (evens xs) + length (odds xs) ≡ length xs
  IH = eol xs

  goal :  suc (length (odds xs) + length (evens xs)) ≡ suc (length xs)
  goal = {!!}

evens-length  : {X : Type} (xs : List X) (n : ℕ) → length xs ≡ double n       → length (evens xs) ≡ n
odds-length   : {X : Type} (xs : List X) (n : ℕ) → length xs ≡ double n       → length (odds xs)  ≡ n
evens-length' : {X : Type} (xs : List X) (n : ℕ) → length xs ≡ suc (double n) → length (evens xs) ≡ suc n
odds-length'  : {X : Type} (xs : List X) (n : ℕ) → length xs ≡ suc (double n) → length (odds xs)  ≡ n

evens-length [] 0 p = refl 0
evens-length (x :: xs) (suc n) p = ap suc (odds-length' xs n (suc-is-injective p))

odds-length [] 0 p = refl 0
odds-length (x :: xs) (suc n) p = evens-length' xs n (suc-is-injective p)

evens-length' [] 0 ()
evens-length' (x :: xs) (suc n) p = ap suc (odds-length xs (suc n) (suc-is-injective p))

odds-length' [] 0 ()
odds-length' (x :: xs) n p = evens-length xs n (suc-is-injective p)

tree : {X : Type} → List X → Tree X
tree xs = {!!}

module _ where
 private
  div2' : (y : ℕ) → Σ x ꞉ ℕ , ((double x ≡ suc y) ∔ (suc (double x) ≡ suc y))
  div2' 0       = 0 , inr (refl 1)
  div2' (suc y) = g IH
   where
    IH : Σ x ꞉ ℕ , ((double x ≡ suc y) ∔ (suc (double x) ≡ suc y))
    IH = div2' y

    g : (Σ x ꞉ ℕ , ((double x  ≡ suc y)       ∔ (suc (double x) ≡ suc y)))
      → Σ x' ꞉ ℕ , ((double x' ≡ suc (suc y)) ∔ (suc (double x') ≡ suc (suc y)))
    g (x , inl p) = x     , inr (ap suc p)
    g (x , inr q) = suc x , inl (ap suc q)

  div2 : (y : ℕ) → Σ x ꞉ ℕ , ((double x ≡ y) ∔ (suc (double x) ≡ y))
  div2 0       = 0 , inl (refl 0)
  div2 (suc y) = div2' y

  half : ℕ → ℕ
  half n = fst (div2 n)

left right : ℕ → ℕ
left 0       = 1
left (suc n) = suc (suc (left n))
right n      = suc (left n)

NB-left-right : (n : ℕ) → left (suc n) ≡ suc (right n)
NB-left-right n = refl _

NB-right-left : (n : ℕ) → right (suc n) ≡ suc (left (suc n))
NB-right-left n = refl _

data 𝔹 : Type where
 Z : 𝔹
 L R : 𝔹 → 𝔹

Suc : 𝔹 → 𝔹
Suc Z     = L Z
Suc (L m) = R m
Suc (R m) = L (Suc m)

unary : 𝔹 → ℕ
unary Z     = 0
unary (L m) = left (unary m)
unary (R m) = right (unary m)

binary : ℕ → 𝔹
binary 0       = Z
binary (suc n) = Suc (binary n)

Length : {X : Type} → List X → 𝔹
Length []        = Z
Length (x :: xs) = Suc (Length xs)

merge-sort : {X : Type} (xs : List X) (b : 𝔹) → Length xs ≡ b → List X
merge-sort = {!!}

mirror :  𝔹 → 𝔹
mirror Z     = Z
mirror (L x) = R (mirror x)
mirror (R x) = L (mirror x)

mi : ℕ → ℕ
mi n = unary (mirror (binary n))

ni : ℕ → ℕ
ni n = mi n + mi n

to : ℕ → List ℕ
to 0       = []
to (suc n) = 0 :: map suc (to n)

ex = map mi (to 1000)

convert : 15 ≡ unary (L (L (L (L Z))))
convert = refl _

data T : Type where
 empty : T
 fork  : T → T → T

data 𝕃 (X : Type) : Type
 Z : 𝕃 X
 L : (x : X) → 𝕃 X → 𝕃 X
 R : (x : X) → 𝕃 X → 𝕃 X

lleft : {X : Type} → List X → List X
lleft xs = ?

data SortedList (X : Type) : Type where
 [] : SortedList X

```
