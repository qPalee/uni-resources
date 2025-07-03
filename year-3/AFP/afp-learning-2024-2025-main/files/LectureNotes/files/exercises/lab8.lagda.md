# Week 8 - Partial Orders and Sorting

```agda
{-# OPTIONS --without-K --safe #-}
module exercises.lab8 where
open import prelude
open import partial-orders hiding (<-irreflexive ; <-transitive ; total-implies-connected)
open import List-functions
open import Fin
open import sorting
open import subtypes
open import isomorphisms
open import binary-sums-equality
```

## Part 1. Strict Orders

Given a partial order `_≤_`, the corresponding *strict* order `_<_` is
given by defined by `x < y = (x ≤ y) × ¬ (x ≡ y)`.  This definition is
exported by the definition of `PartialOrder` so that it is in scope
below.

```agda
module _ {X : Type} (ρ : PartialOrder X) where
  open PartialOrder ρ

  <-irreflexive : (x : X) → ¬ (x < x)
  <-irreflexive = {!!}

  <-transitive : (x y z : X) → x < y → y < z → x < z
  <-transitive = {!!}
```

Recall that a partial order is *total* if any two elements can be
compared.  Show that if the relation `_≤_` is total, then the relation
`_<_` is *connected* in the following sense:

```agda
  total-implies-connected : is-total ρ → (x y : X) → ¬ (x ≡ y) → (x < y) ∔ (y < x)
  total-implies-connected = {!!}
```

## Part 2. Mapping monotone functions over lists

Let's suppose that we have *two* partially ordered types `X` and `Y`.  We'll
say a function `f : X → Y` is monotone if it preserves the order in the following sense:

```agda
module _ {X Y : Type} (ρX : PartialOrder X) (ρY : PartialOrder Y) where

  open PartialOrder ρX renaming (_≤_ to _≤[X]_)
  open PartialOrder ρY renaming (_≤_ to _≤[Y]_)

  is-monotone : (X → Y) → Type
  is-monotone f = (x₀ x₁ : X) → x₀ ≤[X] x₁ → f x₀ ≤[Y] f x₁
```

Show that if a list `xs : List X` is sorted, then mapping a monotone function over
the list results in another sorted list.

```
  map-of-monotone-preserves-sorted : (f : X → Y)
    → is-monotone f
    → (xs : List X)
    → Sorted ρX xs
    → Sorted ρY (map f xs)
  map-of-monotone-preserves-sorted = {!!}
```

## Part 3. Partial Order on Positions

Contstruct a partial order on the positions of a list.

**Hint**: to prove that the partial order is univalent, prove that the
positions of a list always form a set.  For this, check out the function
`∔-is-set` in [this file](../binary-sums-equality.lagda.md).  You may also
wish to examine the proof that `𝟚` is a set [here](subtypes.lagda.md).

```agda
Pos-PartialOrder : {X : Type} (xs : List X) → PartialOrder (Pos xs)
Pos-PartialOrder = {!!}
```

## Part 4. Monotonicity of retrieving elements

Using the partial order constructed above, show that retriving elements from
a sorted list is a monotone map.

```agda
module _ {X : Type} (ρ : PartialOrder X) where
  open PartialOrder ρ

  !!-is-monotone : (xs : List X) (s : Sorted ρ xs)
    → is-monotone (Pos-PartialOrder xs) ρ (λ p → xs !! p)
  !!-is-monotone = {!!}

```
