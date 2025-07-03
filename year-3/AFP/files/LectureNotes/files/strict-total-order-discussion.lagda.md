<!--
```agda
{-# OPTIONS --without-K --safe #-}

module strict-total-order where

open import prelude
open import decidability
open import natural-numbers-functions
             renaming (_≤_ to _≤ₙ_;
                       _≥_ to _≥ₙ ;
                       max to maxₙ ;
                       min to minₙ)
open import List-functions
```
-->

## Strict Total Orders

For sorting elements of a general type `X`, we will need to have some
kind of ordering relation.  In many functional languages, such an
ordering takes the form of a function `compare : X → X → Bool`.  which
calculates a whether the provided elements are strictly less than or
less than or equal to each other.  While such a function is in fact
sufficient for many classical sorting algorithms, just the comparison
function itself is usually not sufficient to prove nice properties.

In a dependently typed language such as Agda, however, we can
additionally state the axioms we would like our ordering relation to
satisfy.  Here is one such possible axiomatization:

```agda
record StrictTotalOrder (X : Type) : Type₁ where
  field
    _<_ : X → X → Type

    irreflexive : (x : X) → ¬ (x < x)
    transitive : {x y z : X} → x < y → y < z → x < z
    connected : {x y : X} → ¬ (x ≡ y) → (x < y) ∔ (y < x)

    ≡-is-decidable : has-decidable-equality X
```

Some derived constructions:

```agda
  _>_ : X → X → Type
  x > y = y < x

  _≤_ : X → X → Type
  x ≤ y = (y ≡ x) ∔ (x < y)

  _≥_ : X → X → Type
  x ≥ y = y ≤ x
```


Some useful facts follow essentially immediately from the definition,
for example that any such relation is antisymmetric:

```agda
  irreflexive' : (x y : X) → x ≡ y → ¬ (x < y)
  irreflexive' x x (refl x) = irreflexive x

  antisymmetric : (x y : X) → x < y → ¬ (y < x)
  antisymmetric x y x<y y<x = irreflexive x (transitive x<y y<x)
```

and that the trichotomoy holds: either `x < y` or `y < x` or `x ≡ y`.

```agda
  trichotomy : (x y : X) → (x < y) ∔ ((x ≡ y) ∔ (y < x))
  trichotomy x y with ≡-is-decidable x y
  trichotomy x y | inl x≡y = inr (inl x≡y)
  trichotomy x y | inr ¬x≡y with connected ¬x≡y
  trichotomy x y | inr ¬x≡y | inl x<y = inl x<y
  trichotomy x y | inr ¬x≡y | inr y<x = inr (inr y<x)

  not-<-and-not-≡-give-> : (x y : X) → ¬ (x < y) → ¬ (x ≡ y) → y < x
  not-<-and-not-≡-give-> x y ¬x<y ¬x≡y with connected ¬x≡y
  not-<-and-not-≡-give-> x y ¬x<y ¬x≡y | inl x<y = 𝟘-elim (¬x<y x<y)
  not-<-and-not-≡-give-> x y ¬x<y ¬x≡y | inr y<x = y<x

  not-<-gives-≥ : (x y : X) → ¬ (x < y) → x ≥ y
  not-<-gives-≥ x y ¬x<y with ≡-is-decidable x y
  not-<-gives-≥ x y ¬x<y | inl x≡y  = inl x≡y
  not-<-gives-≥ x y ¬x<y | inr ¬x≡y = inr (not-<-and-not-≡-give-> x y ¬x<y ¬x≡y)
```

```agda
  <-is-decidable : (x y : X) → is-decidable (x < y)
  <-is-decidable x y with ≡-is-decidable x y
  <-is-decidable x y | inl x≡y = inr (λ x<y → irreflexive' x y x≡y x<y)
  <-is-decidable x y | inr ¬x≡y with connected ¬x≡y
  <-is-decidable x y | inr ¬x≡y | inl x<y = inl x<y
  <-is-decidable x y | inr ¬x≡y | inr y<x = inr (λ x<y → irreflexive x (transitive x<y y<x))

  ≤-is-decidable : (x y : X) → is-decidable (x ≤ y)
  ≤-is-decidable x y = ∔-preserves-decidability
                        (≡-is-decidable y x)
                        (<-is-decidable x y)

  max : X → X → X
  max x y with <-is-decidable x y
  max x y | inl x<y  = y
  max x y | inr ¬x<y = x

  max-upper-boundₗ : (x y : X) → x ≤ max x y
  max-upper-boundₗ x y with <-is-decidable x y
  max-upper-boundₗ x y | inl x<y   = inr x<y
  max-upper-boundₗ x y | inr ¬x<y  = inl (refl x)

  max-upper-boundᵣ : (x y : X) → y ≤ max x y
  max-upper-boundᵣ x y with <-is-decidable x y
  max-upper-boundᵣ x y | inl x<y   = inl (refl y)
  max-upper-boundᵣ x y | inr ¬x<y with ≡-is-decidable x y
  max-upper-boundᵣ x y | inr ¬x<y | inl x≡y = inl x≡y
  max-upper-boundᵣ x y | inr ¬x<y | inr ¬x≡y = inr (not-<-and-not-≡-give-> x y ¬x<y ¬x≡y)

  <-is-decidable' : (x y : X) → is-decidable (x < y)
  <-is-decidable' x y = ∔-nondep-elim
                         (λ (e : x ≡ y) → inr (λ x<y → irreflexive' x y e x<y))
                         (λ (ν : ¬ (x ≡ y))
                               → ∔-nondep-elim
                                  (λ (l : x < y) → inl l)
                                  (λ (l : y < x) → inr (λ (m : x < y) → irreflexive x (transitive m l)))
                                  (connected ν))
                         (≡-is-decidable x y)

  ≤-is-decidable' : (x y : X) → is-decidable (x ≤ y)
  ≤-is-decidable' x y = ∔-preserves-decidability
                        (≡-is-decidable y x)
                        (<-is-decidable' x y)


  max-helper : (x y : X) → is-decidable (x < y) → X
  max-helper x y (inl x<y) = y
  max-helper x y (inr ¬x<y) = x

  max' : X → X → X
  max' x y = max-helper x y (<-is-decidable' x y)

  max-helper-property : (x y : X) → x < y → (d : is-decidable (x < y)) → max-helper x y d ≡ y
  max-helper-property x y x<y (inl _) = refl y
  max-helper-property x y x<y (inr ¬x<y) = 𝟘-elim {λ _ → x ≡ y} (¬x<y x<y)

  max'-property : (x y : X) → x < y → max' x y ≡ y
  max'-property x y x<y = max-helper-property x y x<y (<-is-decidable' x y)

{-
  max' : X → X → X
  max' x y = ∔-nondep-elim
              (λ (l : x < y) → y)
              (λ (ν : ¬ (x < y)) → x)
              (<-is-decidable' x y)

  ∔-non-dep-left-case : {A B C : Type}
                        (f : A → C)
                        (g : B → C)
                        (z : A ∔ B)
                        (a : A)
                      →  z ≡ inl a
                      → ∔-nondep-elim f g z ≡ f a
  ∔-non-dep-left-case {A} {B} {C} f g .(inl a) a (refl .(inl a)) = refl (f a)
-}


  max-upper-boundᵣ' : (x y : X) → y ≤ max' x y
  max-upper-boundᵣ' x y = ∔-nondep-elim
                           (λ (l : x < y)    → inl (max'-property x y l))
                           (λ (ν : ¬ (x < y))
                                 → ∔-nondep-elim
                                    (λ (e : x ≡ y) → {!!})
                                    (λ (ne : ¬ (x ≡ y)) → inl {!!})
                                    (≡-is-decidable x y ))
                           (<-is-decidable' x y)
                        where
                         h : ¬ (y < max' x y) → x ≡ y →  (max' x y ≡ y) ∔ (y < max' x y)
                         h ν (refl .x) = {!!}

  max-upper-boundᵣ'' : (x y : X) → y ≤ max' x y
  max-upper-boundᵣ'' x y = ∔-nondep-elim
                           (λ (l : x < y)    → {!!}) -- inl (∔-non-dep-left-case _ _ {!!} l {!!}))
                           (λ (ν : ¬ (x < y))
                                 → ∔-nondep-elim
                                    (λ (e : x ≡ y) → {!!})
                                    (λ (ne : ¬ (x ≡ y)) → inl {!!})
                                    (≡-is-decidable x y ))
                           (<-is-decidable' x y)
                        where
                         h : ¬ (y < max' x y) → x ≡ y →  (max' x y ≡ y) ∔ (y < max' x y)
                         h ν (refl .x) = {!!}

  max-least-upper-bound : (x y u : X) → y ≤ u → x ≤ u → max x y ≤ u
  max-least-upper-bound x y u y≤u x≤u with <-is-decidable x y
  max-least-upper-bound x y u y≤u x≤u | inl x<y  = y≤u
  max-least-upper-bound x y u y≤u x≤u | inr ¬x<y = x≤u

  min : X → X → X
  min x y with <-is-decidable x y
  min x y | inl x<y  = x
  min x y | inr ¬x<y = y
```


Being able to calculate which of these cases we are in is a key
ingredient in constructing our sorting algorithms.

## The Strict Order on the Natural Numbers

Not surprisingly, the natural numbers can be endowed with a strict
total ordering.  The proofs of the required properties are all
reasonably straightforward by induction.

```agda
data _<ₙ_ : ℕ → ℕ → Type where
  <-zero : {n : ℕ} → zero <ₙ suc n
  <-suc  : {n m : ℕ} → n <ₙ m → suc n <ₙ suc m

<ₙ-trans : {x y z : ℕ} → x <ₙ y → y <ₙ z → x <ₙ z
<ₙ-trans <-zero    (<-suc q) = <-zero
<ₙ-trans (<-suc p) (<-suc q) = <-suc (<ₙ-trans p q)

<ₙ-irreflexive : (x : ℕ) → ¬ (x <ₙ x)
<ₙ-irreflexive (suc x) (<-suc x<x) = <ₙ-irreflexive x x<x

<ₙ-connected : {x y : ℕ} → ¬ (x ≡ y) → (x <ₙ y) ∔ (y <ₙ x)
<ₙ-connected {zero}  {zero} ¬x≡y  = 𝟘-elim (¬x≡y (refl zero))
<ₙ-connected {zero}  {suc y} ¬x≡y = inl <-zero
<ₙ-connected {suc x} {zero} ¬x≡y  = inr <-zero
<ₙ-connected {suc x} {suc y} ¬x≡y =
 ∔-elim _
  (λ x<y → inl (<-suc x<y))
  (λ y<x → inr (<-suc y<x))
  (<ₙ-connected λ p → ¬x≡y (ap suc p))

ℕ-StrictTotalOrder : StrictTotalOrder ℕ
ℕ-StrictTotalOrder =
  record
    { _<_ = _<ₙ_
    ; ≡-is-decidable = ℕ-has-decidable-equality
    ; irreflexive = <ₙ-irreflexive
    ; transitive = <ₙ-trans
    ; connected = <ₙ-connected
    }
```
We also record the following lemma which will be of use later on:

```agda

<ₙ-lem : (n : ℕ) → n <ₙ suc n
<ₙ-lem zero    = <-zero
<ₙ-lem (suc n) = <-suc (<ₙ-lem n)

```

## Sorted Lists

Now that we have a notion of ordering on a type, we can say what we mean
for a list to be sorted.  We do so using the following inductively
defined predicate.

```agda
module _ {X : Type} (τ : StrictTotalOrder X) where
  open StrictTotalOrder τ

  data Sorted : List X → Set where
    nil-sorted  : Sorted []
    sing-sorted : {x : X} → Sorted (x :: [])
    adj-sorted  : {y x : X} {xs : List X}
                → Sorted (x :: xs)
                → (x ≡ y) ∔ (y < x)
                → Sorted (y :: x :: xs)
```

The first two constructors simply state that both the empty list and
any list containing a single element are automatically sorted.  The
final constructor says that if we are trying to adjoin an element `y`
to the list `x :: xs` which is known to be sorted, then for the
resulting list to be sorted we must also provide evidence that `y ≤ x`.

```agda
example : Sorted ℕ-StrictTotalOrder (1 :: 2 :: 3 :: 4 :: [])
example = adj-sorted {ℕ} {ℕ-StrictTotalOrder} {1} {2}
            (adj-sorted {ℕ}  {ℕ-StrictTotalOrder} {2} {3}
             (adj-sorted {ℕ} {ℕ-StrictTotalOrder} {3} {4}
               sing-sorted (inr (<-suc (<-suc (<-suc <-zero)))))
             (inr (<-suc (<-suc <-zero))))
            (inr (<-suc <-zero))

example' : Sorted ℕ-StrictTotalOrder (1 :: 1 :: 3 :: 4 :: [])
example' = adj-sorted
             (adj-sorted
              (adj-sorted sing-sorted (inr (<-suc (<-suc (<-suc <-zero)))))
              (inr (<-suc <-zero)))
             (inl (refl 1))
```
