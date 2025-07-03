<!--
```agda
{-# OPTIONS --without-K --safe #-}

module well-founded where

open import prelude
open import decidability
open import natural-numbers-functions
open import List-functions
open import strict-total-order

```
-->

# Well-Founded Induction

Let's see what happens when we attempt to define another common
sorting algoritm: quicksort.

<!--
```agda
module _ (X : Type) (τ : StrictTotalOrder X) where
  open StrictTotalOrder τ
  private
```
-->

We begin with the partition funtion. This function can be implemented
easily enough as follows:

```agda
    partition : X → List X → List X × List X
    partition x [] = [] , []
    partition x (y :: l) with trichotomy x y | partition x l
    partition x (y :: l) | inl x<y  | (left , right) = left , y :: right
    partition x (y :: l) | inr ¬x<y | (left , right) = y :: left , right
```

And now it is tempting to continue directly to the definition of
quicksort as in the following:

```agda
{-
    quicksort : List X → List X
    quicksort [] = []
    quicksort (x :: l) with partition x l
    quicksort (x :: l) | left , right =
      (quicksort left) ++ (x :: quicksort right)
-}
```

However, if you uncomment this code, you will find that Agda complains
that it cannot see that it terminates.  The reason for this is that we
have made a recursive call but **not to a structurally smaller** piece
of the data we have matched on.  Instead, we have called out to the
"partition" function and made a recursive call on the resulting pair
of lists.  For all Agda knows, perhaps this function quadruples the
size of the input list (there are certainly functions which will do
this ...) in which case the algorithm will never terminate.

On the other hand, **we** know that partitioning the list into two
pieces will not increase its size.  We need a way to justify this to
Agda.

One such tool is called *well-founded induction*.

## Accessibility

Given a type `X` and a relation `_<_`, we will say that an element `x`
is **accessible** if every element it is related to is also
accessible.  This takes the form of the following definition:

```agda
module _ {X : Type} (_<_ : X → X → Type) where

  data Acc (x : X) : Type where
    acc : (ϕ : ∀ y → y < x → Acc y) → Acc x

  acc⁻¹ : {x : X} → Acc x → ∀ y → y < x → Acc y
  acc⁻¹ (acc ϕ) = ϕ
```

The usefulness of this definition is that it allows us to define the following
elimination principle for accessible elements:

```agda
  acc-elim : (P : (x : X) → Type)
           → (p : (x : X) (ϕ : ∀ y → y < x → P y) → P x)
           → (x : X) (a : Acc x) → P x
  acc-elim P r x (acc ϕ) = r x (λ y (l : y < x) → acc-elim P r y (ϕ y l))
```

The idea here is that we want to prove some predicate `P x`.  Suppose
we can show that for any `x`, if the predicate holds on all `y` such
that `y < x`, then it also holds for `x`.  Then the predicate holds
for any `x` which is accessible.

The most useful case will be when we have a predicate for which *every*
element is accessible.  In this case, we say the relation is **well-founded**:

```agda
  WF : Type
  WF = (x : X) → Acc x
```

When the relation is well-founded, the elimination principle from above tells
us that we can prove a predicate `P x` by showing that `P x` holds whenever
`P y` holds for all `y < x`.

```agda
  wf-ind : (P : X → Type) (ω : WF)
         → (p : (x : X) (ϕ : ∀ y → (y < x) → P y) → P x)
         → (x : X) → P x
  wf-ind P ω p x = acc-elim P p x (ω x)
```
## The Well-foundedness of the total order on ℕ

Let's show that the strict total order on ℕ is well-founded.

First some examples:

```agda
nothing-is-less-than-0 : (x : ℕ) → ¬ (x <ₙ 0)
nothing-is-less-than-0 x ()

0-is-accessible : Acc _<ₙ_ 0
0-is-accessible = acc h
 where
  h : (y : ℕ) → y <ₙ 0 → Acc _<ₙ_ y
  h y ()

1-is-accessible : Acc _<ₙ_ 1
1-is-accessible = acc h
 where
  h : (y : ℕ) → y <ₙ 1 → Acc _<ₙ_ y
  h 0 <-zero = 0-is-accessible

2-is-accessible : Acc _<ₙ_ 2
2-is-accessible = acc h
 where
  h : (y : ℕ) → y <ₙ 2 → Acc _<ₙ_ y
  h 0 <-zero         = 0-is-accessible
  h 1 (<-suc <-zero) = 1-is-accessible

3-is-accessible : Acc _<ₙ_ 3
3-is-accessible = acc h
 where
  h : (y : ℕ) → y <ₙ 3 → Acc _<ₙ_ y
  h 0 <-zero                 = 0-is-accessible
  h 1 (<-suc <-zero)         = 1-is-accessible
  h 2 (<-suc (<-suc <-zero)) = 2-is-accessible
```

In order to prove that all natural numbers are accessible, we use the
following two lemmas.

If m < n + 1 then either m < n or m = n.

```agda
<ₙ-suc-lemma : ∀ {m} n → m <ₙ suc n → (m <ₙ n) ∔ (m ≡ n)
<ₙ-suc-lemma zero <-zero = inr (refl zero)
<ₙ-suc-lemma (suc n) <-zero = inl <-zero
<ₙ-suc-lemma (suc n) (<-suc {m} m<n+1) with <ₙ-suc-lemma n m<n+1
<ₙ-suc-lemma (suc n) (<-suc {_} m<n+1) | inl m<n = inl (<-suc m<n)
<ₙ-suc-lemma (suc n) (<-suc {_} m<n+1) | inr m≡n = inr (ap suc m≡n)
```

With this we can prove that if n is accessible then so is n+1.

```agda
suc-is-accessible : (n : ℕ) → Acc _<ₙ_ n → Acc _<ₙ_ (suc n)
suc-is-accessible n a@(acc ϕ) = acc h
 where
  g : ∀ m → (m <ₙ n) ∔ (m ≡ n) → Acc _<ₙ_ m
  g m (inl l)          = ϕ m l
  g .n (inr (refl .n)) = a

  h : (m : ℕ) → m <ₙ suc n → Acc _<ₙ_ m
  h m l = g m (<ₙ-suc-lemma n l)
```

And from this is follows that every natural number is accessible:

```
<ₙ-WF : WF _<ₙ_
<ₙ-WF 0       = 0-is-accessible
<ₙ-WF (suc n) = suc-is-accessible n (<ₙ-WF n)
```

With this we can prove the following alternative induction principle
for natural numbers, also known as strong induction:

```agda
course-of-values-induction : (P : ℕ → Type)
                           → ((n : ℕ) → ((k : ℕ) → (k <ₙ n) → P k) → P n)
                           → (n : ℕ) → P n
course-of-values-induction P = wf-ind (_<ₙ_) P (<ₙ-WF)
```

## Well-foundedness of the length of a list

As a corollary of the above, we can define a relation on lists
saying that the length of one is less that the length of another:
```agda
module <ₗ-wf (X : Type) where

  _<ₗ_ : List X → List X → Type
  l <ₗ r = length l <ₙ length r
```

Now we can show that this relation is well-founded.  As a result, we
can now write programs and prove to Agda that we only make recursive
calls on smaller lists.  We will see an example of this in the next
section.

```agda
  lift : (l : List X) → Acc _<ₙ_ (length l) → Acc _<ₗ_ l
  lift l (acc ϕ) = acc (λ p p<l → lift p (ϕ (length p) p<l))

  <ₗ-WF : WF _<ₗ_
  <ₗ-WF l = lift l (<ₙ-WF (length l))
```
