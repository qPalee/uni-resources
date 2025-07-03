# Test 1

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.test1-solutions where

open import prelude
open import natural-numbers-functions hiding (max ; min ; is-even ; is-prime)
open import isomorphisms
open import function-extensionality
open import subtypes
open import sums-equality
```
## Test Instructions.

 1. The test is 1hr 50min long.
 1. Make sure you submit on Canvas from time to time. The last submission will be marked.
 1. Submissions close at 12:50 sharp.
 1. Late submissions are strictly not accepted.
 1. Make sure you give Canvas time to process your submission. The submission time is included in the time allocated for the test.
 1. Please check your Canvas submission after you have submitted.
 1. RAP students get extra time as usual (to be set on Canvas) based on the information that the Welfare Team sends us.
 1. You will need to sign attendance in the lab (in addition to the university online attendance).
 1. You need to **bring your student id** and have it on the desk for us to check.
 1. You should use your own machine. (You can also use one of the 6 lab machines, if you wish, provided you installed Agda in advance.)
 1. The test is open book.
    * You are allowed to use the module material on GitLab. This includes sample solutions.
    * You are allowed to use the Agda manual online, as well as the emacs cheatsheet and the resources we gave you on GitLab.
    * You are allowed to use your own solutions and notes.
 1. What you are **not** allowed.
    *  You are **not** allowed to use your phone (other than for authentication at the beginning of the test), google search, stackoverflow, chat, email etc.
    * Please put your phone on silent mode inside your bag under the table.
    * You are **not** allowed to use any kind of AI.
 1. By signing the attendance sheet, you declare that you are submitting your own work.

## Question 1 - Distributivity of Addition over Maximum

Recall the definition of `max` from
[`natural-numbers-functions`](../natural-numbers-functions.lagda.md):

```agda
max : ℕ → ℕ → ℕ
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)
```

**Prove** the following distributivity property of addition over the
maximum function:

```agda
+-distributes-over-max : (a b c : ℕ)
                       → c + (max a b) ≡ max (c + a) (c + b)
+-distributes-over-max a b zero = refl (max a b)
+-distributes-over-max a b (suc c)
 = ap suc (+-distributes-over-max a b c)
```

## Question 2 - Minimum and Maximum of Equal Numbers

Recall the definition of `min` from [`natural-numbers-functions`](../natural-numbers-functions.lagda.md):

```agda
min : ℕ → ℕ → ℕ
min zero n  = zero
min (suc m) zero = zero
min (suc m) (suc n) = suc (min m n)
```

**Prove** that if the minimum and maximum of two numbers is the same,
then both of the numbers must be the same too.

```agda
min-max-eq : (n m : ℕ) → min n m ≡ max n m → n ≡ m
min-max-eq zero zero h = refl zero
min-max-eq (suc n) (suc m) h = ap suc (min-max-eq n m (ap pred h))
```

## Question 3 - Goldbach's Conjecture

Recall the definitions of `is-even` and `is-prime` from
[`natural-numbers-functions`](../natural-numbers-functions.lagda.md):

```agda
is-even : ℕ → Type
is-even x = Σ y ꞉ ℕ , x ≡ 2 * y

is-prime : ℕ → Type
is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) ∔ (x ≡ n))
```

Goldbach's conjecture is one of the most famous unproved statements in
mathematics.

It says that, for every even natural number greater than or equal to 4,
there are two prime numbers which add up to that number.

**State** Goldbach's conjecture as a type in Agda.

```agda
goldbach : Type
goldbach = (n : ℕ) → is-even n → 4 ≤ n
         → Σ (p , q) ꞉ (ℕ × ℕ) , is-prime p × is-prime q × (p + q ≡ n)
```

## Question 4 - Isomorphism of Function Spaces

We have seen before¹ that two functions `A → B` and `A → C` correspond
to a single function `A → B × C`. Similarly, we have seen² that if we
have two functions `B → A` and `C → A` this corresponds to a single
function `B ∔ C → A`.

In the case that `A`, `B` and `C` are all the same type `X` then we
would expect to get a correspondence between functions `X → X × X` and
`X ∔ X → X`.

-----
1. This is `function-to-times-isomorphism` in [this file](../LiveCoding/week4-solutions.lagda.md).
2. This is `function-from-plus-isomorphism` in [this file](../LiveCoding/week4-solutions.lagda.md).

**Prove** this isomorphism for all types `X` assuming function
extensionality.

```agda
function-iso : FunExt → (X : Type) → (X ∔ X → X) ≅ (X → X × X)
function-iso fe X = Isomorphism F (Inverse G section retraction)
  where
   F : (X ∔ X → X) → X → X × X
   F f x = f (inl x) , f (inr x)

   G : (X → X × X) → X ∔ X → X
   G f (inl x) = fst (f x)
   G f (inr x) = snd (f x)

   section : G ∘ F ∼ id
   section f = fe aux
    where
     aux : (G ∘ F) f ∼ f
     aux (inl x) = refl (f (inl x))
     aux (inr x) = refl (f (inr x))

   retraction : F ∘ G ∼ id
   retraction f = fe aux
    where
     aux : (F ∘ G) f ∼ f
     aux x = refl (f x)
```

## Question 5 - Inverses are property

Suppose we have a type `X` with an associative binary function `_·_`
and an element `e` acting as a left and right identity (so
`e · x ≡ x ≡ x · e` for all `x : X`).

We say that an element `a : X` is *invertible* if there exists an
`x : X` such that `x · a ≡ e ≡ a · x`. In this question, we will see
that being invertible is a *property*.

For the purposes of this question we will work in an anonymous module.
That means inside this module we have access to all of the following
types, elements and functions below without having to introduce them
as an argument to each function.

```agda
module _ (X : Type)
         (_·_ : X → X → X)
         (e : X)
         (assoc : (x y z : X) → (x · y) · z ≡ x · (y · z))
         (lneutral : (x : X) → e · x ≡ x)
         (rneutral : (x : X) → x · e ≡ x)
       where
```

**Prove** that if `x` is a left inverse of `a` and `y` is a right
inverse of `a` then `x` and `y` are equal.

```agda
 lemma : (a x y : X)
       → x · a ≡ e
       → a · y ≡ e
       → x ≡ y
 lemma a x y x-is-left-inverse y-is-right-inverse =
  x           ≡⟨ sym (rneutral x) ⟩
  x · e       ≡⟨ ap (x ·_) (sym y-is-right-inverse) ⟩
  x · (a · y) ≡⟨ sym (assoc x a y) ⟩
  (x · a) · y ≡⟨ ap (_· y) x-is-left-inverse ⟩
  e · y       ≡⟨ lneutral y ⟩
  y           ∎
```

**Prove** that if `X` is a set, then being invertible is a property.
You may wish to use the above lemma.

```agda
 invertibility-is-prop : is-set X
                       → (a : X)
                       → is-prop (Σ x ꞉ X , (x · a ≡ e) × (a · x ≡ e))
 invertibility-is-prop
  X-is-set a (x , x-linv , x-rinv) (y , y-linv , y-rinv)
  = to-Σ-≡ (lemma a x y x-linv y-rinv
           , to-Σ-≡ (X-is-set (y · a) e _ y-linv
           , X-is-set (a · y) e _ y-rinv)) 
```
