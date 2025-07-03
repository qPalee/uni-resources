# Practice Test

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.practice-test where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
open import binary-type
open import function-extensionality
open import decidability
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
 1. You should use your own machine. (You can also use one of the 6 lab lab machines, if you wish, provided you installed Agda in advance.)
 1. The test is open book.
    * You are allowed to use the module material on GitLab. This includes sample solutions.
    * You are allowed to use the Agda manual online, as well as the emacs cheatsheet and the resources we gave you on GitLab.
    * You are allowed to use your own solutions and notes.
 1. What you are **not** allowed.
    *  You are **not** allowed to use your phone (other than for authentication at the beginning of the test), google search, stackoverflow, chat, email etc.
    * Please put your phone on silent mode inside your bag under the table.
    * You are **not** allowed to use any kind of AI.
 1. By signing the attendance sheet, you declare that you are submitting your own work.

## Question 1 - Cancellability of Addition

**Prove** the following cancellation property of addition:

```agda
+-left-cancellable : (a b c : ℕ)
                   → a + b ≡ a + c
                   → b ≡ c
+-left-cancellable = {!!}
```

## Question 2 - Two Definitions of Subtraction

Consider the following two definitions of a subtraction function given
in terms of the `pred` function. In the first we call `pred` on the
result of the inductive call, while in the second we call `pred` on the
input to the recursive call.

```agda
sub : ℕ → ℕ → ℕ
sub zero    m = m
sub (suc n) m = pred (sub n m)

sub' : ℕ → ℕ → ℕ
sub' zero    m = m
sub' (suc n) m = sub' n (pred m)
```

Intuitively, both `sub n m` and `sub' n m` apply the predecessor
function `n` times to `m`.  The point of this question will be to
prove this fact.  We will need some intermediate lemmas.

**Prove** the following lemmas about subtracting from zero.

```agda
sub-from-zero : (a : ℕ) → sub a 0 ≡ 0
sub-from-zero = {!!}

sub'-from-zero : (a : ℕ) → sub' a 0 ≡ 0
sub'-from-zero = {!!}
```

**Prove** the following lemma about subtracting from a successor.

```agda
pred-sub : (a b : ℕ) → pred (sub a (suc b)) ≡ sub a b
pred-sub = {!!}
```

**Prove** that the two definitions of subtraction agree. You may wish to
use the lemmas proven above.

```agda
sub-agree : (a b : ℕ) → sub a b ≡ sub' a b
sub-agree = {!!}
```

## Question 3 - Formalizing Surjectivity

Formulate the definition of surjectivity in agda.

> A function $`f : X → Y`$ is surjective if for every $`y : Y`$, there is some $`x : X`$ such that $`f(x) = y`$.

```agda
surjective : {X Y : Type} → (X → Y) → Type
surjective = {!!}
```

## Question 4 - Decidability of the Constant List Predicate

We define a predicate `is-constant-list` asserting that all the entries
of a list of natural numbers are equal to a fixed number.

```agda
is-constant-list : ℕ → List ℕ → Type
is-constant-list n [] = 𝟙
is-constant-list n (x :: xs) = (x ≡ n) × is-constant-list n xs
```

**Prove** that the `is-constant-list` predicate is decidable.

```agda
is-constant-list-is-decidable : (n : ℕ) (xs : List ℕ)
                              → is-decidable (is-constant-list n xs)
is-constant-list-is-decidable = {!!}
```

## Question 5 - Isomorphism of Binary and Rose Trees

Consider the following two types of unlabelled trees.  The first are
binary trees (i.e. trees where each node has exactly two children),
while the second are trees where each node has a list of children
(so-called Rose trees).

```agda
data Bin : Type where
  lf : Bin
  nd : Bin → Bin → Bin

data Rose : Type where
  br : List Rose → Rose
```

Show that these two types of trees are isomorphic.


```agda
bin-rose-iso : Bin ≅ Rose
bin-rose-iso = record { bijection = f ; bijectivity = f-is-bijection }
 where

  f : Bin → Rose
  f = {!!}

  g : Rose → Bin
  g = {!!}

  gf : g ∘ f ∼ id
  gf = {!!}

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```
