# Week 6 - Questions

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module LiveCoding.week6-wednesday where

open import prelude
```

In this module, the specific content (e.g. lists, isomorphisms, monads)
often isn't the tricky part -- it's the skills!

Which skills did we test in the practice test?
 1.
 2.
 3.
 4.
 5.

Let's start with your questions!

```agda

```

And if there's not enough questions, let's try this example again:

```agda
[_] : {A : Type} → A → List A
[_] = {!!}

_++_ : {A : Type} → List A → List A → List A
_++_ = {!!}

reverse : {A : Type} → List A → List A
reverse = {!!}

rev-append : {A : Type} → List A → List A → List A
rev-append = {!!}

rev : {A : Type} → List A → List A
rev xs = {!!}

rev-correct : {A : Type} (xs : List A) → rev xs ≡ reverse xs
rev-correct = {!!}
```
