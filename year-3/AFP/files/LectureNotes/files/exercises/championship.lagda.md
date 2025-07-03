```agda
{-# OPTIONS --without-K --auto-inline #-}

open import prelude
open import natural-numbers-functions hiding (max ; min ; is-even ; is-prime)
open import isomorphisms
open import function-extensionality
open import partial-orders
open import BST 
```

Welcome to the Advanced Functional Programming Championship 2025.

Your goal is to work in the following module...

```agda
module exercises.championship 
 (X : Type)
 (ρ : PartialOrder X)
 (trichotomy : trichotomous ρ)
 (fe : FunExt)
 where

 open PartialOrder ρ
 open BST.first-approach X ρ trichotomy
 open BST.second-approach X ρ trichotomy
  renaming
   (BST to BST'
   ; all-smaller to all-smaller'
   ; all-bigger to all-bigger')
```

...in order to **prove** that the two approaches to binary search trees
defined in Todd's Week 8 lectures are *isomorphic*.

The winner will receive a special prize. Good luck!

```agda
 binary-search-iso : BST ≅ BST'
 binary-search-iso = {!!}
```
