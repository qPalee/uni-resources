```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module exercises.lab10 where
open import prelude
open import List-functions
open import sorting
open import subtypes
open import isomorphisms
open import sums-equality
open import Fin
open import partial-orders
open import binary-search
```

# Exercise 1


Let's define a membershipe predicate `_∈_` for lists as follows:

```agda
data _∈_ {X : Type} : X → List X → Type where
  ∈-head : {x : X} {xs : List X} → x ∈ (x :: xs)
  ∈-tail : {x y : X} {xs : List X} → x ∈ xs → x ∈ (y :: xs) 
```

Our goal is to show that the `_∈_` predicate is equivalent to a
position and an equality with the element in that position.  To do this,
we'll need the following lemma about how transport interacts with `ap`:

```agda
transport-ap-lemma : {A B : Type} {C : B → Type}
  → (f : A → B) 
  → {a₀ a₁ : A} (p : a₀ ≡ a₁)
  → (c : C (f a₀))
  → transport C (ap f p) c ≡ transport (λ a → C (f a)) p c 
transport-ap-lemma f (refl _) c = refl c
```

Use this lemma to prove the result:

```agda
∈-is-Pos-and-≡ : {X : Type} (x : X) (xs : List X)
               → x ∈ xs ≅ (Σ p ꞉ Pos xs , x ≡ (xs !! p))
∈-is-Pos-and-≡ x xs = {!!}
```


# Exercise 2

Show that the type of positions in a list `xs` is isomorphic to
`Fin (length xs)`.

```
positions-is-fin-length : {X : Type} (xs : List X)
                        → Pos xs ≅ Fin (length xs)
positions-is-fin-length = {!!}
```

# Exercise 3

Prove the missing lemma from the lecture about ListToTreeAlgorithms.

```
module _ {X : Type}
 (ρ : PartialOrder X) (trichotomy : trichotomous ρ)
 (τ : SortingAlgorithm ρ)
 where

 open import BST

 open PartialOrder ρ
 open SortingAlgorithm τ
 open BST.first-approach X ρ trichotomy
 
 insert-membership-lemma-inverse-ex
  : (y x : X) (t : BST) → (y ≡ x) ∔ (y ∈ₛ t) → y ∈ₛ insert x t
 insert-membership-lemma-inverse-ex = {!!}
```

# Exercise 4

Complete the record (by adding more fileds) TreeToListAlgorithm, whose instantiations are algorithms that appropriately convert a list into a binary search tree.

Your record must allow you to prove that the two proofs below it can be completed.

Then, complete those two proofs.

```
 record TreeToListAlgorithm : Type where
  field
   flatten' : BST → List X

 full-circle-proof-one
  : (F : ListToTreeAlgorithm ρ trichotomy τ)
    (G : TreeToListAlgorithm)
  → let f = ListToTreeAlgorithm.unflatten F in
    let g = TreeToListAlgorithm.flatten' G in
    (y : X) (xs : List X) → y ∈ₗ xs → y ∈ₗ (g ∘ f) xs
 full-circle-proof-one = {!!}
 
 full-circle-proof-two
  : (F : ListToTreeAlgorithm ρ trichotomy τ)
    (G : TreeToListAlgorithm)
  → let f = ListToTreeAlgorithm.unflatten F in
    let g = TreeToListAlgorithm.flatten' G in
    (y : X) (t : BST) → y ∈ₛ t → y ∈ₛ (f ∘ g) t
 full-circle-proof-two = {!!}
```

# Exercise 5

Instantiate the record you created in Exercise 3.

```
 tree-to-list : TreeToListAlgorithm
 tree-to-list = {!!}
```

# Bonus Exercise

Complete the isomorphism in `exercises.championship.lagda.md` if you
haven't already.
