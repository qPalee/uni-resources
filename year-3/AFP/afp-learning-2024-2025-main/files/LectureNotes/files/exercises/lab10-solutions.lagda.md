```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab10-solutions where
open import prelude
open import List-functions
open import sorting
open import subtypes
open import isomorphisms
open import sums-equality
open import Fin
open import partial-orders
open import binary-search
open import exercises.lab9-solutions
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

 insert-membership-lemma-inverse'-ex
  : (y x : X)
  → (t : BT X)
  → (i : is-bst t)
  → y ∈ₛ (t , i)
  → y ∈ₛ insert x (t , i)
 insert-membership-lemma-inverse'-ex y x (branch z l r) (s , g , il , ir)
  = goal (trichotomy x z) (trichotomy y z)
  where
   goal : (γ : Trichotomy x z) (ζ : Trichotomy y z)
        → ∈ₛ-branch y z l r ζ 
        → y ∈ₛ-bst insert'-branch x z l r γ
   goal (inl x<z) = goal' (trichotomy y z)
    where
     goal' : (χ ζ : Trichotomy y z)
           → ∈ₛ-branch y z l r ζ
           → ∈ₛ-branch y z (insert' x l) r χ
     goal' (inl y<z) (inl y<z') y∈t
      = insert-membership-lemma-inverse'-ex y x l il y∈t
     goal' (inl y<z) (inr y≥z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr y≥z) (inl y<z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr (inl (refl _))) (inr _) _ = ⋆
     goal' (inr (inr y>z)) (inr (inl y≡z)) y∈t
      = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡z) y>z)
     goal' (inr (inr y>z)) (inr (inr y>z')) y∈t
      = y∈t
   goal (inr (inl (refl _))) = goal' (trichotomy y z)
    where
     goal' : (χ ζ : Trichotomy y z)
           → ∈ₛ-branch y z l r ζ
           → ∈ₛ-branch y z l r χ
     goal' (inl y<z) (inl y<z') y∈t
      = y∈t
     goal' (inl y<z) (inr y≥z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr y≥z) (inl y<z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr (inl (refl _))) (inr _) _ = ⋆
     goal' (inr (inr y>z)) (inr (inl y≡z)) y∈t
      = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡z) y>z)
     goal' (inr (inr y>z)) (inr (inr y>z')) y∈t
      = y∈t
   goal (inr (inr x>z)) = goal' (trichotomy y z)
    where
     goal' : (χ ζ : Trichotomy y z)
           → ∈ₛ-branch y z l r ζ
           → ∈ₛ-branch y z l (insert' x r) χ
     goal' (inl y<z) (inl y<z') y∈t
      = y∈t
     goal' (inl y<z) (inr y≥z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr y≥z) (inl y<z)
      = 𝟘-nondep-elim (<-means-not-≥ ρ y<z (≥-from-∔ ρ y≥z))
     goal' (inr (inl (refl _))) (inr _) _ = ⋆
     goal' (inr (inr y>z)) (inr (inl y≡z)) y∈t
      = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡z) y>z)
     goal' (inr (inr y>z)) (inr (inr y>z')) y∈t
      = insert-membership-lemma-inverse'-ex y x r ir y∈t

 insert-membership-lemma-inverse-ex
  : (y x : X) (t : BST) → (y ≡ x) ∔ (y ∈ₛ t) → y ∈ₛ insert x t
 insert-membership-lemma-inverse-ex y y t (inl (refl _))
  = insert-membership-property y (fst t) (snd t) 
 insert-membership-lemma-inverse-ex y x (t , i) (inr y∈t)
  = insert-membership-lemma-inverse'-ex y x t i y∈t
```

# Exercise 4

Complete the record (by adding more fileds) TreeToListAlgorithm, whose instantiations are algorithms that appropriately convert a list into a binary search tree.

Your record must allow you to prove that the two proofs below it can be completed.

Then, complete those two proofs.

```
 record TreeToListAlgorithm : Type where
  field
   flatten' : BST → List X
   flatten-should-keep-members
    : (y : X) (t : BST) → y ∈ₛ t → y ∈ₗ flatten' t
   flatten-doesnt-introduce-members
    : (y : X) (t : BST) → y ∈ₗ flatten' t → y ∈ₛ t 

 full-circle-proof-one
  : (F : ListToTreeAlgorithm ρ trichotomy τ)
    (G : TreeToListAlgorithm)
  → let f = ListToTreeAlgorithm.unflatten F in
    let g = TreeToListAlgorithm.flatten' G in
    (y : X) (xs : List X) → y ∈ₗ xs → y ∈ₗ (g ∘ f) xs
 full-circle-proof-one F G y xs y∈xs
  = flatten-should-keep-members y (unflatten xs)
      (unflatten-should-keep-members y xs y∈xs)
  where
   open ListToTreeAlgorithm F
   open TreeToListAlgorithm G
 
 full-circle-proof-two
  : (F : ListToTreeAlgorithm ρ trichotomy τ)
    (G : TreeToListAlgorithm)
  → let f = ListToTreeAlgorithm.unflatten F in
    let g = TreeToListAlgorithm.flatten' G in
    (y : X) (t : BST) → y ∈ₛ t → y ∈ₛ (f ∘ g) t
 full-circle-proof-two F G y t y∈t
  = unflatten-should-keep-members y (flatten' t)
      (flatten-should-keep-members y t y∈t)
  where
   open ListToTreeAlgorithm F
   open TreeToListAlgorithm G
```

# Exercise 5

Instantiate the record you created in Exercise 3.

```
 membership-preserves-double-append
  : (y x : X) (as bs : List X)
  → (y ∈ₗ as) ∔ (y ≡ x) ∔ (y ∈ₗ bs)
  → y ∈ₗ (as ++ [ x ] ++ bs)
 membership-preserves-double-append y x (a :: as) bs (inl (inl (refl _)))
  = inl (refl y)
 membership-preserves-double-append y x (a :: as) bs (inl (inr y∈as))
  = inr (membership-preserves-double-append y x as bs (inl y∈as))
 membership-preserves-double-append y y []        bs (inr (inl (refl _)))
  = inl (refl y)
 membership-preserves-double-append y y (a :: as) bs (inr (inl (refl _)))
  = inr (membership-preserves-double-append y y as bs (inr (inl (refl y))))
 membership-preserves-double-append y x [] bs        (inr (inr y∈bs))
  = inr y∈bs
 membership-preserves-double-append y x (a :: as) bs (inr (inr y∈bs))
  = inr (membership-preserves-double-append y x as bs (inr (inr y∈bs)))

 flatten-indeed-keeps-members
  : (y : X) (t : BT X) (i : is-bst t)
  → y ∈ₛ (t , i)
  → y ∈ₗ (flatten t)
 flatten-indeed-keeps-members y (branch x l r) (s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x l r γ
        → y ∈ₗ (flatten l ++ [ x ] ++ flatten r)
   goal (inl      y<x)  y∈l
    = membership-preserves-double-append y x (flatten l) (flatten r)
        (inl (flatten-indeed-keeps-members y l il y∈l))
   goal (inr (inl y≡x)) _
    = membership-preserves-double-append y x (flatten l) (flatten r)
        (inr (inl y≡x))
   goal (inr (inr y>x)) y∈r
    = membership-preserves-double-append y x (flatten l) (flatten r)
        (inr (inr (flatten-indeed-keeps-members y r ir y∈r)))

 tail-sorted : (x : X) (xs : List X) → Sorted ρ (x :: xs) → Sorted ρ xs
 tail-sorted x [] (sing-sorted _) = nil-sorted
 tail-sorted x (x' :: xs) (adj-sorted _ _ s) = s

 drop-1-sorted : (x x' : X) (xs : List X)
               → Sorted ρ (x :: x' :: xs)
               → Sorted ρ (x       :: xs)
 drop-1-sorted x x' [] (adj-sorted _ x≤x' s) = sing-sorted x
 drop-1-sorted x x' (x'' :: xs)
   (adj-sorted _ x≤x' (adj-sorted _ x'≤x'' s))
  = adj-sorted _ (transitive x≤x' x'≤x'') s

 sorted-list-find-left
  : (y x : X) (as bs : List X)
  → y < x
  → y ∈ₗ (as ++ [ x ] ++ bs)
  → Sorted ρ (as ++ [ x ] ++ bs)
  → y ∈ₗ as
 sorted-list-find-left y x [] bs y<x        (inl y≡x ) s
  = <-irreflexive' ρ y≡x y<x
 sorted-list-find-left y x [] (b :: bs) y<x (inr y∈bs) (adj-sorted _ x≤b s)
  = sorted-list-find-left y b [] bs (<-≤-trans ρ y<x x≤b) y∈bs s
 sorted-list-find-left y x (a :: as) bs y<x (inl y≡x ) s
  = inl y≡x
 sorted-list-find-left y x (a :: as) bs y<x (inr y∈l ) s
  = inr (sorted-list-find-left y x as bs y<x y∈l
      (tail-sorted a (as ++ (x :: bs)) s))

 sorted-list-find-right
  : (y x : X) (as bs : List X)
  → y > x
  → y ∈ₗ (as ++ [ x ] ++ bs)
  → Sorted ρ (as ++ [ x ] ++ bs)
  → y ∈ₗ bs
 sorted-list-find-right y x [] bs y>x        (inl y≡x ) s
  = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡x) y>x)
 sorted-list-find-right y x [] (b :: bs) y>x (inr y∈bs) (adj-sorted _ x≤b s)
  = y∈bs
 sorted-list-find-right y x (a :: as) bs y>x (inr y∈l ) s
  = sorted-list-find-right y x as bs y>x y∈l
      (tail-sorted a (as ++ (x :: bs)) s)
 sorted-list-find-right y x (a :: []) bs y>x (inl y≡a) (adj-sorted _ a≤x s)
  = 𝟘-nondep-elim (<-irreflexive ρ x (<-≤-trans ρ (transport (x <_) y≡a y>x) a≤x))
 sorted-list-find-right y x (a :: a' :: as) bs y>x (inl y≡x) s
  = sorted-list-find-right y x (a :: as) bs y>x (inl y≡x)
      (drop-1-sorted a a' (as ++ [ x ] ++ bs) s)

 flatten-indeed-doesnt-introduce-members
  : (y : X) (t : BT X) (i : is-bst t)
  → y ∈ₗ (flatten t)
  → y ∈ₛ (t , i)
 flatten-indeed-doesnt-introduce-members y t@(branch x l r) i@(s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → y ∈ₗ (flatten l ++ [ x ] ++ flatten r)
        → ∈ₛ-branch y x l r γ
   goal (inl      y<x)  y∈l
    = flatten-indeed-doesnt-introduce-members y l il
        (sorted-list-find-left y x (flatten l) (flatten r) y<x y∈l
          (flattened-BST-is-sorted X ρ trichotomy t i))
   goal (inr (inl y≡x)) _
    = ⋆
   goal (inr (inr y>x)) y∈r
    = flatten-indeed-doesnt-introduce-members y r ir
        (sorted-list-find-right y x (flatten l) (flatten r) y>x y∈r
          (flattened-BST-is-sorted X ρ trichotomy t i))
    
 tree-to-list : TreeToListAlgorithm
 TreeToListAlgorithm.flatten' tree-to-list
  = flatten ∘ fst
 TreeToListAlgorithm.flatten-should-keep-members tree-to-list
  y (t , i) = flatten-indeed-keeps-members y t i
 TreeToListAlgorithm.flatten-doesnt-introduce-members tree-to-list
  y (t , i) = flatten-indeed-doesnt-introduce-members y t i
```
