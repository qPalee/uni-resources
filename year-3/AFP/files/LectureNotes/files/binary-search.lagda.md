```agda
{-# OPTIONS --without-K --safe #-}

module binary-search where

open import prelude
open import partial-orders
open import decidability
open import natural-numbers-functions hiding (_≥_ ; _≤_)
open import List-functions
open import sorting
open import subtypes

_∈ₗ_ : {X : Type} → X → List X → Type
y ∈ₗ [] = 𝟘
y ∈ₗ (x :: xs) = (y ≡ x) ∔ (y ∈ₗ xs)

record ListSearchingAlgorithm {X : Type} : Type where
  field
    search : X → List X → Bool
    search-finds-members
     : (y : X) (xs : List X) → y ∈ₗ xs → search y xs ≡ true
    search-doesnt-find-nonmembers
     : (y : X) (xs : List X) → search y xs ≡ true → y ∈ₗ xs

  search-doesnt-find-nonmembers'
   : (y : X) (xs : List X) → ¬ (y ∈ₗ xs) → search y xs ≡ false
  search-doesnt-find-nonmembers' y xs ¬y∈xs
   = goal (search y xs) (refl (search y xs))
  -- Goal  : search y xs ≡ false
  -- ¬y∈xs : (y ∈ₗ xs) → 𝟘
   where
    goal : (b : Bool) → b ≡ search y xs → b ≡ false
    goal true  e
     = 𝟘-nondep-elim (¬y∈xs (search-doesnt-find-nonmembers y xs (sym e)))
    goal false e
     = refl false

module _ {X : Type} where

 open ListSearchingAlgorithm {X}

 naive-search : X → List X → Bool
 naive-search y xs = true

 naive-search-finds-members
  : (y : X) (xs : List X) → y ∈ₗ xs → naive-search y xs ≡ true
 naive-search-finds-members y xs y∈xs = refl true

 {- naive-search-doesnt-find-nonmembers
  : (y : X) (xs : List X) → naive-search y xs ≡ true → y ∈ₗ xs
 naive-search-doesnt-find-nonmembers y xs _ = {!!}

 Naive-Search : ListSearchingAlgorithm {X}
 search                        Naive-Search
  = naive-search
 search-finds-members          Naive-Search
  = naive-search-finds-members
 search-doesnt-find-nonmembers Naive-Search
  = {!!} -}

module _ {X : Type} (d : has-decidable-equality X) where

 open ListSearchingAlgorithm {X}

 linear-search : X → List X → Bool

 linear-goal : (y x : X) (xs : List X) → (x ≡ y) ∔ ¬ (x ≡ y) → Bool
 linear-goal y x xs (inl _) = true
 linear-goal y x xs (inr _) = linear-search y xs

 linear-search y [] = false
 linear-search y (x :: xs) = linear-goal y x xs (d x y)

 linear-search-finds-members
     : (y : X) (xs : List X) → y ∈ₗ xs → linear-search y xs ≡ true
 linear-search-finds-members y (x :: xs) y∈xs = goal (d x y)
  where
   goal : (γ : (x ≡ y) ∔ ¬ (x ≡ y)) → linear-goal y x xs γ ≡ true
   goal (inl _  ) = refl true
   goal (inr x≠y)
    = linear-search-finds-members y xs
        (∔-nondep-elim (λ y≡x → 𝟘-nondep-elim (x≠y (sym y≡x))) id y∈xs)

 linear-search-doesnt-find-nonmembers
     : (y : X) (xs : List X) → linear-search y xs ≡ true → y ∈ₗ xs
 linear-search-doesnt-find-nonmembers y (x :: xs) = goal (d x y)
  where
   goal : (γ : is-decidable (x ≡ y))
        → linear-goal y x xs γ ≡ true
        → (y ≡ x) ∔ (y ∈ₗ xs)
   goal (inl x≡y) e = inl (sym x≡y)
   goal (inr x≠y) e = inr (linear-search-doesnt-find-nonmembers y xs e)

 Linear-Search : ListSearchingAlgorithm {X}
 search                        Linear-Search
  = linear-search
 search-finds-members          Linear-Search
  = linear-search-finds-members
 search-doesnt-find-nonmembers Linear-Search
  = linear-search-doesnt-find-nonmembers

module _ {X : Type}
 (ρ : PartialOrder X) (trichotomy : trichotomous ρ)
 (τ : SortingAlgorithm ρ)
 where

 open import BST

 open PartialOrder ρ
 open SortingAlgorithm τ
 open BST.first-approach X ρ trichotomy

 record ListToTreeAlgorithm : Type where
  field
   unflatten : List X → BST
   unflatten-should-keep-members
    : (y : X) (xs : List X) → y ∈ₗ xs → y ∈ₛ unflatten xs
   unflatten-doesnt-introduce-members
    : (y : X) (xs : List X) → y ∈ₛ unflatten xs → y ∈ₗ xs

 module _ (ζ : ListToTreeAlgorithm) where

  open ListToTreeAlgorithm ζ

  binary-search-on-BST : X → BST → Bool
  binary-search-on-BST y t
   = fst (fst (decidability-with-booleans (y ∈ₛ t)) (being-in-is-decidable y t))

  binary-search : X → (xs : List X) → Bool
  binary-search y xs = binary-search-on-BST y (unflatten xs)

  binary-search-on-BST-finds-members
   : (y : X) (t : BST) → y ∈ₛ t → binary-search-on-BST y t ≡ true
  binary-search-on-BST-finds-members y t y∈t
   = fst γ y∈t
   where
    γ : (y ∈ₛ t) ⇔ binary-search-on-BST y t ≡ true
    γ = snd (fst (decidability-with-booleans (y ∈ₛ t)) (being-in-is-decidable y t))

  binary-search-finds-members
   : (y : X) (xs : List X) → y ∈ₗ xs → binary-search y xs ≡ true
  binary-search-finds-members y xs y∈xs
   = binary-search-on-BST-finds-members y
      (unflatten xs) (unflatten-should-keep-members y xs y∈xs)

  binary-search-on-BST-doesnt-find-nonmembers
   : (y : X) (t : BST) → binary-search-on-BST y t ≡ true → y ∈ₛ t
  binary-search-on-BST-doesnt-find-nonmembers y t y∈t
   = snd γ y∈t
   where
    γ : (y ∈ₛ t) ⇔ binary-search-on-BST y t ≡ true
    γ = snd (fst (decidability-with-booleans (y ∈ₛ t)) (being-in-is-decidable y t))  
  
  binary-search-doesnt-find-nonmembers
   : (y : X) (xs : List X) → binary-search y xs ≡ true → y ∈ₗ xs
  binary-search-doesnt-find-nonmembers y xs e
   = unflatten-doesnt-introduce-members y xs
       (binary-search-on-BST-doesnt-find-nonmembers y (unflatten xs) e)

 open ListSearchingAlgorithm {X}

 treeify : List X → BST
 treeify [] = leaf , ⋆
 treeify (x :: xs) = insert x (treeify xs)

 insert-membership-lemma-inverse'
  : (y x : X)
  → (t : BT X)
  → (i : is-bst t)
  → y ∈ₛ (t , i)
  → y ∈ₛ insert x (t , i)
 insert-membership-lemma-inverse' y x (branch z l r) (s , g , il , ir)
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
      = insert-membership-lemma-inverse' y x l il y∈t
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
      = insert-membership-lemma-inverse' y x r ir y∈t

 insert-membership-lemma-inverse
  : (y x : X) (t : BST) → (y ≡ x) ∔ (y ∈ₛ t) → y ∈ₛ insert x t
 insert-membership-lemma-inverse y y t (inl (refl _))
  = insert-membership-property y (fst t) (snd t) 
 insert-membership-lemma-inverse y x (t , i) (inr y∈t)
  = insert-membership-lemma-inverse' y x t i y∈t

 treeify-should-keep-members
  : (y : X) (xs : List X) → y ∈ₗ xs → y ∈ₛ treeify xs
 treeify-should-keep-members y (x :: xs) y∈xs
  = insert-membership-lemma-inverse y x (treeify xs)
     (∔-nondep-elim inl (λ y∈ₗxs → inr (treeify-should-keep-members y xs y∈ₗxs)) y∈xs)
   
 treeify-doesnt-introduce-members
  : (y : X) (xs : List X) → y ∈ₛ treeify xs → y ∈ₗ xs
 treeify-doesnt-introduce-members y (x :: xs) y∈xs
  = ∔-nondep-elim inl (λ y∈ₛxs → inr (treeify-doesnt-introduce-members y xs y∈ₛxs)) γ
  where
   γ : (y ≡ x) ∔ (y ∈ₛ treeify xs)
   γ = membership-insert-property x y (fst (treeify xs)) (snd (treeify xs)) y∈xs

 open ListToTreeAlgorithm

 Treeify : ListToTreeAlgorithm 
 unflatten                          Treeify
  = treeify
 unflatten-should-keep-members      Treeify
  = treeify-should-keep-members
 unflatten-doesnt-introduce-members Treeify
  = treeify-doesnt-introduce-members

 Binary-Search : ListSearchingAlgorithm {X}
 search                        Binary-Search
  = binary-search Treeify
 search-finds-members          Binary-Search
  = binary-search-finds-members Treeify
 search-doesnt-find-nonmembers Binary-Search
  = binary-search-doesnt-find-nonmembers Treeify
```
