<!--
```agda
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week7 where
open import prelude
open import subtypes
open import decidability
open import natural-numbers-functions renaming (_≤_ to _≤ₙ_)
open import isomorphisms
open import iso-utils
```
-->

# Parial Orders

In haskell, to sort a list of type `a` we need `_≤_ :: a → a → Bool` 

Step 1 - we'll replace `Bool` with `Type` 

```agda
record PartialOrder (X : Type) : Type₁ where
  field
    _≤_ : X → X → Type
    ≤-is-prop : {x y : X} → is-prop (x ≤ y)

    reflexive : (x : X) → x ≤ x
    transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
    antisymmetry : {x y : X} → (x ≤ y) × (y ≤ x) → x ≡ y 

  inverse-antisymmetry : {x y : X} → x ≡ y → (x ≤ y) × (y ≤ x)
  inverse-antisymmetry {x} {y} = ≡-nondep-elim (λ x y → (x ≤ y) × (y ≤ x))
    (λ x → (reflexive x) , (reflexive x)) x y 

  field
    univalent : {x y : X} → (p : x ≡ y) → antisymmetry (inverse-antisymmetry p) ≡ p 

  ≡-is-retract-of-≤ : {x y : X} → retract x ≡ y of ((x ≤ y) × (y ≤ x))
  ≡-is-retract-of-≤ {x} {y} = antisymmetry  , (inverse-antisymmetry , univalent) 

  carrier-is-set : is-set X
  carrier-is-set x y = retracts-preserve-prop ≡-is-retract-of-≤ (×-is-prop ≤-is-prop ≤-is-prop) 

is-total : {X : Type} → PartialOrder X → Type
is-total {X} ρ = (x y : X) → PartialOrder._≤_ ρ x y ∔ PartialOrder._≤_ ρ y x 


```

```agda

≤ₙ-is-prop : ∀ {x} {y} → is-prop (x ≤ₙ y)
≤ₙ-is-prop 0-smallest 0-smallest = refl _
≤ₙ-is-prop (suc-preserves-≤ x≤y) (suc-preserves-≤ x≤y') =
  ap suc-preserves-≤ (≤ₙ-is-prop x≤y x≤y')

≤ₙ-reflexive : ∀ x → x ≤ₙ x
≤ₙ-reflexive zero = 0-smallest
≤ₙ-reflexive (suc n) = suc-preserves-≤ (≤ₙ-reflexive n)

≤ₙ-transitive : ∀ {x} {y} {z} → x ≤ₙ y → y ≤ₙ z → x ≤ₙ z
≤ₙ-transitive 0-smallest y≤z = 0-smallest
≤ₙ-transitive (suc-preserves-≤ x≤y) (suc-preserves-≤ y≤z) =
  suc-preserves-≤ (≤ₙ-transitive x≤y y≤z)

≤ₙ-antisymmetric : ∀ {x} {y} → (x ≤ₙ y) × (y ≤ₙ x) → x ≡ y
≤ₙ-antisymmetric (0-smallest , 0-smallest) = refl _
≤ₙ-antisymmetric (suc-preserves-≤ x≤y , suc-preserves-≤ y≤x) =
  ap suc (≤ₙ-antisymmetric (x≤y , y≤x))

≤ₙ-univalent : ∀ {x} {y} (p : x ≡ y) →
               ≤ₙ-antisymmetric
               (≡-nondep-elim (λ x₁ y₁ → (x₁ ≤ₙ y₁) × (y₁ ≤ₙ x₁))
                (λ x₁ → ≤ₙ-reflexive x₁ , ≤ₙ-reflexive x₁) x y p)
               ≡ p
≤ₙ-univalent p = ℕ-is-set _ _ _ p

ℕ-PartialOrder : PartialOrder ℕ
ℕ-PartialOrder = record
                  { _≤_ = _≤ₙ_
                  ; ≤-is-prop = ≤ₙ-is-prop
                  ; reflexive = ≤ₙ-reflexive
                  ; transitive = ≤ₙ-transitive
                  ; antisymmetry = ≤ₙ-antisymmetric
                  ; univalent = ≤ₙ-univalent 
                  } 

```

# Sorting

```agda
module _ {X : Type} (ρ : PartialOrder X) where

  open PartialOrder ρ 

  data Sorted : List X → Type where
    nil-sorted : Sorted []
    sing-sorted : (x : X) → Sorted (x :: [])
    adj-sorted : {x y : X} (xs : List X) 
      → x ≤ y
      → Sorted (y :: xs) 
      → Sorted (x :: y :: xs)

ex₀ : Sorted ℕ-PartialOrder (1 :: 2 :: 3 :: [])
ex₀ = adj-sorted (3 :: []) (suc-preserves-≤ 0-smallest)
       (adj-sorted [] (suc-preserves-≤ (suc-preserves-≤ 0-smallest))
        (sing-sorted 3)) 

```


# Sorting Algorithms

```agda

SortingAlgorithm-naive : {X : Type} (ρ : PartialOrder X) → Type
SortingAlgorithm-naive {X} ρ =
  Σ σ ꞉ (List X → List X) ,
  ((xs : List X) → Sorted ρ (σ xs)) 

TrivialSort : {X : Type} (ρ : PartialOrder X) → SortingAlgorithm-naive ρ
TrivialSort p =  (λ xs → []) , λ xs → nil-sorted

Pos : {X : Type} → List X → Type
Pos [] = 𝟘
Pos (x :: xs) = 𝟙 ∔ Pos xs

_!!_ : {X : Type} (xs : List X) → Pos xs → X
(x :: xs) !! inl ∙ = x
(x :: xs) !! inr p = xs !! p

record _is-permutation-of_ {X : Type} (xs ys : List X) : Type where
  field
    pos-iso : Pos xs ≅ Pos ys
    same-el : (p : Pos xs) → xs !! p ≡ ys !! _≅_.bijection pos-iso p 

SortingAlgorithm : {X : Type} (ρ : PartialOrder X) → Type
SortingAlgorithm {X} ρ =
  Σ σ ꞉ (List X → List X) ,
  Σ srtd ꞉ ((xs : List X) → Sorted ρ (σ xs)) ,
  ((xs : List X) → (σ xs) is-permutation-of xs ) 



```

# Insertion Sort

**Note** The function here are detailed and explained in [this file](../insertion-sort.lagda.md).

```agda

module _ {X : Type} (ρ : PartialOrder X) (τ : is-total ρ) where

  open PartialOrder ρ
  open _≅_ 

  insert : X → List X → List X
  perform-insertion : (x y : X) → List X → (x ≤ y) ∔ (y ≤ x)  → List X
  
  insert x [] = x :: []
  insert x (y :: xs) = perform-insertion x y xs (τ x y)

  perform-insertion x y xs (inl x≤y) = x :: y :: xs
  perform-insertion x y xs (inr y≤x) = y :: insert x xs

  insert-all : List X → List X → List X
  insert-all [] ys = ys
  insert-all (x :: xs) ys = insert x (insert-all xs ys)

  insertion-sort : List X → List X
  insertion-sort xs = insert-all xs []

  insertion-lemma : (x : X) (xs : List X) → Sorted ρ xs → Sorted ρ (insert x xs)
  
  perform-insertion-lemma : (x y : X) (xs : List X) (α : (x ≤ y) ∔ (y ≤ x))
    → Sorted ρ (y :: xs)
    → Sorted ρ (perform-insertion x y xs α)

  extension-lemma : (x y : X) (xs : List X) → y ≤ x
    → Sorted ρ (y :: xs)
    → Sorted ρ (y :: insert x xs)
  
  double-lemma : (x y z : X) (xs : List X) → y ≤ x
    → (t : (x ≤ z) ∔ (z ≤ x))
    → Sorted ρ (y :: z :: xs)
    → Sorted ρ (y :: perform-insertion x z xs t)

  insertion-lemma x [] s = sing-sorted x
  insertion-lemma x (y :: xs) s = perform-insertion-lemma x y xs (τ x y) s

  perform-insertion-lemma x y xs (inl x≤y) s = adj-sorted xs x≤y s
  perform-insertion-lemma x y xs (inr y≤x) s = extension-lemma x y xs y≤x s

  extension-lemma x y [] y≤x s = adj-sorted [] y≤x (sing-sorted x)
  extension-lemma x y (z :: xs) y≤x s = double-lemma x y z xs y≤x (τ x z) s

  double-lemma x y z xs y≤x (inl x≤z) (adj-sorted xs y≤z s) = adj-sorted (z :: xs) y≤x (adj-sorted xs x≤z s)
  double-lemma x y z xs y≤x (inr z≤x) (adj-sorted xs y≤z s) = adj-sorted (insert x xs) y≤z (extension-lemma x z xs z≤x s)

  insertion-sort-is-sorted : (xs : List X) → Sorted ρ (insertion-sort xs)
  insertion-sort-is-sorted [] = nil-sorted
  insertion-sort-is-sorted (x :: xs) =
    insertion-lemma x (insertion-sort xs) (insertion-sort-is-sorted xs) 

  -- Now produce the permutation
  
  insert-pos-iso : (x : X) (xs : List X)
    → Pos (insert x xs) ≅ 𝟙 ∔ Pos xs

  perform-insertion-pos-iso : (x y : X) (xs : List X) (t : (x ≤ y) ∔ (y ≤ x))
    → Pos (perform-insertion x y xs t) ≅ 𝟙 ∔ 𝟙 ∔ Pos xs

  insert-pos-iso x [] = id-iso (𝟙 ∔ 𝟘) 
  insert-pos-iso x (y :: xs) = perform-insertion-pos-iso x y xs (τ x y)

  perform-insertion-pos-iso x y xs (inl x≤y) = id-iso (𝟙 ∔ 𝟙 ∔ Pos xs)
  perform-insertion-pos-iso x y xs (inr y≤x) = 𝟙 ∔ Pos (insert x xs) ≅⟨ ∔-pair-iso (id-iso 𝟙) (insert-pos-iso x xs) ⟩
                                               𝟙 ∔ 𝟙 ∔ Pos xs        ≅⟨ ∔-left-swap-iso 𝟙 𝟙 (Pos xs) ⟩ 
                                               𝟙 ∔ 𝟙 ∔ Pos xs ∎ᵢ 


  insertion-sort-pos-iso : (xs : List X) → Pos (insertion-sort xs) ≅ Pos xs 
  insertion-sort-pos-iso [] = id-iso 𝟘
  insertion-sort-pos-iso (x :: xs) = Pos (insert x (insertion-sort xs)) ≅⟨ insert-pos-iso x (insertion-sort xs) ⟩
                                     𝟙 ∔ Pos (insertion-sort xs)        ≅⟨ ∔-pair-iso (id-iso 𝟙) (insertion-sort-pos-iso xs) ⟩ 
                                     𝟙 ∔ Pos xs ∎ᵢ

  
  pos-swap-lemma : (x y : X) (xs : List X)
    → (p : Pos (y :: xs))
    → (x :: y :: xs) !! (inr p) ≡
      (y :: x :: xs) !! (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) (inr p))
  pos-swap-lemma x y xs (inl ⋆) = refl y
  pos-swap-lemma x y xs (inr p) = refl (xs !! p)

  insert-el-eq : (x : X) (xs : List X)
    → (p : Pos (insert x xs))
    → (insert x xs) !! p ≡ (x :: xs) !! (bijection (insert-pos-iso x xs) p)

  perform-insertion-el-eq : (x y : X) (xs : List X) (t : (x ≤ y) ∔ (y ≤ x))
    → (p : Pos (perform-insertion x y xs t))
    → (perform-insertion x y xs t !! p) ≡
      ((x :: y :: xs) !! bijection (perform-insertion-pos-iso x y xs t) p)
      
  insert-el-eq x [] (inl ∙) = refl x
  insert-el-eq x (y :: xs) p = perform-insertion-el-eq x y xs (τ x y) p

  perform-insertion-el-eq x y xs (inl x≤y) p = refl _
  perform-insertion-el-eq x y xs (inr y≤x) (inl ∙) = refl _
  perform-insertion-el-eq x y xs (inr y≤x) (inr p) = 
    insert x xs !! p
      ≡⟨ insert-el-eq x xs p ⟩
    ((x :: xs) !! bijection (insert-pos-iso x xs) p)
      ≡⟨ pos-swap-lemma y x xs (bijection (insert-pos-iso x xs) p) ⟩ 
    (((x :: y :: xs) !! bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs))
       (inr (bijection (insert-pos-iso x xs) p)))) ∎


  inhab-ext-lemma : (x : X) (xs ys : List X) 
    → (α : Pos xs ≅ Pos ys)
    → (e : (p : Pos xs) → xs !! p ≡ ys !! (bijection α p))
    → (p : Pos (x :: xs))
    → (x :: xs) !! p ≡ (x :: ys) !! (bijection (∔-pair-iso (id-iso 𝟙) α) p)
  inhab-ext-lemma x xs ys α e (inl ⋆) = refl x
  inhab-ext-lemma x xs ys α e (inr p) = e p


  insertion-sort-el-eq : (xs : List X) (p : Pos (insertion-sort xs)) →
    (insertion-sort xs !! p) ≡
    (xs !! bijection (insertion-sort-pos-iso xs) p)
  insertion-sort-el-eq (x :: xs) p = 
    insert x (insertion-sort xs) !! p

      ≡⟨ insert-el-eq x (insertion-sort xs) p ⟩
      
    (x :: insertion-sort xs) !! (bijection (insert-pos-iso x (insertion-sort xs)) p)

      ≡⟨ inhab-ext-lemma x (insertion-sort xs) xs (insertion-sort-pos-iso xs)
          (insertion-sort-el-eq xs)
          (bijection (insert-pos-iso x (insertion-sort xs)) p)  ⟩
    
    (x :: xs) !! bijection (∔-pair-iso (id-iso 𝟙) (insertion-sort-pos-iso xs))
                  (bijection (insert-pos-iso x (insertion-sort xs)) p)

       ≡⟨ refl _ ⟩
                  
    (x :: xs) !! bijection (insertion-sort-pos-iso (x :: xs)) p ∎ 

  insertion-permutation : (xs : List X) → (insertion-sort xs) is-permutation-of xs 
  insertion-permutation xs = record { pos-iso = insertion-sort-pos-iso xs
                                    ; same-el = insertion-sort-el-eq xs 
                                    } 


```
