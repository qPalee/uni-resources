# Week 8 - Partial Orders and Sorting

```agda
{-# OPTIONS --without-K --safe #-}
module exercises.lab8-solutions where
open import prelude
open import partial-orders
open import List-functions
open import Fin
open import sorting
open import subtypes
open import isomorphisms
open import binary-sums-equality
```

## Part 1. Strict Orders

Given a partial order `_≤_`, the corresponding *strict* order `_<_` is
given by defined by `x < y = (x ≤ y) × ¬ (x ≡ y)`.  This definition is
exported by the definition of `PartialOrder` so that it is in scope
below.

```agda
module _ {X : Type} (ρ : PartialOrder X) where
  open PartialOrder ρ
  
  <-irreflexive : (x : X) → ¬ (x < x) 
  <-irreflexive x (_ , ¬x≡x) = ¬x≡x (refl x) 

  <-transitive : (x y z : X) → x < y → y < z → x < z
  <-transitive x y z (x≤y , x≠y) (y≤z , y≠z) =
    transitive x≤y y≤z ,
    λ x≡z → x≠y (antisymmetric (x≤y , transport (_≤_ y) (sym x≡z) y≤z))
```

Recall that a partial order is *total* if any two elements can be
compared.  Show that if the relation `_≤_` is total, then the relation
`_<_` is *connected* in the following sense:

```agda
  total-implies-connected : is-total ρ → (x y : X) → ¬ (x ≡ y) → (x < y) ∔ (y < x)
  total-implies-connected τ x y ¬x≡y =
    ∔-nondep-elim
      (λ x≤y → inl (x≤y , ¬x≡y))
      (λ y≤x → inr (y≤x , λ y≡x → ¬x≡y (sym y≡x)))
      (τ x y)
```

## Part 2. Mapping monotone functions over lists

Let's suppose that we have *two* partially ordered types `X` and `Y`.  We'll
say a function `f : X → Y` is monotone if it preserves the order in the following sense:

```agda
module _ {X Y : Type} (ρX : PartialOrder X) (ρY : PartialOrder Y) where 

  open PartialOrder ρX renaming (_≤_ to _≤[X]_)
  open PartialOrder ρY renaming (_≤_ to _≤[Y]_)
  
  is-monotone : (X → Y) → Type
  is-monotone f = (x₀ x₁ : X) → x₀ ≤[X] x₁ → f x₀ ≤[Y] f x₁ 
```

Show that if a list `xs : List X` is sorted, then mapping a monotone function over
the list results in another sorted list.

```
  map-of-monotone-preserves-sorted : (f : X → Y)
    → is-monotone f 
    → (xs : List X)
    → Sorted ρX xs
    → Sorted ρY (map f xs)
  map-of-monotone-preserves-sorted f is-m [] s = nil-sorted
  map-of-monotone-preserves-sorted f is-m (x :: []) (sing-sorted x) = sing-sorted (f x)
  map-of-monotone-preserves-sorted f is-m (x :: y :: xs) (adj-sorted xs x≤y s) =
    adj-sorted (map f xs) (is-m x y x≤y)
      (map-of-monotone-preserves-sorted f is-m (y :: xs) s)
```

## Part 3. Partial Order on Positions

Contstruct a partial order on the positions of a list.

**Hint**: to prove that the partial order is univalent, prove that the
positions of a list always form a set.  For this, check out the function
`∔-is-set` in [this file](../binary-sums-equality.lagda.md).  You may also
wish to examine the proof that `𝟚` is a set [here](subtypes.lagda.md).

```agda
_≤ₚ_ : {X : Type} {xs : List X} → Pos xs → Pos xs → Type
_≤ₚ_ {xs = x :: xs} (inl ∙) _ = 𝟙
_≤ₚ_ {xs = x :: xs} (inr p) (inl ∙) = 𝟘
_≤ₚ_ {xs = x :: xs} (inr p) (inr q) = p ≤ₚ q

≤ₚ-is-prop : ∀ {X} {xs : List X} (p q : Pos xs) → is-prop (p ≤ₚ q)
≤ₚ-is-prop {xs = x :: xs} (inl ∙) _ = 𝟙-is-prop
≤ₚ-is-prop {xs = x :: xs} (inr p) (inl ∙) = 𝟘-is-prop
≤ₚ-is-prop {xs = x :: xs} (inr p) (inr q) = ≤ₚ-is-prop p q

≤ₚ-reflexive : ∀ {X} {xs : List X} (p : Pos xs) → p ≤ₚ p
≤ₚ-reflexive {xs = x :: xs} (inl ∙) = ⋆
≤ₚ-reflexive {xs = x :: xs} (inr p) = ≤ₚ-reflexive p

≤ₚ-transitive : ∀ {X} {xs : List X} {x y z : Pos xs} →
                x ≤ₚ y → y ≤ₚ z → x ≤ₚ z
≤ₚ-transitive {xs = x :: xs} {inl ∙} {q} {r} p≤q q≤r = ⋆
≤ₚ-transitive {xs = x :: xs} {inr p} {inr q} {inr r} p≤q q≤r =
  ≤ₚ-transitive {xs = xs} p≤q q≤r

≤ₚ-antisymmetric : ∀ {X} {xs : List X} {x y : Pos xs} →
                   (x ≤ₚ y) × (y ≤ₚ x) → x ≡ y
≤ₚ-antisymmetric {xs = x :: xs} {inl ∙} {inl ∙} (p≤q , q≤p) = refl _
≤ₚ-antisymmetric {xs = x :: xs} {inr p} {inr q} (p≤q , q≤p) =
  ap inr (≤ₚ-antisymmetric {xs = xs} (p≤q , q≤p))

𝟙-is-set : is-set 𝟙
𝟙-is-set = retracts-of-sets-are-sets
  ((λ _ → ⋆) , (λ _ → 0) , λ _ → refl _) ℕ-is-set 

Pos-is-set : ∀ {X} → (xs : List X) → is-set (Pos xs)
Pos-is-set (x :: xs) = ∔-is-set 𝟙-is-set (Pos-is-set xs) 

≤ₚ-univalent : ∀ {X} {xs : List X} {x y : Pos xs} (p : x ≡ y) →
               ≤ₚ-antisymmetric
               (≡-nondep-elim (λ x₁ y₁ → (x₁ ≤ₚ y₁) × (y₁ ≤ₚ x₁))
                (λ x₁ → ≤ₚ-reflexive x₁ , ≤ₚ-reflexive x₁) x y p)
               ≡ p
≤ₚ-univalent {xs = xs} p = Pos-is-set xs _ _ _ p

Pos-PartialOrder : {X : Type} (xs : List X) → PartialOrder (Pos xs)
Pos-PartialOrder xs = record
                       { _≤_ = _≤ₚ_ 
                       ; ≤-is-prop = ≤ₚ-is-prop 
                       ; reflexive = ≤ₚ-reflexive
                       ; transitive = λ {x} {y} {z} α β →
                          ≤ₚ-transitive {x = x} {y} {z} α β
                       ; antisymmetric = ≤ₚ-antisymmetric
                       ; univalent = ≤ₚ-univalent
                       }
```

## Part 4. Monotonicity of retrieving elements

Using the partial order constructed above, show that retriving elements from
a sorted list is a monotone map.

```agda
module _ {X : Type} (ρ : PartialOrder X) where
  open PartialOrder ρ

  !!-is-monotone : (xs : List X) (s : Sorted ρ xs)
    → is-monotone (Pos-PartialOrder xs) ρ (λ p → xs !! p)
  !!-is-monotone (x :: []) (sing-sorted x) (inl ∙) (inl ∙) p≤q = reflexive x
  !!-is-monotone (x :: y :: xs) (adj-sorted xs x≤y s) (inl ∙) (inl ∙) p≤q = reflexive x
  !!-is-monotone (x :: y :: xs) (adj-sorted xs x≤y s) (inl ∙) (inr (inl ∙)) p≤q = x≤y
  !!-is-monotone (x :: y :: xs) (adj-sorted xs x≤y s) (inl ∙) (inr (inr q)) p≤q =
    transitive x≤y (!!-is-monotone (y :: xs) s (inl ∙) (inr q) ∙)
  !!-is-monotone (x :: y :: xs) (adj-sorted xs x≤y s) (inr p) (inr q) p≤q =
    !!-is-monotone (y :: xs) s p q p≤q
    
```

