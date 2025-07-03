<!--
```agda
{-# OPTIONS --without-K --safe #-}

module partial-orders where

open import prelude
open import subtypes 
open import natural-numbers-functions renaming (_≤_ to _≤ₙ_; _≥_ to _≥ₙ_)
open import decidability 
```
-->

# Partial Orders

Many algorithms, such as sorting lists, depending on talking about
types whose elements are "ordered" in some way. In Haskell, these are
type which are members of the `Ord` typeclass and support comparison
operators like `(<=) :: a -> a -> Bool`.

In Agda, however, we would like a notion of ordering which allows us
to state and prove properties.  A first step is to lift the ordering
operator to be a `Type`-valued relation on a type: `_≤_ : X → X →
Type`.  Additionally, we would like to impose some axioms which
reflect our intuitive notion of how and ordering should behave.  Hence
we will adapt the notion of a [partially ordered
set](https://en.wikipedia.org/wiki/Partially_ordered_set) which is common
in mathematics.

We will collect together all the data and axioms into a record type.
We begin by saying that a partial order is a *property valued
relation* on a type.

```agda
record PartialOrder (X : Type) : Type₁ where
  field
    _≤_ : X → X → Type
    ≤-is-prop : (x y : X) → is-prop (x ≤ y)
```

Already we see a small difference with the usual mathematical notion:
because our relation is type valued, witnesses for the relation will
not necessarily be unique unless we add that statement explicity.
This is in contrast to standard usage in mathematics, where relations
are usual understood as *subsets*, and hence are single-valued by
assumption.

Next we add some basic axioms: reflexivity, transitivity and
antisymmetry.

```agda
    reflexive : (x : X) → x ≤ x
    transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
    antisymmetric : {x y : X} → (x ≤ y) × (y ≤ x) → x ≡ y 
```

Finally, one more subtlety arises in Agda as compared with classical
mathematics.  We would like to be slightly more precise about the
interaction of `_≤_` and the equality type on our type `X`.  The
`antisymmetric` axiom is a first step.  It converts a pair of inequalities
into an equality.  In fact, we can go the opposite direction as well simply
by using `≡`-elimination:

```agda 
  inverse-antisymmetric : {x y : X} → x ≡ y → (x ≤ y) × (y ≤ x)
  inverse-antisymmetric {x} {y} = ≡-nondep-elim (λ x y → (x ≤ y) × (y ≤ x))
    (λ x → (reflexive x) , (reflexive x)) x y 
```

So we now have that the two types `(x ≤ y) × (y ≤ x)` and `x ≡ y` are
*logically equivalent* in that we have constructed maps in both
directions.  Note that the first type is a property by our assumption
on `_≤_` and the closure of properties under `_×_`.  However, the
equality type need *not* be a property.  If we were to strengthen our
logical equivalence to an *isomorphism*, then it would automatically
follow that `_≡_` was a property since properties are closed under
isomorphism.  The only thing missing is to state the round-trip
equations for the functions we have already considered.  It turns out
that one of them is automatic (why?) so we add the other:

```agda 
  field
    univalent : {x y : X} → (p : x ≡ y) → antisymmetric (inverse-antisymmetric p) ≡ p 
```
We can now show that any partially ordered *type* is in fact a *set* in the sense we have defined:

```agda
  ≡-is-retract-of-≤ : {x y : X} → retract x ≡ y of ((x ≤ y) × (y ≤ x))
  ≡-is-retract-of-≤ {x} {y} = antisymmetric  , (inverse-antisymmetric , univalent) 

  carrier-is-set : is-set X
  carrier-is-set x y =
    retracts-preserve-prop
      ≡-is-retract-of-≤
      (×-is-prop (≤-is-prop x y) (≤-is-prop y x)) 
```

We add a couple of auxillary definition, which can be useful when using a partial order.

```agda
  _≥_ : X → X → Type 
  x ≥ y = y ≤ x

  _<_ : X → X → Type
  x < y = (x ≤ y) × ¬ (x ≡ y)

  _>_ : X → X → Type
  x > y = y < x 
```
This now completes our definition of partial orders.

# The partial order on `ℕ`

It is not hard to show that the usual ordering on the natural numbers,
defined [here](natural-numbers-functions.lagda.md) is and example
of a partial order.

```agda
≤ₙ-is-prop : {m n : ℕ} → is-prop (m ≤ₙ n)
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
                  ; ≤-is-prop = λ m n → ≤ₙ-is-prop {m} {n}
                  ; reflexive = ≤ₙ-reflexive
                  ; transitive = ≤ₙ-transitive
                  ; antisymmetric = ≤ₙ-antisymmetric
                  ; univalent = ≤ₙ-univalent 
                  } 
```

# Total Orders

In practice, when writing programs, we ofter need to know slightly
more than just that a type is ordered: we need a way to ask, given any
two elements `x` and `y` of a partially ordered type `X`, whether `x ≤
y` or `y ≤ x`.  Orders for which one of these two conditions always holds
are called *total orders*.

```agda

module _ {X : Type} (ρ : PartialOrder X) where

  open PartialOrder ρ 

  is-total : Type
  is-total = (x y : X) → (x ≤ y) ∔ (y ≤ x)
```

```agda
  trichotomous : Type
  trichotomous = (x y : X) → (x < y) ∔ (x ≡ y) ∔ (x > y)

  decidability-implies-trichotomy : has-decidable-equality X → is-total → trichotomous
  decidability-implies-trichotomy X-is-dec ≤-total x y =
    ∔-nondep-elim
      (λ x≡y → inr (inl x≡y))
      (λ ¬x≡y → ∔-nondep-elim
                  (λ x≤y → inl (x≤y , ¬x≡y))
                  (λ y≤x → inr (inr (y≤x , λ y≡x → ¬x≡y (sym y≡x))))
                  (≤-total x y))
      (X-is-dec x y) 

  trichotomous-implies-decidable-equality : trichotomous → has-decidable-equality X
  trichotomous-implies-decidable-equality τ x y =
    ∔-nondep-elim
      (λ (_ , ¬x≡y) → inr ¬x≡y)
      (∔-nondep-elim inl (λ (_ , ¬y≡x) → inr (λ x≡y → ¬y≡x (sym x≡y))))
      (τ x y) 

  trichotomous-implies-total : trichotomous → is-total
  trichotomous-implies-total τ x y = 
    ∔-nondep-elim
      (λ (x≤y , _) → inl x≤y)
      (∔-nondep-elim
        (λ x≡y → inl (fst (inverse-antisymmetric x≡y)))
        (λ (y≤x , _) → inr y≤x)) 
      (τ x y)

  trichotomous-implies-<-decidable : trichotomous → (x y : X) → is-decidable (x < y)
  trichotomous-implies-<-decidable τ x y =
    ∔-nondep-elim
      inl
      (∔-nondep-elim
        (λ x≡y → inr (λ (_ , ¬x≡y) → ¬x≡y x≡y))
        λ (y≤x , ¬y≡x) → inr (λ (x≤y , ¬x≡y) → ¬x≡y (antisymmetric (x≤y , y≤x))))
      (τ x y) 

```

Let's show that the partial order of `ℕ` is total:

```agda
≤ₙ-is-total : is-total ℕ-PartialOrder
≤ₙ-is-total zero n = inl 0-smallest
≤ₙ-is-total (suc m) zero = inr 0-smallest
≤ₙ-is-total (suc m) (suc n) =
  ∔-nondep-elim
    (λ m≤n → inl (suc-preserves-≤ m≤n))
    (λ n≤m → inr (suc-preserves-≤ n≤m))
    (≤ₙ-is-total m n)
```

## A Strict Total Order from a Partial Order

```agda
module _ {X : Type} (ρ : PartialOrder X) where
  open PartialOrder ρ
  
  <-irreflexive : (x : X) → ¬ (x < x) 
  <-irreflexive x (_ , ¬x≡x) = ¬x≡x (refl x) 
  
  <-transitive : (x y z : X) → x < y → y < z → x < z
  <-transitive x y z (x≤y , x≠y) (y≤z , y≠z) =
    transitive x≤y y≤z ,
    λ x≡z → x≠y (antisymmetric (x≤y , transport (_≤_ y) (sym x≡z) y≤z))

  total-implies-connected : is-total ρ → (x y : X) → ¬ (x ≡ y) → (x < y) ∔ (y < x)
  total-implies-connected τ x y ¬x≡y =
    ∔-nondep-elim
      (λ x≤y → inl (x≤y , ¬x≡y))
      (λ y≤x → inr (y≤x , λ y≡x → ¬x≡y (sym y≡x)))
      (τ x y)

  <-irreflexive' : {x y : X} → x ≡ y → ¬ (x < y)
  <-irreflexive' (refl x) = <-irreflexive x

  <-antisymmetric : (x y : X) → x < y → ¬ (y < x)
  <-antisymmetric x y x<y y<x = <-irreflexive x (<-transitive x y x x<y y<x)

  ≥-from-∔ : {x y : X} → (x ≡ y) ∔ (x > y) → x ≥ y
  ≥-from-∔ (inl (refl _)) = reflexive _
  ≥-from-∔ (inr x<y) = fst x<y

  <-means-not-≥ : {x y : X} → x < y → ¬ (x ≥ y)
  <-means-not-≥ (x≤y , x≠y) y≥x
   = 𝟘-nondep-elim (x≠y (antisymmetric (x≤y , y≥x)))

  <-≤-trans : {x y z : X} → x < y → y ≤ z → x < z
  <-≤-trans {x} {y} {z} (x≤y , x≠y) y≤z = transitive x≤y y≤z , x≠z
   where
    x≠z : ¬ (x ≡ z)
    x≠z (refl _) = x≠y (antisymmetric (x≤y , y≤z))

  ≤-<-trans : {x y z : X} → x ≤ y → y < z → x < z
  ≤-<-trans {x} {y} {z} x≤y (y≤z , y≠z) = transitive x≤y y≤z , x≠z
   where
    x≠z : ¬ (x ≡ z)
    x≠z (refl _) = y≠z (antisymmetric (y≤z , x≤y))

```
