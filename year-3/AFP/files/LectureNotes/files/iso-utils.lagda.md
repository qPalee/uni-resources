<!--
```agda
{-# OPTIONS --without-K --safe #-}

module iso-utils where

open import prelude
open import isomorphisms
```
-->

## Equational Reasoning for Isomorphisms

We need some functionality for dealing with isomorphisms.  First, we
note that isomorphisms can be reasoned with in exactly the same way as
equality.  In a sense which we may explain later, isomorphisms play
the role of equalities between types.

```agda
open _≅_
open is-bijection

id-iso : (A : Type) → A ≅ A
id-iso A = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A → A
  f = id

  g : A → A
  g = id

  gf : g ∘ f ∼ id
  gf a = refl a

  fg : f ∘ g ∼ id
  fg a = refl a

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

≅-sym : {X Y : Type} → X ≅ Y → Y ≅ X
≅-sym (Isomorphism f (Inverse g η ε)) = Isomorphism g (Inverse f ε η)

_∘ᵢ_ : {A B C : Type} → B ≅ C → A ≅ B → A ≅ C
α ∘ᵢ β = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : _ → _
  f = bijection α ∘ bijection β

  g : _ → _
  g = inverse (bijectivity β) ∘ inverse (bijectivity α)

  gf : g ∘ f ∼ id
  gf a = trans (ap (inverse (bijectivity β)) (η (bijectivity α) (bijection β a)))
               (η (bijectivity β) a)

  fg : f ∘ g ∼ id
  fg c = trans (ap (bijection α) (ε (bijectivity β) (inverse (bijectivity α) c)))
               (ε (bijectivity α) c)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Equational reasoning for iso's
_≅⟨_⟩_ : (X : Type) {Y Z : Type} → X ≅ Y → Y ≅ Z → X ≅ Z
X ≅⟨ p ⟩ q = q ∘ᵢ p

_∎ᵢ : (X : Type) → X ≅ X
X ∎ᵢ = id-iso X

infixr  0 _≅⟨_⟩_
infix   1 _∎ᵢ

```

## Additional Isomorphisms relating Binary Sums

The following isomorphisms will be useful and are not difficult.
First, `𝟘` is a left unit for binary sums (it is also a right unit
...)

```agda

∔-unit-left-iso : (X : Type) → X ≅ 𝟘 ∔ X
∔-unit-left-iso X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X → 𝟘 ∔ X
  f x = inr x

  g : 𝟘 ∔ X → X
  g (inr x) = x

  gf : g ∘ f ∼ id
  gf x = refl x

  fg : f ∘ g ∼ id
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

Next, if we are given isomorphisms between summands, this then induces
an isomorphism of their sum:

```agda
∔-pair-iso : {A B C D : Type} → A ≅ B → C ≅ D → (A ∔ C) ≅ (B ∔ D)
∔-pair-iso {A} {B} {C} {D} α β = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ C → B ∔ D
  f (inl a) = inl (bijection α a)
  f (inr c) = inr (bijection β c)

  g : B ∔ D → A ∔ C
  g (inl b) = inl (inverse (bijectivity α) b)
  g (inr d) = inr (inverse (bijectivity β) d)

  gf : g ∘ f ∼ id
  gf (inl a) = ap inl (η (bijectivity α) a)
  gf (inr c) = ap inr (η (bijectivity β) c)

  fg : f ∘ g ∼ id
  fg (inl b) = ap inl (ε (bijectivity α) b)
  fg (inr d) = ap inr (ε (bijectivity β) d)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

Binary sums are associative.

```agda
∔-assoc-iso : (A B C : Type) → A ∔ B ∔ C ≅ (A ∔ B) ∔ C
∔-assoc-iso A B C = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ B ∔ C → (A ∔ B) ∔ C
  f (inl a) = inl (inl a)
  f (inr (inl b)) = inl (inr b)
  f (inr (inr c)) = inr c

  g : (A ∔ B) ∔ C → A ∔ B ∔ C
  g (inl (inl a)) = inl a
  g (inl (inr b)) = inr (inl b)
  g (inr c) = inr (inr c)

  gf : g ∘ f ∼ id
  gf (inl a) = refl (inl a)
  gf (inr (inl b)) = refl (inr (inl b))
  gf (inr (inr c)) = refl (inr (inr c))

  fg : f ∘ g ∼ id
  fg (inl (inl a)) = refl (inl (inl a))
  fg (inl (inr b)) = refl (inl (inr b))
  fg (inr c) = refl (inr c)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

In a triple sum, we can swap the order of the left two summands:


```agda
∔-left-swap-iso : (A B C : Type) → A ∔ B ∔ C ≅ B ∔ A ∔ C
∔-left-swap-iso A B C = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ B ∔ C → B ∔ A ∔ C
  f (inl a) = inr (inl a)
  f (inr (inl b)) = inl b
  f (inr (inr c)) = inr (inr c)

  g : B ∔ A ∔ C → A ∔ B ∔ C
  g (inl b) = inr (inl b)
  g (inr (inl a)) = inl a
  g (inr (inr c)) = inr (inr c)

  gf : g ∘ f ∼ id
  gf (inl a) = refl (inl a)
  gf (inr (inl b)) = refl (inr (inl b))
  gf (inr (inr c)) = refl (inr (inr c))

  fg : f ∘ g ∼ id
  fg (inl b) = refl (inl b)
  fg (inr (inl a)) = refl (inr (inl a))
  fg (inr (inr c)) = refl (inr (inr c))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```
