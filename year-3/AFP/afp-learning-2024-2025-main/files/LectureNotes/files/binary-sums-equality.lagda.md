#<!--
```agda
{-# OPTIONS --without-K --safe #-}

module binary-sums-equality where

open import prelude
open import isomorphisms
open import subtypes
```
-->

# Equality in `∔` types

First, we define a natural candidate for equality on a `∔` type:

```agda
∔-equality : ∀ {X Y} → X ∔ Y → X ∔ Y → Type
∔-equality (inl x) (inl x') = x ≡ x'
∔-equality (inl x) (inr y) = 𝟘
∔-equality (inr y) (inl x) = 𝟘
∔-equality (inr y) (inr y') = y ≡ y'
```

Now we show that this notion of equality is isomorphic to the usual one:

```agda
∔-equality-encode : ∀ {X Y} (p q : X ∔ Y) → (p ≡ q) → ∔-equality p q
∔-equality-encode (inl x) .(inl x) (refl .(inl x)) = refl x
∔-equality-encode (inr x) .(inr x) (refl .(inr x)) = refl x

∔-equality-decode : ∀ {X Y} (p q : X ∔ Y) → ∔-equality p q → p ≡ q
∔-equality-decode (inl x) (inl x') x≡x' = ap inl x≡x'
∔-equality-decode (inr y) (inr y') y≡y' = ap inr y≡y'

∔-equality-encode-decode : ∀ {X Y} (p q : X ∔ Y) (α : ∔-equality p q)
  → ∔-equality-encode p q (∔-equality-decode p q α) ≡ α
∔-equality-encode-decode (inl x) (inl .x) (refl .x) = refl _
∔-equality-encode-decode (inr y) (inr .y) (refl .y) = refl _

∔-equality-decode-encode : ∀ {X Y} (p q : X ∔ Y) (α : p ≡ q)
  → ∔-equality-decode p q (∔-equality-encode p q α) ≡ α
∔-equality-decode-encode (inl x) .(inl x) (refl .(inl x)) = refl _
∔-equality-decode-encode (inr x) .(inr x) (refl .(inr x)) = refl _

∔-equality-iso : ∀ {X Y} (p q : X ∔ Y) → (p ≡ q) ≅ (∔-equality p q)
∔-equality-iso p q = Isomorphism (∔-equality-encode p q)
  (Inverse (∔-equality-decode p q)
           (∔-equality-decode-encode p q)
           (∔-equality-encode-decode p q)) 
```

As a consequence, we can show that the binary sum of two sets is a set.

```
∔-equality-is-prop : ∀ {X Y} → is-set X → is-set Y
  → (p q : X ∔ Y) → is-prop (∔-equality p q)
∔-equality-is-prop X-is-set Y-is-set (inl x) (inl x') = X-is-set x x'
∔-equality-is-prop X-is-set Y-is-set (inl x) (inr y) = 𝟘-is-prop
∔-equality-is-prop X-is-set Y-is-set (inr y) (inl x) = 𝟘-is-prop
∔-equality-is-prop X-is-set Y-is-set (inr y) (inr y') = Y-is-set y y'

∔-is-set : ∀ {X Y} → is-set X → is-set Y → is-set (X ∔ Y)
∔-is-set X-is-set Y-is-set p q =
  retracts-preserve-prop {X = ∔-equality p q}
    (∔-equality-decode p q , ∔-equality-encode p q , ∔-equality-decode-encode p q)
    (∔-equality-is-prop X-is-set Y-is-set p q) 
```
