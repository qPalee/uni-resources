<!--
```agda
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week5-subtypes where
open import prelude
open import natural-numbers-functions
```
-->

# Subtypes

Very often it is useful to consider a subtype of a type. We have seen some examples already, such as the subtype of the natural consisting of the even numbers, the subtype of lists of a given length, the subtype of binary trees consisting of the search trees.

In such a situation it is important to discuss when two elements of a subtype are equal, and this turns out to be a little bit subtle. We need a few new concepts to discuss this:
 1. The function `transport` defined in the file [identity-type](identity-type.lagda.md)
 1. The functions `to-Σ-≡` and `from-Σ-≡` defined in the module [sums-equality](sums.equality.lagda.md)
 1. A function `has-at-most-one-element` defined here.

## Discussion

Consider the functions `is-even` and `is-odd` defined by the module [natural-numbers-functions](natural-numbers-functions.lagda.md).
In some sense the type `is-even x` is **property** of the number `n`, rather than **data**. This is because `is-even x` is defined to be the type `Σ y ꞉ ℕ , x ≡ 2 * y`, and whereas an element of this `Σ`-type does provide data, there is **at most one** `y` with `x ≡ 2 * y`. So when `y` exists, it is unique. We will regard types that have at most one element as expressing *properties*, with all types, in general, expressing *data*. Of course, types that express property, in particular, express data. For example, the property of being even, expressed as the above type, carries a number. But this number is unique when it exists.

On the other hand, consider type `composite n` defined as follows:
```agda
composite : ℕ → Type
composite x = Σ y ꞉ ℕ , Σ z ꞉ ℕ , (y ≥ 2) × (z ≥ 2) × (x ≡ y * z)
```
Now, e.g. the number 30 is composite in several ways.
```
30-composite₀ : composite 30
30-composite₀ = 3 , 10 ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                refl 30

30-composite₁ : composite 30
30-composite₁ = 10 , 3 ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                refl 30

30-composite₂ : composite 30
30-composite₂ = 5 , 6 ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                refl 30

30-composite₃ : composite 30
30-composite₃ = 15 , 2 ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) , refl 30

30-composite₄ : composite 30
30-composite₄ = 2 , 15 ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                suc-preserves-≤ (suc-preserves-≤ 0-smallest) ,
                refl 30
```
So the type `composite 30` collects *all* the ways in which 30 can be composite, and so, in some sense, its elements are *data* rather than mere property.

We say that a type expresses property, rather than data, if it has at
most one element, that is, any two of its elements are equal.
```agda
is-prop : Type → Type
is-prop X = (x y : X) → x ≡ y
```

Definition. A subtype of a type X is a type of the form

  Σ x ꞉ X , A x

where A : X → Type and A x is property for every x : X.

Example. Σ ys : List Y , length ys ≡ n
Here X = List Y, and A ys = (length ys ≡ n).

Counter-example. Σ x : ℕ , composite x.

Here are some examples.

Falsity as expressed by emptiness is property.
```
𝟘-is-prop : is-prop 𝟘
𝟘-is-prop = {!!}
```
Truth as expressed by the unit type is property.
```
𝟙-is-prop : is-prop 𝟙
𝟙-is-prop = {!!}
```
Now the following is harder to prove.
```
being-even-is-prop : (n : ℕ) → is-prop (is-even n)
being-even-is-prop = {!!}
```
One of the main purposes of this file is to explain how we can prove things such as the above.

We also have, in light of the above example, that being a composite number is not property.
```agda
being-composite-is-not-prop-in-general : Σ n ꞉ ℕ , ¬ is-prop (composite n)
being-composite-is-not-prop-in-general = {!!}
```
This is easier to prove than the above. You can take e.g. `n` to be 30, assume that would be property, and get a contradiction (that is, an element of the empty type `𝟘`).

## When equality is property

It is not the case that equality is always property, but it is for most types we are interested in, although we have to prove this. Here we prove it for the natural numbers.

```
_≣_ : ℕ → ℕ → Type
0     ≣ 0     = 𝟙
0     ≣ suc y = 𝟘
suc x ≣ 0     = 𝟘
suc x ≣ suc y = x ≣ y

open import isomorphisms
open import natural-numbers-functions

ℕ-≡-iso : (x y : ℕ) → (x ≡ y) ≅ (x ≣ y)
ℕ-≡-iso x y = Isomorphism (f x y) (Inverse (g x y) (gf x y) (fg x y))
 where
  f : (x y : ℕ) → (x ≡ y) → (x ≣ y)
  f 0       0       (refl 0) = ⋆
  f (suc x) (suc y) p        = f x y (suc-is-injective p)

  g : (x y : ℕ) → (x ≣ y) → (x ≡ y)
  g 0       0       ⋆ = refl 0
  g (suc x) (suc y) p = ap suc (g x y p)

  gf : (x y : ℕ) → g x y ∘ f x y ∼ id
  gf 0       0       (refl 0) = refl (refl 0)
  gf (suc x) (suc y) (refl .(suc x)) = goal
   where
    IH : g x x (f x x (refl x)) ≡ refl x
    IH = gf x y (refl x)

    goal : ap suc (g x x (f x x (refl x))) ≡ refl (suc x)
    goal = ap (ap suc) IH

  fg : (x y : ℕ) → f x y ∘ g x y ∼ id
  fg 0       0       ⋆ = refl ⋆
  fg (suc x) (suc y) p = goal
   where
    IH : f x y (g x y p) ≡ p
    IH = fg x y p

    h : (m n : ℕ) (e : m ≡ n) → ap pred (ap suc e) ≡ e
    h m m (refl m) = refl (refl m)

    goal = f x y (ap pred (ap suc (g x y p))) ≡⟨ ap (f x y) (h x y (g x y p)) ⟩
           f x y (g x y p)                    ≡⟨ IH ⟩
           p                                  ∎
```

## Equality in Σ-types

This is developed in the following file (click at the name to read it, and then come back to this file.
```
open import sums-equality
```
Σ x : X , A x

X = 𝟚
A 𝟎 = Bool
A 𝟏 = ℕ

## Equality in subtypes

## The `Vector X n ≃ (Σ xs ꞉ List A , length xs ≡ n)` example

## An alternative, equivalent notion of subtype

For example, the type `𝟚`, together with the embedding,
```
open import binary-type

𝟚-to-ℕ : 𝟚 → ℕ
𝟚-to-ℕ 𝟎 = 0
𝟚-to-ℕ 𝟏 = 1
```
can be considered as a subtype of `ℕ`. To see this, notice that we have an isomorphism
```
open import isomorphisms

an-isomorphic-copy-of-𝟚 : 𝟚 ≅ (Σ n ꞉ ℕ , (n ≡ 0) ∔ (n ≡ 1))
an-isomorphic-copy-of-𝟚 = {!!}
```
Exercise. Fill the above hole.

To be continued.
