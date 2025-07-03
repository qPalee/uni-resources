# Week 4 - Lab Sheet

```agda
module exercises.lab4 where
 open import prelude
 open import isomorphisms
 open import List-functions
```

## Part I: Decidability and decidable equality

Recall the definition of a *decidable type* from the lecture notes:

```agda
 is-decidable : Type → Type
 is-decidable A = A ∔ ¬ A
```

To assert `is-decidable A` for some type `A` is to say that type `A` satisfies
the law of excluded middle: we can either construct an inhabitant of `A` or
prove that the existence of an inhabitant for `A` is impossible.

### Exercise 1.1 

Decidable types satisfy many useful closure properties.  Many of these
are proven in the lecture notes, but it is extremely useful to attempt
to prove them yourself as an exercise.

First, show that if two types are logically equivalent, then the decidability
of one implies the decidability of the other:

```agda
 map-decidable : {A B : Type} → (A ⇔ B) → is-decidable A → is-decidable B
 map-decidable = {!!} 
```

Now strengthen this result by showing that if two types are logically
equivalent, then the decidability of one is logically equivalent to
the decidability of the other:

```agda
 map-decidable-corollary : {A B : Type} → (A ⇔ B) → (is-decidable A ⇔ is-decidable B)
 map-decidable-corollary = {!!}
```

Show that decidability is preserved by conjunction, disjunction, implication and negation:

```agda
 ×-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A × B)
 ×-preserves-decidability = {!!}
 
 ∔-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A ∔ B)
 ∔-preserves-decidability = {!!}

 →-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A → B)
 →-preserves-decidability = {!!} 

 ¬-preserves-decidability : {A : Type}
                          → is-decidable A
                          → is-decidable (¬ A)
 ¬-preserves-decidability = {!!}
```

### Exercise 1.2

In the lecture, we stated that a type was decidable if and only if one
could find a `b : Bool` such that `A` holds if and only if the boolean
`b` is `true`.  We also wrote the generalization of this statement for
predicates.  Complete the proof of this statement:

```agda
 is-decidable-predicate : {A : Type} (P : A → Type) → Type
 is-decidable-predicate {A} P = (a : A) → is-decidable (P a) 

 decidability-of-predicates : {A : Type} (P : A → Type)
   → is-decidable-predicate P ⇔ Σ Q ꞉ (A → Bool) , ((a : A) → P a ⇔ (Q a ≡ true))
 decidability-of-predicates = {!!}
```

### Exercise 1.3 (Harder)

The lecture notes contain a definition of what we call "exhaustively searchable" types:
[lecture notes](../decidability.lagda.md)

```agda
 is-exhaustively-searchable : Type → Type₁
 is-exhaustively-searchable X = (A : X → Type)
                              → is-decidable-predicate A
                              → is-decidable (Σ x ꞉ X , A x)
```                              

Recall the definition of the family `Fin` of finite types:

```agda
 data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  succ : {n : ℕ} → Fin n → Fin (suc n)
```
(You can read more about this type [here](../Fin.lagda.md))

Show that `Fin n` is exhaustively searchable for every `n`.

```agda
 Fin-is-exhaustively-searchable : (n : ℕ) → is-exhaustively-searchable (Fin n)
 Fin-is-exhaustively-searchable = {!!} 
```

## Part II: Order on the natural numbers

In this part we will study two ways of expressing that a natural number is less
than or equal to another natural number.

The first definition is an inductive one.

```agda
 data _≤_ : ℕ → ℕ → Type where
  ≤-zero : (  y : ℕ) → 0 ≤ y
  ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y
```

It says:
1. that zero is less than or equal to any natural number;
1. if `x` is less than or equal to `y`, then `suc x` is less than or equal to `suc y`.

The second definition uses a `Σ`-type.

```agda
 _≤'_ : ℕ → ℕ → Type
 x ≤' y = Σ k ꞉ ℕ , x + k ≡ y
```

It says that `x` is less than or equal to `y` if we have some `k : ℕ`
such that `x + k ≡ y`.

We will prove that the two definitions are logically equivalent.

### Exercise 2.1

In order to prove that the first definition implies the second, we first
prove two little lemmas about `_≤'_`.

Note that they amount to the constructors of `_≤_`.

```agda
 ≤'-zero : (  y : ℕ) → 0 ≤' y
 ≤'-zero = {!!}

 ≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
 ≤'-suc = {!!}
```

**Prove** the two little lemmas about `_≤'_`.

### Exercise 2.2

We now prove that the first definition implies the second.

```agda
 ≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
 ≤-prime = {!!}
```

**Prove** that `x ≤ y` implies `x ≤' y` using the little lemmas from 3.1.

### Exercise 2.3

The other direction is slightly trickier.

```agda
 ≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
 ≤-unprime = {!!}
```

**Prove** that `x ≤' y` implies `x ≤ y`.

*Hint:* The base case only requires pattern matching on `x`, whereas
the inductive case requires further pattern matching.

### Exercise 2.4

The order on the natural numbers is transitive, meaning that if
`x ≤ y` and `y ≤ z` then also `x ≤ z`. We can prove this for
both our definitions of the order.

```agda
 ≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
 ≤-trans = {!!}

 ≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
 ≤'-trans = {!!}
```

**Complete** the proofs that `_≤_` and `_≤'_` are transitive.

### Exercise 2.5

Recall the definition of a decidable relation:

```agda
 is-decidable-relation : {A : Type} (R : A → A → Type) → Type
 is-decidable-relation {A} R = (a₀ a₁ : A) → is-decidable (R a₀ a₁) 
```

Prove that `_≤_` is decidable:

```agda
 ≤-is-decidable : is-decidable-relation _≤_
 ≤-is-decidable = {!!} 
```

## Homework: Isomorphisms

We will be speaking about the concept of isomorphism in the lectures
this week.  These problems can be completed after attending these
lectures.

### Exercise H.1

**Show** that X × Y is isomorphic to Y × X using the above template.

```agda
 ×-iso : (X Y : Type) → X × Y ≅ Y × X
 ×-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : X × Y → Y × X
   f = {!!}

   g : Y × X → X × Y
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

### Exercise H.2

**Show** that X ∔ Y is isomorphic to Y ∔ X using the above template.

```agda
 +-iso : (X Y : Type) → X ∔ Y ≅ Y ∔ X
 +-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : X ∔ Y → Y ∔ X
   f = {!!}

   g : Y ∔ X → X ∔ Y
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

### Exercise 2.3

**Show** that the the type `List A` is isomorphic to the type `Σ (Vector A)`.

```agda
 lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
 lists-from-vectors {A}
  = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : List A → Σ n ꞉ ℕ , Vector A n
   f = {!!}

   g : Σ n ꞉ ℕ , Vector A n → List A
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
