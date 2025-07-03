# Week 4 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}
module exercises.lab4-solutions where
 open import prelude
 open import isomorphisms
 open import List-functions
 open import natural-numbers-functions using (+-assoc)
 open import negation
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
 map-decidable (f , g) (inl x) = inl (f x)
 map-decidable (f , g) (inr h) = inr (λ y → h (g y))
```

Now strengthen this result by showing that if two types are logically
equivalent, then the decidability of one is logically equivalent to
the decidability of the other:

```agda
 map-decidable-corollary : {A B : Type} → (A ⇔ B) → (is-decidable A ⇔ is-decidable B)
 map-decidable-corollary (f , g) = map-decidable (f , g) , map-decidable (g , f)
```

Show that decidability is preserved by conjunction, disjunction, implication and negation:

```agda
 ×-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A × B)
 ×-preserves-decidability (inl x) (inl y) = inl (x , y)
 ×-preserves-decidability (inl _) (inr k) = inr (λ (x , y) → k y)
 ×-preserves-decidability (inr h) _       = inr (λ (x , y) → h x)


 ∔-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A ∔ B)
 ∔-preserves-decidability (inl x) _       = inl (inl x)
 ∔-preserves-decidability (inr _) (inl y) = inl (inr y)
 ∔-preserves-decidability (inr h) (inr k) = inr (∔-nondep-elim h k)

 →-preserves-decidability : {A B : Type}
                          → is-decidable A
                          → is-decidable B
                          → is-decidable (A → B)
 →-preserves-decidability _       (inl y) = inl (λ _ → y)
 →-preserves-decidability (inl x) (inr k) = inr (λ f → k (f x))
 →-preserves-decidability (inr h) (inr k) = inl (λ x → 𝟘-elim (h x))

 𝟘-is-decidable : is-decidable 𝟘
 𝟘-is-decidable = inr (λ x → x) 

 ¬-preserves-decidability : {A : Type}
                          → is-decidable A
                          → is-decidable (¬ A)
 ¬-preserves-decidability d = →-preserves-decidability d 𝟘-is-decidable
```

### Exercise 1.2

In the lecture, we stated that a type was decidable if and only if one
could find a `b : Bool` such that `A` holds if and only if the boolean
`b` is `true`.  We also wrote the generalization of this statement for
predicates.  Complete the proof of this statement:

```agda
 is-decidable-predicate : {A : Type} (P : A → Type) → Type
 is-decidable-predicate {A} P = (a : A) → is-decidable (P a) 

 decidability-with-booleans : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
 decidability-with-booleans A = f , g
   where
    f : is-decidable A → Σ b ꞉ Bool , (A ⇔ b ≡ true)
    f (inl x) = true , (α , β)
     where
      α : A → true ≡ true
      α _ = refl true

      β : true ≡ true → A
      β _ = x

    f (inr ν) = false , (α , β)
     where
      α : A → false ≡ true
      α x = 𝟘-elim (ν x)

      β : false ≡ true → A
      β ()

    g : (Σ b ꞉ Bool , (A ⇔ b ≡ true)) → is-decidable A
    g (true ,  α , β) = inl (β (refl true))
    g (false , α , β) = inr (false-is-not-true ∘ α)

 decidability-of-predicates : {A : Type} (P : A → Type)
   → is-decidable-predicate P ⇔ Σ Q ꞉ (A → Bool) , ((a : A) → P a ⇔ (Q a ≡ true))
 decidability-of-predicates {A} P = f , g
 
   where
    f : is-decidable-predicate P → Σ α ꞉ (A → Bool) , ((x : A) → P x ⇔ α x ≡ true)
    f d = α , β
     where
      α : A → Bool
      α x = fst (lr-implication I (d x))
       where
        I : is-decidable (P x) ⇔ Σ b ꞉ Bool , (P x ⇔ b ≡ true)
        I = decidability-with-booleans (P x)

      β : (x : A) → P x ⇔ α x ≡ true
      β x = ϕ , γ
       where
        I : is-decidable (P x) → Σ b ꞉ Bool , (P x ⇔ b ≡ true)
        I = lr-implication (decidability-with-booleans (P x))

        II : Σ b ꞉ Bool , (P x ⇔ b ≡ true)
        II = I (d x)

        ϕ : P x → α x ≡ true
        ϕ = lr-implication (snd II)

        γ : α x ≡ true → P x
        γ = rl-implication (snd II)

    g : (Σ α ꞉ (A → Bool) , ((x : A) → P x ⇔ α x ≡ true)) → is-decidable-predicate P
    g (α , ϕ) = d
     where
      d : is-decidable-predicate P
      d x = III
       where
        I : (Σ b ꞉ Bool , (P x ⇔ b ≡ true)) → is-decidable (P x)
        I = rl-implication (decidability-with-booleans (P x))

        II : Σ b ꞉ Bool , (P x ⇔ b ≡ true)
        II = (α x , ϕ x)

        III : is-decidable (P x)
        III = I II

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
 Fin-search-base : is-exhaustively-searchable (Fin 0)
 Fin-search-base A d = inr n
   where
    n : ¬ (Σ x ꞉ Fin 0 , A x)
    n ((), _)

 Fin-search-step : (n : ℕ)
                  → is-exhaustively-searchable (Fin n)
                  → is-exhaustively-searchable (Fin (suc n))
 Fin-search-step n s = I
   where
    I : is-exhaustively-searchable (Fin (suc n))
    I A d = II (d zero) -- Check whether A zero holds using d and feed this to II.
     where
      II : A zero ∔ ¬ A zero → is-decidable (Σ x ꞉ Fin (suc n) , A x)
      II (inl a) = inl (zero , a) -- We have that a : A zero, so we've found something
      II (inr f) = IV III         -- f says that ¬ A zero.
                                  -- So search after zero using s with III,
                                  -- And then feed this to IV to see whether we got
                                  -- something or not.
       where
        III : is-decidable (Σ x ꞉ Fin n , A (succ x))
        III = s (λ x → A (succ x)) (λ x → d (succ x))

        IV : is-decidable (Σ x ꞉ Fin n , A (succ x))
           → is-decidable (Σ x ꞉ Fin (suc n) , A x)
        IV (inl (x , a)) = inl (succ x , a) -- We've found something.
        IV (inr g)       = inr V          -- g says that ¬ (Σ x ꞉ Fin (succ n) , A (succ x)),
                                     -- so there is nothing to be found, which is
                                     -- proved by V with two cases, using f and g.
         where
          V : ¬ (Σ x ꞉ Fin (suc n) , A x)
          V (zero   , a) = f a
          V (succ x , a) = g (x , a)

 Fin-is-exhaustively-searchable : (n : ℕ) → is-exhaustively-searchable (Fin n)
 Fin-is-exhaustively-searchable zero = Fin-search-base
 Fin-is-exhaustively-searchable (suc n) = Fin-search-step n (Fin-is-exhaustively-searchable n)
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
 ≤'-zero y = y , refl y

 ≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
 ≤'-suc x y (n , p) = n , ap suc p
```

**Prove** the two little lemmas about `_≤'_`.

### Exercise 2.2

We now prove that the first definition implies the second.

```agda
 ≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
 ≤-prime 0            y  (≤-zero  y)   = ≤'-zero y
 ≤-prime (suc x) (suc y) (≤-suc x y p) = ≤'-suc x y (≤-prime x y p)
```

**Prove** that `x ≤ y` implies `x ≤' y` using the little lemmas from 3.1.

### Exercise 2.3

The other direction is slightly trickier.

```agda
 ≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
 ≤-unprime zero y (n , p)
  = ≤-zero y
 ≤-unprime (suc x) (suc .(x + n)) (n , refl .(suc (x + n)))
  = ≤-suc x (x + n) (≤-unprime x (x + n) (n , refl (x + n)))
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
 ≤-trans zero y z p q
  = ≤-zero z
 ≤-trans (suc x) .(suc y) .(suc z) (≤-suc .x y p) (≤-suc .y z q)
  = ≤-suc x z (≤-trans x y z p q)

 ≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
 ≤'-trans x .(x + n) .((x + n) + m) (n , refl .(x + n)) (m , refl .((x + n) + m))
  = (n + m) , sym (+-assoc x n m) 
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
 suc-is-not-≤-zero : (n : ℕ) → ¬ (suc n ≤ zero)
 suc-is-not-≤-zero n ()

 ≤-pred : {m n : ℕ} → suc m ≤ suc n → m ≤ n
 ≤-pred (≤-suc _ _ m≤n) = m≤n
 
 ≤-is-decidable : is-decidable-relation _≤_
 ≤-is-decidable zero n = inl (≤-zero n)
 ≤-is-decidable (suc m) zero = inr (suc-is-not-≤-zero m)
 ≤-is-decidable (suc m) (suc n) =
   ∔-nondep-elim
   (λ m≤n → inl (≤-suc m n m≤n))
   (λ ¬m≤n → inr (λ sm≤sn → ¬m≤n (≤-pred sm≤sn)))
   (≤-is-decidable m n)
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
   f (x , y) = y , x

   g : Y × X → X × Y
   g (y , x) = x , y

   gf : g ∘ f ∼ id
   gf (x , y) = refl (x , y)

   fg : f ∘ g ∼ id
   fg (y , x) = refl (y , x)

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
   f (inl x) = inr x
   f (inr y) = inl y

   g : Y ∔ X → X ∔ Y
   g (inl y) = inr y
   g (inr x) = inl x

   gf : g ∘ f ∼ id
   gf (inl x) = refl (inl x)
   gf (inr y) = refl (inr y)

   fg : f ∘ g ∼ id
   fg (inl y) = refl (inl y)
   fg (inr x) = refl (inr x)

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
   f []        = 0 , []
   f (x :: xs) = suc (fst (f xs)) , (x :: snd (f xs))

   g : Σ n ꞉ ℕ , Vector A n → List A
   g (0     , []       ) = []
   g (suc n , (x :: xs)) = x :: g (n , xs)

   gf : g ∘ f ∼ id
   gf []        = refl []
   gf (x :: xs) = ap (x ::_) (gf xs)

   fg : f ∘ g ∼ id
   fg (0     , []       ) = refl (0 , [])
   fg (suc n , (x :: xs)) =
    ap (λ - → suc (fst -) , (x :: snd -)) (fg (n , xs))

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
