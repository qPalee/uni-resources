# Week 3 - Lab and homework sheet solutions

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab3-solutions where
open import prelude hiding (𝟘-nondep-elim)
```

## Part I: Propositional logic

### Section 1: Disjunction

#### Exercise I.1.1

**Complete** the following proofs involving disjunctions.

```agda
private

 ∔-introduction-left  : {A B : Type} → A → A ∔ B
 ∔-introduction-left a = inl a

 ∔-introduction-right : {A B : Type} → B → A ∔ B
 ∔-introduction-right b = inr b
```

#### Exercise I.1.2

**Complete** the proof about disjunctions.

```agda
 ∔-elimination : {A B X : Type} → (A → X) → (B → X) → (A ∔ B → X)
 ∔-elimination f g (inl a) = f a
 ∔-elimination f g (inr b) = g b
```

### Section 2: Conjunction

#### Exercise I.2.1

**Complete** the following proofs involving conjunctions.

```agda
 ×-elimination-left : {A B : Type} → A × B → A
 ×-elimination-left (a , b) = a

 ×-elimination-right : {A B : Type} → A × B → B
 ×-elimination-right (a , b) = b
```

#### Exercise I.2.2

**Prove** the following:

```agda
 ×-introduction : {A B : Type} → A → B → A × B
 ×-introduction a b = a , b

 ×-introduction' : {A B X : Type} → (X → A) → (X → B) → (X → A × B)
 ×-introduction' f g x = ×-introduction (f x) (g x)
```

### Section 3: Implication

#### Exercise I.3.1

**Complete** the following proofs involving implications.

```agda
 uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
 uncurry f (a , b) = f a b

 curry : {A B X : Type} → (A × B → X) → (A → B → X)
 curry f a b = f (a , b)
```

You probably already know `curry` and `uncurry` from Haskell, but
notice how we can read them from a logical perspective: `uncurry`
says that if `A` implies that `B` implies `X`, then the conjunction of
`A` and `B` implies `X`.

#### Exercise I.3.2

**Prove** that implication is transitive.

```
 →-trans : {A B C : Type} → (A → B) → (B → C) → (A → C)
 →-trans f g a = g (f a)
```

Notice that the proof that implication is transitive is just function
composition.


### Section 4: Negation

The fact that falsity implies everything is known as the [_principle of
explosion_](https://en.wikipedia.org/wiki/Principle_of_explosion) or _ex falso
quodlibet_.

**Complete** the proof of the principle of explosion in Agda.

#### Exercise I.4.1

```agda
 𝟘-nondep-elim : {A : Type} → 𝟘 → A
 𝟘-nondep-elim ()
```

#### Exercise I.4.2

**Write** two *different* proofs that show "not false" (or "the empty
type is empty").

```agda
 not-false : ¬ 𝟘
 not-false x = 𝟘-nondep-elim x

 not-false' : ¬ 𝟘
 not-false' x = x
```

#### Exercise I.4.3

Before we proceed, we introduce some convenient notation
for multiple negations.

```agda
 ¬¬ : Type → Type
 ¬¬ A = ¬ (¬ A)

 ¬¬¬ : Type → Type
 ¬¬¬ A = ¬ (¬¬ A)
```

**Complete** the proof a proposition implies its own double negation,
by first proving the more general notion `dni`.

```agda
 dni : (A R : Type) → A → ((A → R) → R)
 dni A R a f = f a
 
 ¬¬-introduction : {A : Type} → A → ¬¬ A
 ¬¬-introduction {A} = dni A 𝟘
```

#### Exercise I.4.4

**Prove** that having three negations is the logically equivalent to
having a single negation.

```agda
 not-implies-not³ : {A : Type} → ¬ A → ¬¬¬ A
 not-implies-not³ ¬a ¬¬a = ¬¬a ¬a

 not³-implies-not : {A : Type} → ¬¬¬ A → ¬ A
 not³-implies-not ¬¬¬a a = ¬¬¬a (λ ¬a → ¬a a)
```

#### Exercise I.4.5

A particular case of interest of `→-trans` is the following. The
[contrapositive](https://en.wikipedia.org/wiki/Contraposition) of an
implication `A → B` is the implication `¬ B → ¬ A`.

**Complete** the proof of contraposition.

```agda
 contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
 contraposition f ¬b a = →-trans f ¬b a
```

This can also be read as "if we have a function A → B and B is empty,
then also A must be empty".

#### Exercise I.4.6

Use `contraposition` to **complete** the following proof of double
contraposition.

```agda
 double-contrapositive : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 double-contrapositive f ¬¬a ¬b = ¬¬a (contraposition f ¬b)
```

#### Exercise I.4.7

Use `contraposition` to **complete** the following two proofs that show
double negation is a monad.

```agda
 ¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 ¬¬-functor = double-contrapositive

 ¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
 ¬¬-kleisli f ¬¬a ¬b = ¬¬a (contraposition f (λ ¬¬b → ¬¬b ¬b))
```

### Section 5: De Morgan Laws and logical laws

The De Morgan laws cannot be proved in Agda, though some of the
implications involved in the De Morgan laws _can_ be. The following
exercises will involve proving these (and some other similar laws) for
Agda types.

#### Exercise I.5.1

**Complete** the proofs.

```agda
 de-morgan₁ : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
 de-morgan₁ f = f ∘ inl , f ∘ inr

 de-morgan₂ : {A B : Type} → ¬ A ∔ ¬ B → ¬ (A × B)
 de-morgan₂ (inl ¬a) (a , b) = ¬a a
 de-morgan₂ (inr ¬b) (a , b) = ¬b b
```

#### Exercise I.5.2

**Complete** the proofs.

```agda
 ¬-and-+-exercise₁ : {A B : Type} → ¬ A ∔ B → A → B
 ¬-and-+-exercise₁ (inl ¬a) a = 𝟘-nondep-elim (¬a a)
 ¬-and-+-exercise₁ (inr  b) a = b

 ¬-and-+-exercise₂ : {A B : Type} → ¬ A ∔ B → ¬ (A × ¬ B)
 ¬-and-+-exercise₂ (inl ¬a) (a , ¬b) = ¬a a
 ¬-and-+-exercise₂ (inr  b) (a , ¬b) = ¬b b
```

#### Exercise I.5.3

If  `A ∔ B` holds and `B` is false, then `A` must hold (and vice
versa). **Compelete** the proofs of this.

#### Exercise I.5.4

**Prove** the distributivity laws for `×` and `∔`.

```agda
 distributivity₁ : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
 distributivity₁ (inl (a , b)) = inl a , inl b
 distributivity₁ (inr c) = inr c , inr c

 distributivity₂ : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
 distributivity₂ (inl a , c) = inl (a , c)
 distributivity₂ (inr b , c) = inr (b , c)
```

#### Exercise I.5.5

Earlier, we showed that `A → ¬¬ A`; but we don't always have `¬¬ A → A`
in proofs-as-programs (this has to do with *computability theory*).
But sometimes we do. For example, if we know that `A ∔ ¬ A` holds,
then `¬¬A → A` follows.

**Prove** this fact.

```agda
 ¬¬-elim : {A : Type} → A ∔ ¬ A → ¬¬ A → A
 ¬¬-elim (inl  a) ¬¬a = a
 ¬¬-elim (inr ¬a) ¬¬a = 𝟘-nondep-elim (¬¬a ¬a)
```

## Part II: Logic with quantifiers

### Section 1: Sums

#### Exercise II.1.1

**Complete** the following constructions.

```agda
 Σ-introduction : {A : Type} {B : (A → Type)}
                → (a : A) → B a → (Σ a ꞉ A , B a)
 Σ-introduction a Ba = a , Ba

 Σ-to-× : {A : Type} {B : (A → Type)}
        → ((a , _) : (Σ a ꞉ A , B a)) → A × B a
 Σ-to-× (a , ba) = a , ba
```

#### Exercise II.1.2

**Complete** the following proof about sums over Booleans.

```agda
 Σ-on-Bool : {B : Bool → Type} → (Σ x ꞉ Bool , B x) → B true ∔ B false
 Σ-on-Bool (true  , b) = inl b
 Σ-on-Bool (false , b) = inr b
```

### Section 2: Products

#### Exercise II.2.1

Complete the proof.

```agda
 Π-apply : {A : Type} {B : (A → Type)}
         → ((a : A) → B a) → (a : A) → B a
 Π-apply f a = f a
```

#### Exercise II.2.2

**Prove**  the following.

```agda
 Π-→ : {A : Type} {B C : A → Type}
     → ((a : A) → B a → C a)
     → ((a : A) → B a) → ((a : A) → C a)
 Π-→ f g a = f a (g a)
```

### Section 3: Negation

#### Exercise III.3.1

**Show** that if there is no `x : X` with `A x`, then for all `x : X`
not `A x`.

```agda
not-exists-implies-forall-not : {X : Type} {A : X → Type}
                              → ¬ (Σ x ꞉ X , A x)
                              → (x : X) → ¬ A x
not-exists-implies-forall-not f x ax = f (x , ax)
```

Also **show** that the converse also holds.

```agda
forall-not-implies-not-exists : {X : Type} {A : X → Type}
                              → ((x : X) → ¬ A x)
                              → ¬ (Σ x ꞉ X , A x)
forall-not-implies-not-exists f (x , ax) = f x ax
```

Notice how these are particular cases of `curry` and `uncurry` from
Exercise I.3.1!

## Homework: Return of the Parity Theorem

In logic, we have a notion of *implication*; i.e. `A` implies `B`. We
also have a notion of *logical equivalence*, which says that
`A` implies `B` and `B` implies `A`.

### Exercise H.1

**Define** the type of logical equivalences between `A` and `B`.

```agda
_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)
```

Recall from the lecture the definitions of `is-even` and `is-odd`.

```agda
is-even : ℕ → Type
is-even 0 = 𝟙
is-even 1 = 𝟘
is-even (suc (suc n)) = is-even n

is-odd : ℕ → Type
is-odd n = ¬ is-even n
```

In the statement of the Parity Theorem (which we now call
`ParityTheorem'`), we implicitly gave other definitions of `is-even`
and `is-odd`.

```agda
ParityTheorem' : Type
ParityTheorem'
 = (n : ℕ) → Σ m ꞉ ℕ , (n ≡ (m + m)) ∔ (n ≡ (suc (m + m)))

is-even' : ℕ → Type
is-even' n = Σ m ꞉ ℕ , n ≡ (m + m)

is-odd' : ℕ → Type
is-odd' n = Σ m ꞉ ℕ , n ≡ suc (m + m)
```

### Exercise H.2

**Prove** that the two definitions of evenness are logically
equivalent.

```agda
lemma-2 : (k m : ℕ) →  suc (k + m) ≡ k + suc m
lemma-2 zero m = refl (suc m)
lemma-2 (suc k) m = ap suc (lemma-2 k m)

pred : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

even-iff-even' : (n : ℕ) → is-even n ↔ is-even' n
even-iff-even' 0 = left , right
 where
  left : is-even 0 → is-even' 0
  left _ = zero , refl zero
  right : is-even' 0 → is-even 0
  right _ = ⋆
even-iff-even' 1 = left , right
 where
  left : is-even 1 → is-even' 1
  left ()
  right : is-even' 1 → is-even 1
  right (1 , ())
  right (suc (suc m) , ())
even-iff-even' (suc (suc n)) = left , right
 where
  IH : is-even n ↔ is-even' n
  IH = even-iff-even' n
  left : is-even (suc (suc n)) → is-even' (suc (suc n))
  left e = m , p
   where
    ih : is-even n → is-even' n
    ih = fst IH
    i : is-even' n
    i = ih e
    k : ℕ
    k = fst i
    q : n ≡ k + k
    q = snd i
    m : ℕ
    m = suc k
    p : suc (suc n) ≡ m + m
    p = ap suc (trans (ap suc q) (lemma-2 k k))
  right : is-even' (suc (suc n)) → is-even (suc (suc n))
  right (suc m , p) = i
   where
    ih : is-even' n → is-even n
    ih = snd IH
    k : ℕ
    k = m
    q : n ≡ k + k
    q = ap pred (ap pred q')
     where
      q' : suc (suc n) ≡ suc (suc (k + k))
      q' = trans p (sym (lemma-2 (suc m) m))
    i : is-even n
    i = ih (k , q)
```

### Exercise H.3

**Prove** that the two definitions of oddness are logically equivalent.

```agda
odd-iff-odd' : (n : ℕ) → is-odd n ↔ is-odd' n
odd-iff-odd' 0 = left , right
 where
  left : is-odd 0 → is-odd' 0
  left z = 𝟘-nondep-elim (z ⋆)
  right : is-odd' 0 → is-odd 0
  right ()
odd-iff-odd' 1 = left , right
 where
  left : is-odd 1 → is-odd' 1
  left _ = 0 , refl 1
  right : is-odd' 1 → is-odd 1
  right _ ()
odd-iff-odd' (suc (suc n)) = left , right
 where
  IH : is-odd n ↔ is-odd' n
  IH = odd-iff-odd' n
  left : is-odd (suc (suc n)) → is-odd' (suc (suc n))
  left e = m , p
   where
    ih : is-odd n → is-odd' n
    ih = fst IH
    i : is-odd' n
    i = ih e
    k : ℕ
    k = fst i
    q : n ≡ suc (k + k)
    q = snd i
    m : ℕ
    m = suc k
    p : suc (suc n) ≡ suc (m + m)
    p = ap (suc ∘ suc) (trans q (lemma-2 k k))
  right : is-odd' (suc (suc n)) → is-odd (suc (suc n))
  right (suc m , p) = i
   where
    ih : is-odd' n → is-odd n
    ih = snd IH
    k : ℕ
    k = m
    q : n ≡ suc (k + k)
    q = ap (pred ∘ pred) q'
     where
      q' : suc (suc n) ≡ suc (suc (suc (k + k)))
      q' = trans p (sym (lemma-2 (suc (suc m)) m))
    i : is-odd n
    i = ih (k , q)
```

### Exercise H.4

**State** the Parity Theorem using the original definitions of evenness
and oddness.

```agda
ParityTheorem : Type
ParityTheorem = (n : ℕ) → is-even n ∔ is-odd n
```

### Exercise H.5

**Prove** the Parity Theorem using the original definitions of evenness
and oddness.

```agda
parity-proof : ParityTheorem
parity-proof 0 = inl ⋆
parity-proof 1 = inr id
parity-proof (suc (suc n)) = ∔-nondep-elim inl inr (parity-proof n)
```
