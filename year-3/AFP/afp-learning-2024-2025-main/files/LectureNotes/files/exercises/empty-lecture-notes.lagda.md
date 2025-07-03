```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.empty-lecture-notes where

open import general-notation
open import empty-type
open import unit-type
open import binary-type
open import products
open import sums
open import binary-products
open import binary-sums
```

# Week 2

## The type `ℕ` of natural numbers

We repeat the definition given [earlier](introduction.lagda.md):
```agda
data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
```

### Elimination principle

The elimination principle for all type formers follow the same pattern: they tell us how to define dependent functions *out* of the given type. In the case of natural numbers, the eliminator gives [primitive recursion](https://encyclopediaofmath.org/wiki/Primitive_recursion). Given a base case `a : A 0` and a step function `f : (k : ℕ) → A k → A (suc k)`, we get a function `h : (n : ℕ) → A n` defined by primitive recursion as follows:
```agda
ℕ-elim : {A : ℕ → Type}
       → A 0
       → ((k : ℕ) → A k → A (suc k))
       → (n : ℕ) → A n
ℕ-elim = {!!}
```
In usual accounts of primitive recursion outside type theory, one encounters the following particular case of primitive recursion, which is the non-dependent version of the above.
```agda

ℕ-nondep-elim : {A : Type}
              → A
              → (ℕ → A → A)
              → ℕ → A
ℕ-nondep-elim = {!!}
```
Notice that this is like `fold` for lists.
There is a further restricted version, which is usually called iteration:
```agda
ℕ-iteration : {A : Type}
            → A
            → (A → A)
            → ℕ → A
ℕ-iteration = {!!}
```
Intuitively, `ℕ-iteration a f n = f (f (f (⋯ f a)))` where we apply `n` times the function `f` to the element `a`, which sometimes is written `fⁿ(a)` in the literature.

### The induction principle for ℕ

In logical terms, one can see immediately what the type of `ℕ-elim` is: it is simply the [principle of induction on natural numbers](https://en.wikipedia.org/wiki/Mathematical_induction), which say that in order to show that a property `A` holds for all natural numbers, it is enough to show that `A 0` holds (this is called the base case), and that if `A k` holds then so does `A (suc k)` (this is called the induction step). In Agda, in practice, we don't explicitly use this induction principle, but instead write definition recursively, just as we defined the above function `h` recursively.

### Addition and multiplication

As an **exercise**, you may try to define the following functions using some version of the above eliminators instead of using pattern matching and recursion:

```agda
_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}

infixr 20 _+_
infixr 30 _*_
```

## The identity type former `_≡_`

The original and main terminology for the following type is *identity type*, but sometimes it is also called the *equality type*. Sometimes this is also called *propositional equality*, but we will avoid this terminology as it sometimes leads to confusion.
```agda
data _≡_ {A : Type} : A → A → Type where
 refl : (x : A) → x ≡ x

infix 0 _≡_
```

### Elimination principle

The elimination principle for this type is defined as follows:
```agda
≡-elim : {X : Type} (A : (x y : X) → x ≡ y → Type)
       → ((x : X) → A x x (refl x))
       → (x y : X) (p : x ≡ y) → A x y p
≡-elim = {!!}
```
This says that in order to show that `A x y p` holds for all `x y : X` and `p : x ≡ y`, it is enough to show that `A x x (refl x)` holds for all `x : X`.
In the literature, this elimination principle is called `J`. Again, we are not going to use it explicitly, because we can use definitions by pattern matching on `refl`, just as we did for defining it.

We also have the non-dependent version of the eliminator:
```agda
≡-nondep-elim : {X : Type} (A : X → X → Type)
              → ((x : X) → A x x)
              → (x y : X) → x ≡ y → A x y
≡-nondep-elim = {!!}
```
A property of two variables like `A` above is referred to as a *relation*. The assumption `(x : X) → A x x` says that the relation is reflexive. Then the non-dependent version of the principle says that the reflexive relation given by the identity type `_≡_` can always be mapped to any reflexive relation, or we may say that `_≡_` is the smallest reflexive relation on the type `X`.

### Fundamental constructions with the identity type

As an exercise, you may try to rewrite the following definitions to use `≡-nondep-elim` instead of pattern matching on `refl`:
```agda
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = {!!}

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym = {!!}

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap = {!!}

ap₂ : {A B C : Type} (f : A → B → C) {x x' : A} {y y' : B}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂ = {!!}

transport : {X : Type} (A : X → Type)
          → {x y : X} → x ≡ y → A x → A y
transport = {!!}
```
We have already seen the first three. In the literature, `ap` is often called `cong`. In logical terms, the last one, often called `subst` in the literature, says that if `x` is equal `y` and `A x` holds, then so does `A y`. That is, we can substitute equals for equals in logical statements.

### Pointwise equality of functions

It is often convenient to work with *pointwise equality* of functions, defined as follows:
```agda
_∼_ : {A : Type} {B : A → Type} → ((x : A) → B x) → ((x : A) → B x) → Type
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_
```

Unfortunately, it is not provable or disprovable in Agda that pointwise equal functions are equal, that is, that `f ∼ g` implies `f ≡ g` (but it is provable in [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html), which is outside the scope of these lecture notes). This principle is very useful and is called [function extensionality](function-extensionality.lagda.md).

### Notation for equality reasoning

When writing `trans p q` we lose type information of the
identifications `p : x ≡ y` and `q : y ≡ z`, which makes some definitions using `trans` hard to read. We now
introduce notation to be able to write e.g.

   > `x ≡⟨ p ⟩`

   > `y ≡⟨ q ⟩`

   > `z ≡⟨ r ⟩`

   > `t ∎`

rather than the more unreadable `trans p (trans q r) : x ≡ t`.

```agda
_≡⟨_⟩_ : {X : Type} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {X : Type} (x : X) → x ≡ x
x ∎ = refl x

infixr  0 _≡⟨_⟩_
infix   1 _∎
```
We'll see examples of uses of this in other handouts.

## The booleans

We discuss the elimination principle for the booleans. The booleans
are defined by constructors `true` and `false`:
```agda
data Bool : Type where
 true false : Bool
```
### `if-then-else`

The non-dependent eliminator of the type of booleans amounts to `if-then-else`
```agda
if_then_else_ : {A : Type} → Bool → A → A → A
if_then_else_ = {!!}
```
In general, the non-dependent elimination principle of a type explains how to "get out of the type", whereas the constructors tell us how to "get into the type".

### Dependent `if-then-else`

Notice that both `x` (the `then` branch) and `y` (the `else` branch) have the same type, name `A`. Using dependent type, we can have different types in the dependent version of the eliminator. We make the type `A` depend on the boolean condition of the `if-then-else`. This means that now we will have `A : Bool → Type` instead of `A : Bool`. This is a function that given a boolean `b : Bool`, returns a type `A b`. Functions whose return value is a type are also called *type families*. Also `A b` is called a *dependent type*. It depends on the value of the boolean `b`. Here is an example, which we make private to this module.
```agda
private
 A-example : Bool → Type
 A-example true  = ℕ
 A-example false = Bool
```
Using this idea, we have the following dependently-typed version of `if_then_else_`, which now has four explicit arguments. We make `A` explicit this time, because Agda can hardly ever infer it.
```agda
dependent-on_if_then_else_ : (A : Bool → Type) → (b : Bool) → A true → A false → A b
dependent-on_if_then_else_ = {!!}
```
Notice that the return type `A b` depends on the second argument `b` of the function.
Notice also that `x : A true` and `y : A false`.
```agda
private
 example₀ : (b : Bool) → A-example b
 example₀ b = dependent-on A-example if b then 3 else true
```
This works because `3 : A-example true` and `true : A-example false`. So the dependent version of `if-then-else` allows the `then` and `else` branches have different types, which depend on the type of the condition.

### The official definition of the eliminator of the type of booleans

Traditionally the argument of the type we want to eliminate (the booleans in our case) is written last:
```agda
Bool-elim : (A : Bool → Type)
          → A true
          → A false
          → (b : Bool) → A b
Bool-elim = {!!}
```
The type of `Bool-elim` says that if we provide elements of the type `A true` and `A false`, we get a function `(b : Bool) → A b`.

The non-dependent version is a particular case of the dependent version, by considering the constant type family `λ _ → A` for a given `A : Type`. This time we make the first argument `A` implicit:
```agda
Bool-nondep-elim : {A : Type}
                 → A
                 → A
                 → Bool → A
Bool-nondep-elim = {!!}
```
This produces a function `Bool → A` from two given elements of the type `A`.

### Logical reading of the eliminator

The *conclusion* of `Bool-elim` is `(b : Bool) → A b`, which under *propositions as types* has the logical reading "for all `b : Bool`, the proposition `A b` holds". The *hypotheses* `A true` and `A false` are all is needed to reach this conclusion.

Thus the logical reading of `Bool-elim` is:

 * In order to prove that "for all `b : Bool`, the proposition `A b` holds"

it is enough to prove that

 * the proposition `A true` holds, and

 * the proposition `A false` holds,

which should be intuitively clear.

### Examples of proofs using the eliminator

First define
```agda
not : Bool → Bool
not = {!!}
```
Then we can prove that `not` can be expressed using `if-then-else`:
```agda
not-defined-with-if : (b : Bool) → not b ≡ if b then false else true
not-defined-with-if = {!!}
```
In situations where we try to use `_` but Agda can't determine that there is a *unique* answer to what `_` should be, the colour yellow is used to indicate this in the syntax highlighting, accompanied by an error message. To give another example, we first define the notion of an [involution](https://en.wikipedia.org/wiki/Involution_(mathematics)), or involutive function:
```agda
is-involution : {X : Type} → (X → X) → Type
is-involution {X} f = (x : X) → f (f x) ≡ x
```
For example, list reversal is an involution. Another example is boolean negation:
```agda
not-is-involution : is-involution not
not-is-involution = {!!}
```
Very often we will give definitions by pattern-matching as above instead of
`Bool-elim`. But the concept of eliminator for a type remains useful, and it is what `MLTT` (Martin-Löf Type Theory), the foundation of our programming language Agda, uses to define types. Types are defined by formation rules, construtors, eliminators, and equations explaining how the constructors interact with the eliminators. Pattern-matching can be considered as "syntax sugar" for definitions using eliminators. Usually definitions using pattern matching are more readable than definitions using eliminators, but they are equivalent to definitions using eliminators.

Notice that in the definition of `is-involution` we needed to explicitly indicate the implicit argument `X` using curly brackets. Agda allows the notation `∀` in order to be able to omit the type `X`, provided it can be inferred automaticaly, which it can in our situation:
```agda
is-involution' : {X : Type} → (X → X) → Type
is-involution' f = ∀ x → f (f x) ≡ x
```

### Some useful functions

```agda
_&&_ : Bool → Bool → Bool
_&&_ = {!!}

_||_ : Bool → Bool → Bool
_||_ = {!!}

infixr 20 _||_
infixr 30 _&&_
```

## Reasoning with negation

[Recall that](empty-type.lagda.md) we defined the negation `¬ A` of a type `A` to be the function type `A → 0`,
and that we also wrote `is-empty A` as a synonym of `¬ A`.

### Emptiness of the empty type

We have the following proof of "not false" or "the empty type is empty":
```agda
not-false : ¬ 𝟘
not-false = {!!}
```
A lot of things about negation don't depend on the fact that the target type of the function type is `𝟘`. We will begin by proving some things about negation by generalizing `𝟘` to any type `R` of "results".

### Implication from disjunction and negation

If `¬ A` or `B`, then `A implies B`:
```agda
implication-from-disjunction-and-negation : {A B : Type} → ¬ A ∔ B → (A → B)
implication-from-disjunction-and-negation = {!!}
```

### Contrapositives

If `A` implies `B`, then `B → R` implies `A → R`:
```agda
arrow-contravariance : {A B R : Type}
                     → (A → B)
                     → (B → R) → (A → R)
arrow-contravariance = {!!}
```
A particular case of interest is the following. The [contrapositive](https://en.wikipedia.org/wiki/Contraposition) of an implication `A → B` is the implication `¬ B → ¬ A`:
```agda
contrapositive : {A B : Type} → (A → B) → (¬ B → ¬ A)
contrapositive = {!!}

double-contrapositive : {A B : Type} → (A → B) → (¬ (¬ A) → ¬ (¬ B))
double-contrapositive = {!!}

```
This can also be read as "if we have a function A → B and B is empty, then also A must be empty".

### Double and triple negations

We now introduce notation for double and triple negation, to reduce the number of needed brackets:

```agda
¬¬_ ¬¬¬_ : Type → Type
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
```
We have that `A` implies `¬¬ A`. This is called double negation introduction. More generally, we have the following:
```agda
dni : (A R : Type) → A → ((A → R) → R)
dni = {!!}

¬¬-intro : {A : Type} → A → ¬¬ A
¬¬-intro = {!!}
```
We don't always have `¬¬ A → A` in proofs-as-programs. This has to do with *computability theory*. But sometimes we do. For example, if we know that `A ∔ ¬ A` then `¬¬A → A` follows:
```agda
module _ where
 private
  ¬¬-elim : {A : Type} → A ∔ ¬ A → ¬¬ A → A
  ¬¬-elim = {!!}
```
For more details, see the lecture notes on [decidability](decidability.lagda.md), where we discuss `¬¬-elim` again.
But three negations always imply one, and conversely:
```agda
three-negations-imply-one : {A : Type} → ¬¬¬ A → ¬ A
three-negations-imply-one = {!!}

one-negation-implies-three : {A : Type} → ¬ A → ¬¬¬ A
one-negation-implies-three = {!!}
```

### Negation of the identity type

It is useful to introduce a notation for the negation of the [identity type](identity-type.lagda.md):
```agda
_≢_ : {X : Type} → X → X → Type
x ≢ y = ¬ (x ≡ y)

≢-sym : {X : Type} {x y : X} → x ≢ y → y ≢ x
≢-sym = {!!}

false-is-not-true : false ≢ true
false-is-not-true = {!!}

true-is-not-false : true ≢ false
true-is-not-false = {!!}
```
The following is more interesting:
```agda
not-false-is-true : (x : Bool) → x ≢ false → x ≡ true
not-false-is-true = {!!}

not-true-is-false : (x : Bool) → x ≢ true → x ≡ false
not-true-is-false = {!!}
```

### Disjointness of binary sums

We now show something that is intuitively the case:
```agda
inl-is-not-inr : {X Y : Type} {x : X} {y : Y} → inl x ≢ inr y
inl-is-not-inr = {!!}
```
Agda just knows it.

### Disjunctions and negation

If  `A or B` holds and `B` is false, then `A` must hold:
```agda
right-fails-gives-left-holds : {A B : Type} → A ∔ B → ¬ B → A
right-fails-gives-left-holds = {!!}

left-fails-gives-right-holds : {A B : Type} → A ∔ B → ¬ A → B
left-fails-gives-right-holds = {!!}
```

### Negation of the existential quantifier:

If there is no `x : X` with `A x`, then for all `x : X` not `A x`:
```agda
not-exists-implies-forall-not : {X : Type} {A : X → Type}
                              → ¬ (Σ x ꞉ X , A x)
                              → (x : X) → ¬ A x
not-exists-implies-forall-not = {!!}
```
The converse also holds:
```agda
forall-not-implies-not-exists : {X : Type} {A : X → Type}
                              → ((x : X) → ¬ A x)
                              → ¬ (Σ x ꞉ X , A x)
forall-not-implies-not-exists = {!!}
```
Notice how these are particular cases of [`curry` and `uncurry`](https://en.wikipedia.org/wiki/Currying).

### Implication truth table

Here is a proof of the implication truth-table:
```agda

implication-truth-table : ((𝟘 → 𝟘) ⇔ 𝟙)
                        × ((𝟘 → 𝟙) ⇔ 𝟙)
                        × ((𝟙 → 𝟘) ⇔ 𝟘)
                        × ((𝟙 → 𝟙) ⇔ 𝟙)
implication-truth-table = {!!}
```

## Function extensionality

Recall that we defined pointwise equality `f ∼ g` of functions in the [identity type handout](identity-type.lagda.md).
The principle of function extensionality says that pointwise equal functions are equal and is given by the following type `FunExt`:
```agda
FunExt = {A : Type} {B : A → Type} {f g : (x : A) → B x} → f ∼ g → f ≡ g
```
Unfortunately, this principle is not provable or disprovable in Agda or MLTT (we say that it is [independent](https://en.wikipedia.org/wiki/Independence_(mathematical_logic))).
But it is provable in [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html), which is based on Cubical Type Theory and is outside the scope of these lecture notes. Sometimes we will use function extensionality as an explicit assumption.

# Week 3

## Finite types

We now define a type `Fin n` which has exactly `n` elements, where `n : ℕ` is a natural number.

```agda
data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)
```
Examples:
```agda
private
 x₀ x₁ x₂ : Fin 3
 x₀ = zero
 x₁ = suc zero
 x₂ = suc (suc zero)

 y₀ y₁ y₂ : Fin 3
 y₀ = zero {2}
 y₁ = suc {2} (zero {1})
 y₂ = suc {2} (suc {1} (zero {0}))
```
And these are all the elements of `Fin 3`. Notice that `Fin 0` is empty:
```agda
Fin-0-is-empty : is-empty (Fin 0)
Fin-0-is-empty = {!!}
```
Here `()` is a pseudo-pattern that tells that there is no constructor for the type.
```agda
Fin-suc-is-nonempty : {n : ℕ} → ¬ is-empty (Fin (suc n))
Fin-suc-is-nonempty = {!!}
```

### Elimination principle

```agda
Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim = {!!}
```
So this again looks like [primitive recursion](natural-numbers-type.lagda.md). And it gives an induction principle for `Fin`.

### Every element of `Fin n` can be regarded as an element of `ℕ`

```agda
ι : {n : ℕ} → Fin n → ℕ
ι = {!!}
```

## Propositions as types versus propositions as booleans

When programming in Haskell, and indeed in C or Java or Python, etc., we use *booleans* rather than *types* to encode logical propositions.

We now discuss *why* we use *types* to encode logical propositions, and
*when* we can use *booleans* instead. It is not always.  It is here
that the prerequisite *Theories of Computation* shows up.

### Discussion and motivation

In Haskell, we have a function `(==) : Eq a => a -> a -> Bool`. The type constraint `Eq a` is a prerequisite for this function because not all types have decidable equality. What does this mean? It means that, in general, there is no algorithm to decide whether the elements of a type are equal or not.

**Examples.** We *can check* equality of booleans, integers, strings and much more.

**Counter-example.** We *can't check* equality of functions of type `ℕ → ℕ`, for instance. Intuitively, to check that two functions `f` and `g` of this type are equal, we need to check infinitely many cases, namely `f x = g x` for all `x : ℕ`. But, we are afraid, intuition is not enough. This has to be proved. Luckily in our case, [Alan Turing](https://en.wikipedia.org/wiki/Alan_Turing) provided the basis to prove that. He showed that the [Halting Problem](https://en.wikipedia.org/wiki/Halting_problem) can't be solved by an algorithm in any programming language. It follows from this that we can't check whether two such functions `f` and `g` are equal or not using an algorithm.

The above examples and counter-examples show that sometimes we can decide equality with an algorithm, and sometimes we can't. However, for example, the identity type `_≡_` applies to *all* types, whether they have decidable equality or not, and this is why it is useful. We can think about equality, not only in our heads but also in Agda, without worrying whether it can be *checked* to be true or not by a computer. The identity type is not about *checking* equality. It is about asserting that two things are equal, and then proving this ourselves. In fact, equality is very often not checkable by the computer. It is instead about *stating* and *proving* or *disproving* equalities, where the proving and disproving is done by people (the lecturers and the students in this case), by hard, intelligent work.

### Decidable propositions

Motivated by the above discussion, we define when a logical proposition is decidable under the understanding of propositions as types:
```agda
is-decidable : Type → Type
is-decidable A = A ∔ ¬ A
```
This means that we can produce an element of `A` or show that no such element can be found.

Although it is not possible in general to write a program of type `¬¬ A → A`, this is possible when `A` is decidable:
```agda
¬¬-elim : {A : Type} → is-decidable A → ¬¬ A → A
¬¬-elim = {!!}
```

### Decidable propositions as booleans

The following shows that a type `A` is decidable if and only if there is `b : Bool` such that `A` holds if and only if the boolean `b` is `true`.

For the purposes of this handout, understanding the following proof is not important at a first reading. What is important is to understand *what* the type of the following function is saying, which is what we explained above.
```agda
decidability-with-booleans : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
decidability-with-booleans = {!!}
```

### Decidable predicates as boolean-valued functions

Consider the logical statement "x is even". This is decidable, because
there is an easy algorithm that tells whether a natural number `x` is
even or not. In programming languages we write this algorithm as a
procedure that returns a boolean. But an equally valid definition is to say that `x` is even if there is a natural number `y` such that `x = 2 * y`. This definition doesn't automatically give an algorithm to check whether or not `x` is odd.
<!--
```agda
module _ where
 private
```
-->
```agda
  is-even : ℕ → Type
  is-even = {!!}
```
This says what to be even *means*. But it doesn't say how we *check* with a computer program whether a number is even or not, which would be given by a function `check-even : ℕ → Bool`.
```agda
  check-even : ℕ → Bool
  check-even = {!!}
```

For this function to be correct, it has to be the case that

 > `is-even x ⇔ check-even x ≡ true`

**Exercise.** We believe you have learned enough Agda, try this.

This is possible because

 > `(x : X) → is-decidable (is-even x)`.

The following generalizes the above discussion and implements it in Agda.

First we define what it means for a predicate, such as `A = is-even`, to be decidable:
```agda
is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

```
In our example, this means that we can tell whether a number is even or not.

Next we show that a predicate `A` is decidable if and only if there is a boolean valued function `α` such that `A x` holds if and only if `α x ≡ true`. In the above example, `A` plays the role of `is-even` and `alpha` plays the role of `check-even`.

Again, what is important at a first reading of this handout is not to understand the proof but what the type of the function is saying. But we will discuss the proof in lectures.

```agda
predicate-decidability-with-booleans : {X : Type} (A : X → Type)
                                     → is-decidable-predicate A
                                     ⇔ Σ α ꞉ (X → Bool) , ((x : X) → A x ⇔ α x ≡ true)
predicate-decidability-with-booleans = {!!}
```

Although boolean-valued predicates are fine, we prefer to use type-valued predicates for the sake of uniformity, because we can always define type valued predicates, but only on special circumstances can we define boolean-valued predicates. It is better to define all predicates in the same way, and then write Agda code for predicates that happen to be decidable.

### Preservation of decidability

If `A` and `B` are logically equivalent, then `A` is decidable if and only if `B` is decidable. We first prove one direction.
```agda
map-decidable : {A B : Type} → (A → B) → (B → A) → is-decidable A → is-decidable B
map-decidable = {!!}

map-decidable-corollary : {A B : Type} → (A ⇔ B) → (is-decidable A ⇔ is-decidable B)
map-decidable-corollary = {!!}
```
Variation:
```agda
map-decidable' : {A B : Type} → (A → ¬ B) → (¬ A → B) → is-decidable A → is-decidable B
map-decidable' = {!!}
map-decidable' = {!!}
```

```agda
pointed-types-are-decidable : {A : Type} → A → is-decidable A
pointed-types-are-decidable = {!!}

empty-types-are-decidable : {A : Type} → ¬ A → is-decidable A
empty-types-are-decidable = {!!}

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = {!!}

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = {!!}

∔-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A ∔ B)
∔-preserves-decidability = {!!}

×-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A × B)
×-preserves-decidability = {!!}

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

### Decidable equality

A particular case of interest regarding the above discussion is the notion of a type having decidable equality, which can be written in Agda as follows.

```agda
has-decidable-equality : Type → Type
has-decidable-equality X = (x y : X) → is-decidable (x ≡ y)
```
**Exercise.** Show, in Agda, that a type `X` has decidable equality if and only if there is a function `X → X → Bool` that checks whether two elements of `X` are equal or not.

Some examples:
```agda
Bool-has-decidable-equality : has-decidable-equality Bool
Bool-has-decidable-equality = {!!}

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality = {!!}
```

### Equality of functions

As discussed above, it is not possible to decide whether or not we have `f ∼ g` for two functions `f` and `g`, for example of type `ℕ → ℕ`. However, sometimes we can *prove* or *disprove* this. Here are some examples:

```agda
module _ where
 private

  f g h : ℕ → ℕ

  f x = x

  g 0       = 0
  g (suc x) = suc (g x)

  h x = suc x

  f-equals-g : f ∼ g
  f-equals-g = {!!}

  f-not-equals-h : ¬ (f ∼ h)
  f-not-equals-h = {!!}
```

### Exhaustively searchable types (Harder!)

We will explain in a future lecture why we need to use `Type₁` rather than `Type` in the following definition. For the moment we just mention that because the definition mentions `Type`, there would be a circularity if the type of the definition where again `Type`. Such circular definitions are not allowed because if they were then we would be able to prove that `0=1`. We have that `Type : Type₁` (the type of `Type` is `Type₁`) but we can't have `Type : Type`.
```agda
is-exhaustively-searchable : Type → Type₁
is-exhaustively-searchable X = (A : X → Type)
                             → is-decidable-predicate A
                             → is-decidable (Σ x ꞉ X , A x)
```
**Exercise**. Show, in Agda, that the types `𝟘`, `𝟙` , `Bool` and  `Fin n`, for any `n : ℕ`, are exhaustively searchable. The idea is that we check whether or not `A x` holds for each `x : A`, and if we find at least one, we conclude that `Σ x ꞉ X , A x`, and otherwise we conclude that `¬ (Σ x ꞉ X , A x)`. This is possible because these types are finite.
```agda
𝟘-is-exhaustively-searchable : {!!}
𝟘-is-exhaustively-searchable = {!!}

𝟙-is-exhaustively-searchable : {!!}
𝟙-is-exhaustively-searchable = {!!}

Bool-is-exhaustively-searchable : {!!}
Bool-is-exhaustively-searchable = {!!}

Fin-is-exhaustively-searchable : {!!}
Fin-is-exhaustively-searchable = {!!}
```

**Exercise**. Think why there can't be any program of type `is-exhaustively-searchable ℕ`, by reduction to the Halting Problem. No Agda code is asked in this question. In fact, the question is asking you to think why such Agda code can't exist. This is very different from proving, in Agda, that `¬ is-exhaustively-searchable ℕ`. Interestingly, this is also not provable in Agda, but explaining why this is the case is beyond the scope of this module. In any case, this is an example of a statement `A` such that neither `A` nor `¬ A` are provable in Agda. Such statements are called *independent*. It must be remarked that the reason why there isn't an Agda program of type `is-exhaustively-searchable ℕ` is *not* merely that `ℕ` is infinite, because there are, perhaps surprisingly, infinite types `A` such that a program of type `is-exhastively-searchable A` can be coded in Agda. One really does an argument such as reduction to the Halting Problem to show that there is no program that can exaustively search the set `ℕ` of natural numbers.

```agda
Π-exhaustibility : (X : Type)
                 → is-exhaustively-searchable X
                 → (A : X → Type)
                 → is-decidable-predicate A
                 → is-decidable (Π x ꞉ X , A x)
Π-exhaustibility = {!!}
```
**Exercises.** If two types `A` and `B` are exhaustively searchable types, then so are the types `A × B` and `A + B`. Moreover, if `X` is an exhaustively searchable type and `A : X → Type` is a family of types, and the type `A x` is exhaustively searchable for each `x : X`, then the type `Σ x ꞉ X , A x` is exhaustively searchable.
```agda
×-is-exhaustively-searchable : {!!}
×-is-exhaustively-searchable = {!!}

∔-is-exhaustively-searchable : {!!}
∔-is-exhaustively-searchable = {!!}

Σ-is-exhaustively-searchable : {!!}
Σ-is-exhaustively-searchable = {!!}
```

## Natural numbers functions, relations and properties

### Some general properties

```agda
suc-is-not-zero : {x : ℕ} → suc x ≢ 0
suc-is-not-zero = {!!}

zero-is-not-suc : {x : ℕ} → 0 ≢ suc x
zero-is-not-suc = {!!}

pred : ℕ → ℕ
pred 0       = 0
pred (suc n) = n

suc-is-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-is-injective = {!!}
```

### Order relation _≤_

The less-than order on natural numbers can be defined in a number of
equivalent ways. The first one says that `x ≤ y` iff `x + z ≡ y` for
some `z`:
```agda
_≤₀_ : ℕ → ℕ → Type
x ≤₀ y = Σ a ꞉ ℕ , x + a ≡ y
```
The second one is defined by recursion:
```agda
_≤₁_ : ℕ → ℕ → Type
0     ≤₁ y     = 𝟙
suc x ≤₁ 0     = 𝟘
suc x ≤₁ suc y = x ≤₁ y
```
The third one, which we will as the official one, is defined *by induction* using `data`:
```agda
data _≤_ : ℕ → ℕ → Type where
 0-smallest      : {y : ℕ} → 0 ≤ y
 suc-preserves-≤ : {x y : ℕ} → x ≤ y → suc x ≤ suc y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

infix 0 _≤_
infix 0 _≥_
```

We will now show some properties of these relations.
```agda
suc-reflects-≤ : {x y : ℕ} → suc x ≤ suc y → x ≤ y
suc-reflects-≤ = {!!}

suc-preserves-≤₀ : {x y : ℕ} → x ≤₀ y → suc x ≤₀ suc y
suc-preserves-≤₀ = {!!}

≤₀-implies-≤₁ : {x y : ℕ} → x ≤₀ y → x ≤₁ y
≤₀-implies-≤₁ = {!!}

≤₁-implies-≤ : {x y : ℕ} → x ≤₁ y → x ≤ y
≤₁-implies-≤ = {!!}

≤-implies-≤₀ : {x y : ℕ} → x ≤ y → x ≤₀ y
≤-implies-≤₀ = {!!}
```

### Exponential function

```agda
_^_ : ℕ → ℕ → ℕ
_^_ = {!!}

infix 40 _^_
```

### Maximum and minimum

```agda
max : ℕ → ℕ → ℕ
max = {!!}

min : ℕ → ℕ → ℕ
min = {!!}
```

### No natural number is its own successo

We now show that there is no natural number `x` such that `x = suc x`.
```agda
every-number-is-not-its-own-successor : (x : ℕ) → x ≢ suc x
every-number-is-not-its-own-successor = {!!}

there-is-no-number-which-is-its-own-successor : ¬ (Σ x ꞉ ℕ , x ≡ suc x)
there-is-no-number-which-is-its-own-successor = {!!}
```

### Prime numbers

```agda
is-prime : ℕ → Type
is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) ∔ (x ≡ n))
```
**Exercise.** Show that `is-prime n` is [decidable](decidability.lagda.md) for every `n : ℕ`. Hard.

```agda
is-prime-decidable : {!!}
is-prime-decidable = {!!}
```

The following is a conjecture that so far mathematicians haven't been able to prove or disprove. But we can still say what the conjecture is in Agda:
```agda
twin-prime-conjecture : Type
twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                          × is-prime p
                                          × is-prime (p + 2)
```

### Properties of addition

```agda
+-base : (x : ℕ) → x + 0 ≡ x
+-base = {!!}

+-step : (x y : ℕ) → x + suc y ≡ suc (x + y)
+-step = {!!}

+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm = {!!}
```

### Associativity of addition

```agda
+-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc = {!!}
```

### 1 is a neutral element of multiplication

```agda
1-*-left-neutral : (x : ℕ) → 1 * x ≡ x
1-*-left-neutral = {!!}

1-*-right-neutral : (x : ℕ) → x * 1 ≡ x
1-*-right-neutral = {!!}
```

### Multiplication distributes over addition:

```agda
*-+-distrib : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*-+-distrib = {!!}
```

### Commutativity of multiplication

```agda
*-base : (x : ℕ) → x * 0 ≡ 0
*-base = {!!}

*-comm : (x y : ℕ) → x * y ≡ y * x
*-comm = {!!}
```

### Associativity of multiplication

```agda
*-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*-assoc = {!!}
```

### Even and odd numbers

```agda
is-even is-odd : ℕ → Type
is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
is-odd  x = Σ y ꞉ ℕ , x ≡ 1 + 2 * y

zero-is-even : is-even 0
zero-is-even = {!!}

ten-is-even : is-even 10
ten-is-even = {!!}

zero-is-not-odd : ¬ is-odd 0
zero-is-not-odd = {!!}

one-is-not-even : ¬ is-even 1
one-is-not-even = {!!}

one-is-not-even' : ¬ is-even 1
one-is-not-even' = {!!}

one-is-odd : is-odd 1
one-is-odd = {!!}

even-gives-odd-suc : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc = {!!}

even-gives-odd-suc' : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc' = {!!}

odd-gives-even-suc : (x : ℕ) → is-odd x → is-even (suc x)
odd-gives-even-suc = {!!}

even-or-odd : (x : ℕ) → is-even x ∔ is-odd x
even-or-odd = {!!}
```

```agda
even : ℕ → Bool
even 0       = true
even (suc x) = not (even x)

even-true  : (y : ℕ)  → even (2 * y) ≡ true
even-true = {!!}

even-false : (y : ℕ) → even (1 + 2 * y) ≡ false
even-false = {!!}

div-by-2 : ℕ → ℕ
div-by-2 x = f (even-or-odd x)
 where
  f : is-even x ∔ is-odd x → ℕ
  f (inl (y , _)) = y
  f (inr (y , _)) = y

remainder-div-by-2 : ℕ → ℕ
remainder-div-by-2 x = f (even-or-odd x)
 where
  f : is-even x ∔ is-odd x → ℕ
  f (inl (y , _)) = 0
  f (inr (y , _)) = 1
```

*Exercise.* `(n : ℕ) → 2 * div-by-2 n + remainder-div-by-2 n ≡ n`.
This is hard. You will need to prove a number of auxiliary results (lemmas).
```agda
even-odd-lemma : (y z : ℕ) →  1 + 2 * y ≡ 2 * z → 𝟘
even-odd-lemma = {!!}

not-both-even-and-odd : (x : ℕ) → ¬ (is-even x × is-odd x)
not-both-even-and-odd = {!!}

double : ℕ → ℕ
double 0 = 0
double (suc x) = suc (suc (double x))

double-correct : (x : ℕ) → double x ≡ x + x
double-correct = {!!}

div-plus-remainder-equals-original : {!!}
div-plus-remainder-equals-original = {!!}
```

# Week 4


## Type isomorphisms

A function `f : A → B` is called a *bijection* if there is a function `g : B → A` in the opposite direction such that `g ∘ f ∼ id` and `f ∘ g ∼ id`. Recall that `_∼_` is [pointwise equality](identity-type.lagda.md) and that `id` is the [identity function](products.lagda.md). This means that we can convert back and forth between the types `A` and `B` landing at the same element with started with, either from `A` or from `B`. In this case, we say that the types `A` and `B` are *isomorphic*, and we write `A ≅ B`. Bijections are also called type *isomorphisms*. We can define these concepts in Agda using [sum types](sums.lagda.md) or [records](https://agda.readthedocs.io/en/latest/language/record-types.html). We will adopt the latter, but we include both definitions for the sake of illustration. Recall that we [defined](general-notation.lagda.md) the domain of a function `f : A → B` to be `A` and its codomain to be `B`.

Here we apply the proposition-as-types interpretation of logic to define the concepts:
<!--
```agda
module _ where
 private
```
-->
```agda
  is-bijection : {A B : Type} → (A → B) → Type
  is-bijection f = Σ g ꞉ (codomain f → domain f) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

  _≅_ : Type → Type → Type
  A ≅ B = Σ f ꞉ (A → B) , is-bijection f
```
And here we give an equivalent definition which uses records and is usually more convenient in practice and is the one we adopt:
```agda
record is-bijection {A B : Type} (f : A → B) : Type where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_
```
The definition with `Σ` is probably more intuitive, but, as discussed above, the definition with a record is often easier to work with, because we can easily extract the components of the definitions using the names of the fields. It also often allows Agda to infer more types, and to give us more sensible goals in the interactive development of Agda programs and proofs.

Notice that `inverse` plays the role of `g`. The reason we use `inverse` is that then we can use the word `inverse` to extract the inverse of a bijection. Similarly we use `bijection` for `f`, as we can use the word `bijection` to extract the bijection from a record.

### Some basic examples

```agda

Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = {!!}
```
But there is also a different isomorphism:
```agda
-- Try giving a different isomorphism from the one above
Bool-𝟚-isomorphism' : Bool ≅ 𝟚
Bool-𝟚-isomorphism' = {!!}
```
And these are the only two isomorphisms (you could try to prove this in Agda as a rather advanced exercise). More advanced examples are in other files.

## Some constructions with isomorphisms

```agda
≃-refl : (X : Type) → X ≅ X
≃-refl = {!!}

≅-sym : {X Y : Type} → X ≅ Y → Y ≅ X
≅-sym = {!!}

≅-trans : {X Y Z : Type} → X ≅ Y → Y ≅ Z → X ≅ Z
≅-trans = {!!}
```

Notation for chains of isomorphisms (like chains of equalities):

```agda
_≃⟨_⟩_ : (X {Y} {Z} : Type) → X ≅ Y → Y ≅ Z → X ≅ Z
_ ≃⟨ d ⟩ e = ≅-trans d e

_■ : (X : Type) → X ≅ X
_■ = ≃-refl

```

## The booleans

The booleans are isomorphic to a Basic MLTT type:

```agda
Bool-isomorphism : Bool ≅ 𝟙 ∔ 𝟙
Bool-isomorphism = {!!}
```

## The `Maybe` type constructor

```agda

data Maybe (X : Type) : Type where
  nothing : Maybe X
  just    : X → Maybe X
```

### Elimination principle

```agda
Maybe-elim : {X : Type} (A : Maybe X → Type)
           → A nothing
           → ((x : X) → A (just x))
           → (m : Maybe X) → A m
Maybe-elim = {!!}
```
In terms of functional programming, this says that using an element `a : A nothing` and a dependent function `f : (x : X) → A (just x)`, we can define a dependent function of type `(m : Maybe X) → A m`, by cases on whether `m` is `nothing` or `just x`.

In terms of logic, the elimination principle says that in order to prove that "for all `m : Maybe X`, the proposition `A m` holds" it is enough to prove that `A nothing` holds and that for all `x : X`, the proposition `A (just x)` holds.

### Non-dependent version

It is a special case of the dependent version:
```agda
Maybe-nondep-elim : {X A : Type}
                  → A
                  → (X → A)
                  → Maybe X → A
Maybe-nondep-elim = {!!}
```

### Isomorphism with a Basic MLTT type

We now show that there is an [isomorphism](isomorphisms.lagda.md) of the type `Maybe X` with a type in basic Martin-Löf Type Theory, so that, strictly speaking, we don't need to include `Maybe` in our repertoire of Agda definitions. Nevertheless, in practice, it is convenient to include it.
```agda

Maybe-isomorphism : (X : Type) → Maybe X ≅ 𝟙 ∔ X
Maybe-isomorphism X = {!!}
```

### The monad structure and laws

We will define later, in Agda, what a monad is. But before knowing what a monad is, it is possible to define the monad structure. We do this using the non-dependent eliminator. We define this within a submodule. Note that the things within the submodule must be indented.
```agda
module Maybe-Monad where

 return : {X : Type} → X → Maybe X
 return = {!!}

 extend : {X Y : Type} → (X → Maybe Y) → Maybe X → Maybe Y
 extend = {!!}

 _>>=_ : {X Y : Type} → Maybe X → (X → Maybe Y) → Maybe Y
 _>>=_ = {!!}
```
As we will see later, the monad structure consists of `return` and `>>=`. Another way to present a monad is with `return`, `map` and `join`:
```agda

 map : {X Y : Type} → (X → Y) → Maybe X → Maybe Y
 map = {!!}

 join : {X : Type} → Maybe (Maybe X) → Maybe X
 join = {!!}
```
Here `∘` is function composition and `id` is the identity function.

The following function is useful when making monadic computations with `Maybe`:
```agda
 _orElse_ : {A : Type} → Maybe A → Maybe A → Maybe A
 _orElse_ = {!!}
```

Here are some facts about these functions, which could have been used as definitions by pattern matching, if we wished:
```agda
 extend-nothing : {X Y : Type} (f : X → Maybe Y) → extend f nothing ≡ nothing
 extend-nothing = {!!}

 extend-just : {X Y : Type} (f : X → Maybe Y) (x : X) → extend f (just x) ≡ f x
 extend-just = {!!}

 map-nothing : {X Y : Type} (f : X → Y) → map f nothing ≡ nothing
 map-nothing = {!!}

 map-just : {X Y : Type} (f : X → Y) (x : X) → map f (just x) ≡ just (f x)
 map-just = {!!}

 join-nothing : {X : Type} → join nothing ≡ nothing {X}
 join-nothing = {!!}

 join-just : {X : Type} (m : Maybe X) → join (just m) ≡ m
 join-just = {!!}
```
Notice that we wrote `nothing {X}` because Agda can't infer, in this case, which type we meant for `nothing`.

If we had defined `map` and `join` first, we could have defined `extend` from them using the following fact:
```agda
 >>=-in-terms-of-map-and-join : {X Y : Type} (f : X → Maybe Y) (m : Maybe X)
                              →  m >>= f ≡ join (map f m)
 >>=-in-terms-of-map-and-join = {!!}
```

We can also prove the monad laws before we know what a monad is:
```agda
 left-identity : {X Y : Type} (f : X → Maybe X) (x : X) → return x >>= f ≡ f x
 left-identity = {!!}

 right-identity : {X : Type} (m : Maybe X) → m >>= return ≡ m
 right-identity = {!!}

 associativity : {X Y Z : Type} (f : X → Maybe Y) (g : Y → Maybe Z) (m : Maybe X)
               → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
 associativity = {!!}
```
The monad laws can be alternatively expressed in terms of `return`, `map` and `join`.
This is the end of the submodule. Agda uses indentation to know this.

## Lists

This type has already been briefly discussed in the introduction.
```agda
data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_
```

### Elimination principle

```agda
List-elim : {X : Type} (A : List X → Type)
          → A []
          → ((x : X) (xs : List X) → A xs → A (x :: xs))
          → (xs : List X) → A xs
List-elim = {!!}
```
Notice that the definition of `h` is the same as that of the usual `fold` function for lists, but the type is more general. In fact, the `fold` function is just the non-dependent version of the eliminator
```agda
List-nondep-elim : {X A : Type}
                 → A
                 → (X → List X → A → A)
                 → List X → A
List-nondep-elim = {!!}
```

## Some functions on lists

### Length, concatenation, map and singleton lists

```agda
length : {A : Type} → List A → ℕ
length = {!!}

_++_ : {A : Type} → List A → List A → List A
_++_ = {!!}

infixr 20 _++_

map : {A B : Type} → (A → B) → List A → List B
map = {!!}

[_] : {A : Type} → A → List A
[_] = {!!}
```

### Properties of list concatenation

```agda
[]-left-neutral : {X : Type} (xs : List X) → [] ++ xs ≡ xs
[]-left-neutral = {!!}

[]-right-neutral : {X : Type} (xs : List X) → xs ++ [] ≡ xs
[]-right-neutral = {!!}

++-assoc : {A : Type} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc = {!!}
```

### List reversal

First an obvious, but slow reversal algorithm:
```agda
reverse : {A : Type} → List A → List A
reverse = {!!}
```
This is quadratic time. To get a linear-time algorithm, we use the following auxiliary function:
```agda
rev-append : {A : Type} → List A → List A → List A
rev-append = {!!}
```
The intended behaviour of `rev-append` is that `rev-append xs ys = reverse xs ++ ys`.
Using this fact, the linear time algorithm is the following:
```agda
rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```
We now want to show that `rev` and `reverse` behave in the same way. To do this, we first show that the auxiliary function does behave as intended:
```agda
rev-append-behaviour : {A : Type} (xs ys : List A)
                     → rev-append xs ys ≡ reverse xs ++ ys
rev-append-behaviour = {!!}
```
We state this as follows in Agda:
```agda
rev-correct : {A : Type} (xs : List A) → rev xs ≡ reverse xs
rev-correct = {!!}
```

## Vectors

This type has already been briefly discussed in the [introduction](introduction.lagda.md).
```agda
data Vector (A : Type) : ℕ → Type where
 []   : Vector A 0
 _::_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

```

### Elimination principle

```agda
Vector-elim : {X : Type} (A : (n : ℕ) → Vector X n → Type)
            → A 0 []
            → ((x : X) (n : ℕ) (xs : Vector X n) → A n xs → A (suc n) (x :: xs))
            → (n : ℕ) (xs : Vector X n) → A n xs
Vector-elim = {!!}
```
It is better, in practice, to make the parameter `n` implicit, because it can be inferred from the type of `xs`, and so we get less clutter:
```agda
Vector-elim' : {X : Type} (A : {n : ℕ} → Vector X n → Type)
             → A []
             → ((x : X) {n : ℕ} (xs : Vector X n) → A xs → A (x :: xs))
             → {n : ℕ} (xs : Vector X n) → A xs
Vector-elim' = {!!}
```
Again, the non-dependent version gives a fold function for vectors:
```agda
Vector-nondep-elim' : {X A : Type}
                    → A
                    → (X → {n : ℕ} → Vector X n → A → A)
                    → {n : ℕ} → Vector X n → A
Vector-nondep-elim' = {!!}
```

## Some functions on vectors

As mentioned in the [introduction](introduction.lagda.md), vectors allow us to have safe `head` and `tail` functions.
```agda
head : {A : Type} {n : ℕ} → Vector A (suc n) → A
head = {!!}

tail : {A : Type} {n : ℕ} → Vector A (suc n) → Vector A n
tail = {!!}
```

We can also define a safe indexing function on vectors using [finite types](Fin.lagda.md) as follows.
```agda

_!!_ : ∀ {X n} → Vector X n → Fin n → X
_!!_ = {!!}
```
Alternatively, this can be defined as follows:
```agda
_!!'_ : {X : Type} {n : ℕ} → Vector X n → Fin n → X
_!!'_ = {!!}
```

We can also do vector concatenation:
```agda
_++v_ : {X : Type} {m n : ℕ} → Vector X m → Vector X n → Vector X (m + n)
_++v_ = {!!}

infixr 20 _++v_
```

### Vectors represented as a Basic MLTT type

```agda

Vector' : Type → ℕ → Type
Vector' A 0       = 𝟙
Vector' A (suc n) = A × Vector' A n

[]' : {A : Type} → Vector' A 0
[]' = {!!}

_::'_ : {A : Type} {n : ℕ} → A → Vector' A n → Vector' A (suc n)
_::'_ = {!!}

infixr 10 _::'_

private
 example₂ : Vector' ℕ 3
 example₂ = {!!}

 example₃ : example₂ ≡ (1 , 2 , 3 , ⋆)
 example₃ = {!!}

Vector-iso : {A : Type} {n : ℕ} → Vector A n ≅ Vector' A n
Vector-iso = {!!}

private
 open _≅_
 open is-bijection

 example₄ : bijection Vector-iso (1 :: 2 :: 3 :: []) ≡ (1 , 2 , 3 , ⋆)
 example₄ = {!!}

 example₅ : Vector ℕ 3
 example₅ = {!!}

 example₆ : example₅ ≡ 1 :: 2 :: 3 :: []
 example₆ = {!!}
```

## Binary sums as a special case of arbitrary sums

Using the binary type `𝟚`, binary sums can be seen as a special case of arbitrary sums as follows:
```agda
_∔'_ : Type → Type → Type
A₀ ∔' A₁ = Σ n ꞉ 𝟚 , A n
 where
  A : 𝟚 → Type
  A 𝟎 = A₀
  A 𝟏 = A₁
```

To justify this claim, we establish an isomorphism.
```agda
binary-sum-isomorphism : (A₀ A₁ : Type) → A₀ ∔ A₁ ≅ A₀ ∔' A₁
binary-sum-isomorphism = {!!}
```

## Binary products as a special case of arbitrary products

Using the [binary type](binary-type.lagda.md) `𝟚`, binary products can be seen as a special case of arbitrary products as follows:
```agda
_×'_ : Type → Type → Type
A₀ ×' A₁ = Π n ꞉ 𝟚 , A n
 where
  A : 𝟚 → Type
  A 𝟎 = A₀
  A 𝟏 = A₁

infixr 2 _×'_
```
We could have written the type `Π n ꞉ 𝟚 , A n` as simply `(n : 𝟚) → A n`, but we wanted to emphasize that binary products `_×_` are special cases of arbitrary products `Π`.

To justify this claim, we establish an [isomorphism](isomorphisms.lagda.md). But we need to assume [function extensionality](function-extensionality.lagda.md) for this purpose.
```agda
binary-product-isomorphism : FunExt → (A₀ A₁ : Type) → A₀ × A₁ ≅ A₀ ×' A₁
binary-product-isomorphism = {!!}
```
Notice that the above argument, in Agda, not only *shows* that the types are indeed isomorphic, but also explains *how* and *why* they are isomorphic. Thus, logical arguments coded in Agda are useful not only to get confidence in correctness, but also to gain understanding.

## Vector and list isomorphisms

We will do this handout in the lab. We will solve some of the problems, and you will solve the remaining ones.

### The type of lists can be defined from that of vectors

```agda
lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors = {!!}
```

### The type of vectors can be defined from that of lists

```agda

vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ (Σ xs ꞉ List A , (length xs ≡ n))
vectors-from-lists = {!!}
```

### The types of lists can be defined in basic MLTT

```agda
List' : Type → Type
List' X = Σ n ꞉ ℕ , Vector' X n

lists-in-basic-MLTT : {A : Type} → List A ≅ List' A
lists-in-basic-MLTT = {!!}
```

## Isomorphism of Fin n with a Basic MLTT type

```agda
Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = {!!}

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = {!!}

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism = {!!}
```

**Exercise.** Show that the type `Fin n` is isormorphic to the type `Σ k : ℕ , k < n`.

```agda
Fin-in-basic-MLTT : {!!}
Fin-in-basic-MLTT = {!!}
```
