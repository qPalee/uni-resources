# Lecture Notes - Week 2

Todd Waugh Ambridge, 28-29 January 2025.

```
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week2 where

open import general-notation
```

# Week 1 Recap

We installed Agda, and started defining types and functions using it.

Agda already has builtin types for functions, and a type of types...
called `Type`.

Other than that, we defined our own types inductively!

So which types did we introduce to our type system so far?

```
open import unit-type hiding (𝟙-elim;𝟙-nondep-elim)
open import empty-type hiding (¬_;𝟘-elim;𝟘-nondep-elim)
open import binary-type
open import natural-numbers-type hiding (_+_;ℕ-elim;ℕ-nondep-elim)
open import Bool hiding (Bool-elim;Bool-nondep-elim;if_then_else_)
open import List
open import products
```

So far, we've mostly introduced types for *data*, such as numbers,
lists, etc. However, you began with Martín to introduce types for logic
instead: functions `→` correspond to logical implication `→`, while
products `Π` (dependent functions) correspond to for-all
quantification `∀`.

This week, we will continue to abolish logic and replace it with
programming: logical *propositions* will become *types*.

# Week 2 Lab Recap

In the Week 2 lab, we introduced the identity type `≡`, which
corresponds to the logical concept of equality `=`.

```
data _≡_ {X : Type} : X → X → Type where
 refl : (x : X) → x ≡ x

infix 0 _≡_
```

This says that for every type `X` and each pair of elements `x,y : X`
there is a *type* called `x ≡ y : Type`.

Intuitively, this type will have an element if we can show that `x` and
`y` are indeed equal.

## Constructing terms of identity types

The identity type has only one constructor, `refl`, which says that
every type `x ≡ x` has an element (i.e. we simply show that `x` and `x`
are equal by definition).

```
5-equals-5 : 5 ≡ 5
5-equals-5 = refl 5
```

But we can combine this constructor with the equational rules we've
defined in functions. When you write `f x = y` in Agda, you are telling
Agda that `f x` and `y` are the same *definitionally*: they are
literally two names for the same mathematical object.

For example, the `_+_` function defines the following equational rules:

```
_+_ : ℕ → ℕ → ℕ
0     + y = y           -- Let's call this 'Rule +-base'
suc x + y = suc (x + y) -- Let's call this 'Rule +-induction'
```

Agda can then apply these rules whenever it sees these patterns.

For example, it will be able to identify that:

  2 + 3
= suc (suc zero) + 3               -- Using {-# BUILTIN NATURAL ℕ #-}
= suc (suc zero  + 3)              -- By Rule +-induction,
= suc (suc (zero + 3))             -- By Rule +-induction,
= suc (suc 3))                     -- By Rule +-base,
= suc (suc (suc (suc (suc zero)))) -- Using {-# BUILTIN NATURAL ℕ #-}
= 5                                -- Using {-# BUILTIN NATURAL ℕ #-}

Therefore, `2 + 3 = 5` *definitionally* in Agda, which means they're
automatically equal as *terms of type `ℕ`*.

```
5-equals-2+3 : 5 ≡ 2 + 3
5-equals-2+3 = refl 5
```

Note that in the above, when we perform `C-c C-,`, Agda performs the
six definitional rules above automatically to simplify the goal.

## Pattern matching on terms of identity types

We then learned that if we have an element `p : x ≡ y` as an argument
to a function/proof, we can pattern match on it in the same way as
elements of any other inductively-defined type!

```
trans : {X : Type} (x y z : X) → x ≡ y → y ≡ z → x ≡ z
trans x x x (refl x) (refl x) = refl x
```

When we pattern patch on `p : x ≡ y`, Agda recognises that the only
pattern is `refl x` -- therefore, `p = refl x`, meaning that
`p : x ≡ x`. Because both `p : x ≡ y` and `p : x ≡ x`, `x` and `y` must
in fact be defintionally the same object!

They are then completely aligned in the type system, and can be used
interchangeably. That's why the definition of `trans` looks so strange:
the goal to prove `x ≡ z` ultimately becomes a goal to prove `x ≡ x`...
which is easy! It's just `refl x`!

## Elimination rules

When we define a type using `data`, we define that type's introduction
rules. By pattern matching, we use the type's elimination rules.

For example, we can define the length function on lists by pattern
matching:

```
length : {A : Type} → List A → ℕ
length [] = 0
length (x :: xs) = suc (length xs)
```

But we can also define the elimination rule explicitly, and then define
length using that *without* pattern matching.

The elimination principle for lists says that to prove a proposition
`P xs : Type`, which depends on a list `xs : List X`, we have to
prove it for the empty list and for a list `(x :: xs) : List X` made
up of a head element `x : X` and a list `xs : List X` which itself
satisfies the proposition.

As we saw in the lab, this is called induction on lists:

```
List-induction : {X : Type}
               → (P : List X → Type)
               → P []
               → ((x : X) (xs : List X) → P xs → P (x :: xs))
               → (n : List X) → P n
List-induction {X} P p f = h
 where
  h : (xs : List X) → P xs
  h [] = p
  h (x :: xs) = f x xs (h xs)
```

We can define the non-dependent version of List induction as follows:
it says that to give an element of `A` for every list `xs : List X`, we
have to give one for the empty list and provide a function that allows
us to build elements from the constituent parts of the list, as well as
an accumulator. Note that this is just the `fold` function!

```
fold : {X A : Type} → A → (X → List X → A → A) → List X → A
fold {X} {A} a f = List-induction {X} (λ _ → A) a f
```

We can use this to define tail' *without* pattern matching:

```
length' : {X : Type} → List X → ℕ
length' xs = fold 0 (λ y ys acc → 1 + acc) xs
                   -- ^ xs = y :: ys
                   -- acc = length' ys
```

Now let's continue programming logic!

# Our logic of types thus far

First, let's think about the types we already have, what they mean in
logic, and define their elimination rules explicitly.

## Natural numbers type `ℕ`

The natural numbers simply represent all positive integers.

Recall the induction principle on natural numbers from Theories of
Computation and MLFCS:

```
ℕ-elim : {P : ℕ → Type}
       → P 0
       → ((k : ℕ) → P k → P (suc k))
       → (n : ℕ) → P n
ℕ-elim {P} a f = h
 where
  h : (n : ℕ) → P n
  h 0       = a
  h (suc n) = f n (h n)
```

The non-dependent version follows:

```
ℕ-nondep-elim : {A : Type}
              → A
              → (ℕ → A → A)
              → ℕ → A
ℕ-nondep-elim {A} = ℕ-elim {λ _ → A}
```

## Unit type `𝟙`

The unit type is used to represent truth. For example, if we wanted to
define the type of proofs that a given number is even, we could do
something like this:

```
is-even : ℕ → Type
is-even 0 = 𝟙
is-even 1 = 𝟘
is-even (suc (suc n)) = is-even n
```

Therefore, if the given number `n : ℕ` is indeed even, the type
`is-even n : Type` is inhabited, i.e. `⋆ : is-even n` because
`is-even n = 𝟙`.

```
2834-is-even : is-even 2834
2834-is-even = ⋆
```

We didn't have to use `𝟙` here, because any non-empty type could be
used to represent truth. But it makes sense to use `𝟙`, because we then
have at most *one* proof that a given number is even.

The elimination principle for `𝟙` follows:

```
𝟙-elim : {A : 𝟙 → Type}
       → A ⋆
       → (x : 𝟙) → A x
𝟙-elim a ⋆ = a
```

In logical terms, this says that in order to prove that a property `A`
of elements of the unit type `𝟙` holds for all elements of the type `𝟙`,
it is enough to prove that it holds for the element `⋆`.

Makes sense, right?

The non-dependent version says that if A holds, then "true implies A":

```agda
𝟙-nondep-elim : {A : Type}
              → A
              → 𝟙 → A
𝟙-nondep-elim {A} = 𝟙-elim {λ _ → A}
```

## Empty type `𝟘`

What does a type with zero elements correspond to logically?

If a given number `n : ℕ` is odd, then the type `is-even n : Type` is
empty, i.e. `is-even n = 𝟘`. Therefore, there are no proofs that `n` is
even!

So `𝟘` corresponds to falsity.

Now let's define the elimination principle:

```
𝟘-elim : {P : 𝟘 → Type} (x : 𝟘) → P x
𝟘-elim ()
```

In terms of logic, this says that in order to show that a property `P`
of elements of the empty type holds for all `x : 𝟘`, we have to do
nothing, because there is no element to check, and by doing nothing we
exhaust all possibilities.

This is called vacuous truth!

All unicorns in this room are wearing hats.

The non-dependent version says there is a function from the empty type
to any type:

```agda
𝟘-nondep-elim : {A : Type} → 𝟘 → A
𝟘-nondep-elim {A} = 𝟘-elim {λ _ → A}

if-false-then-283-is-even : 𝟘 → is-even 283
if-false-then-283-is-even = 𝟘-nondep-elim
```

## Two element types `𝟚` and `Bool` 

It may seem right to think of these types as representing truth values.
However, we are defining a *type-valued* logic, where (as discussed
above) `𝟙` corresponds to truth and `𝟘` to falsity.

We will look at Boolean-valued logic vs. Type-valued logic in a future
lecture. For now, let's define the elimination principles for one of
the above types (given that the types are equivalent).

```
Bool-elim : (A : Bool → Type)
          → A true
          → A false
          → (b : Bool) → A b
Bool-elim A x y true  = x
Bool-elim A x y false = y

Bool-nondep-elim : {A : Type}
                 → A
                 → A
                 → Bool → A
Bool-nondep-elim {A} = Bool-elim (λ _ → A)
```

Of course, the non-dependent version is just the `if-then-else`
function!

```
if_then_else_ : {A : Type} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f
```

# More logic via types -- And, Or and Not

Now, we would next like to define types that correspond to logical
conjunction (i.e. '_&&_'), disjunction (`_||_`), negation (`¬`) and
existence (`∃`).

## Disjunction

I want a proof of A || B. It could be:
 * A proof of A,
 * A proof of B.

```
data _∔_ (A B : Type) : Type where
 inl : A → A ∔ B
 inr : B → A ∔ B

infixr 20 _∔_

this-proof : is-even 9842 ∔ is-even 2
this-proof = inr ⋆
```

## Conjunction

I want a proof of A && B. It could be:
 * A pair of (a proof of A) and (a proof of B)

```
module data-× where
  data _×_ (A B : Type) : Type where
   _,_ : A → B → A × B

  infixr 2 _×_

  this-other-proof : is-even 9842 × is-even 2
  this-other-proof = ⋆ , ⋆
```

## Negation

I want a proof of ¬ A. It could be:
 * A proof that (a proof of A) leads to false

```
¬_ : Type → Type
¬ A = A → 𝟘

is-odd : ℕ → Type
is-odd n = ¬ is-even n

another-proof : is-odd 1
another-proof = 𝟘-nondep-elim
-- C-u C-u C-c C-,
```

# Existential quantification via types

Let's think about the following logical statement, which we call the

  Parity Theorem: `∀ n ꞉ ℕ , ∃ m ꞉ ℕ , (n ＝ 2m) ∨ (n ＝ 2m+1)`

What does the Parity Theorem say in English?

  "For every number n, there exists a number m such that either n is
  equal to 2m or n is equal to 2m+1."

Given a particular `n`, let's say `31`, how can we prove that there
does indeed exist such an `m`?

  We simply *give* that `m` along with a proof that `n` is equal to
  either `2m` or `2m+1`.

Therefore, a proof of existence `∃ x : X , P x` consists of two things:

  * A witness `x : X`,

  * A proof itself that `P x` holds (i.e., an element of `P x : Type`).

This is similar to a pair, except that the type of the second
projection changes based on the type of the first projection. These are
called *dependent pairs*, or *sums*.

```agda
module data-Σ where
 data Σ {A : Type } (B : A → Type) : Type  where
  _,_ : (x : A) (y : B x) → Σ {A} B

 fst : {A : Type} {B : A → Type} → Σ B → A
 fst (x , y) = x

 snd : {A : Type} {B : A → Type} → (z : Σ B) → B (fst z)
 snd (x , y) = y
```

However, for a number of reasons to be explained later, we prefer to
define it using a record definition:

```
open import sums hiding (Σ-elim;Σ-uncurry)
```

Let's now write the Parity Theorem in Agda.

Because it is a mathematical proposition, it will be represented as a
Type. We will build this type out of the types we've defined thus far
in our type-valued logic.

To recap:
 * The unit type `𝟙` corresponds to truth `⊤`, 
 * The empty type `𝟘` corresponds to falsity `⊥`,
 * Function types `X → Y` correspond to implication `X → Y`,
 * Negated types `¬ X` correspond to negation `¬ X`,
 * Binary product types `X × Y` correspond to conjunction `X && Y`,
 * Binary sum types `X ∔ Y` correspond to disjunction `X || Y`,
 * Dependent product types `(x : A) → B x`
   correspond to for-all quantification `∀ x : A , B x`,
 * Dependent sum types `Σ x ꞉ A , B x`
   correspond to existential quantification `∃ x ꞉ A , B x`,
 * Identity types `x ≡ y` correspond to equality `x = y`.

So which type corresponds to the proposition
  `∀ n ꞉ ℕ , ∃ m ꞉ ℕ , (n ＝ 2m) ∨ (n ＝ 2m+1)` ?

```
ParityTheorem : Type
ParityTheorem
 = (n : ℕ) → Σ m ꞉ ℕ , (n ≡ (m + m)) ∔ (n ≡ (suc (m + m)))
```

# Elimination rules for `_∔_`, `_×_` and `Σ`

## Binary sums `_∔_`

The elimination rule of binary sums says logically that in order to
prove a proposition `P : A ∔ B → Type` for every element `x : A ∔ B`,
we need to prove the proposition holds for every element of `A` and
`B`.

```
∔-elim : {A B : Type} (P : A ∔ B → Type)
       → ((a : A) → P (inl a))
       → ((b : B) → P (inr b))
       → (x : A ∔ B) → P x
∔-elim P l r (inl a) = l a
∔-elim P l r (inr b) = r b
```

The non-dependent version allows us to give an element of some type `C`
for every element of `A ∔ B`, if we have a function that gives us
elements of `C` from elements of `A` and a function that gives us
elements of `C` from elements of `B`.

```
∔-nondep-elim : {A B C : Type}
              → (A → C)
              → (B → C)
              → (A ∔ B → C)
∔-nondep-elim {A} {B} {C} = ∔-elim (λ _ → C)
```

This is like a type-valued version of `if_then_else_`!

Note that we can define binary sums in terms of dependent sums:

```
open import binary-sums-as-sums
```

## Binary products `_×_`

We can also define binary products in terms of dependent sums. Binary
products are just dependent sums where the second projection does not
depend on the first.

Therefore, we will redefine binary products like so:

```
_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B
```

This says that a binary product consists of a witness `x : A` of the
type `B` which does *not* depend on `x`.

The elimination rule for `_×_` then follows from the elimination rule
for `Σ`, which follows.

## Dependent sums `Σ`

The elimination rule for ‵Σ` looks a little scary!

```
Σ-elim : {A : Type } {B : A → Type} {P : (Σ a ꞉ A , B a) → Type}
       → ((a : A) (b : B a) → P (a , b))
       → (x : Σ a ꞉ A , B a) → P x
```

Logically, this says that in order to show that "for all
`x : Σ a ꞉ A , B x`) we have that `P x` holds", it is enough to show
that "for all `a : A` and `b : B a` we have that `P (a , b)` holds".

In programming, this is called *currying*:

```
Σ-elim f (a , b) = f a b
```

The function `P` which takes a pair becomes a function which takes two
arguments. The inverse function, uncurrying, can also be defined:

```
Σ-uncurry : {A : Type } {B : A → Type} {C : (Σ x ꞉ A , B x) → Type}
          → ((z : Σ x ꞉ A , B x) → C z)
          → (x : A) (y : B x) → C (x , y)
Σ-uncurry g x y = g (x , y)
```

The non-dependent version follows straightforwardly:

```
curry : {A : Type} {B : A → Type} {C : Type}
      → ((x : A) → B x → C)
      → Σ x ꞉ A , B x → C
curry = Σ-elim

uncurry : {A : Type} {B : A → Type} {C : Type}
        → (Σ x ꞉ A , B x → C)
        → (x : A) → B x → C
uncurry = Σ-uncurry
```

The binary product elimination principles can now be easily derived:

```
×-elim : {A B : Type } {P : A × B → Type}
       → ((a : A) (b : B) → P (a , b))
       → (x : A × B) → P x
×-elim = Σ-elim

×-nondep-elim : {A B : Type } {P : A × B → Type}
              → ((x : A × B) → P x)
              → (a : A) (b : B) → P (a , b)
×-nondep-elim = Σ-uncurry
```

# Proof of the Parity Theorem

Now let's prove the parity theorem! We will need to prove a few lemmas
first: one about identity types and two about the natural numbers.

The following lemma about identity types is crucial to many of the
proofs in this module, so let's take a moment to understand it:

```
ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)
```

This proof says that equality is preserved by functions.

The following two lemmas about the natural numbers are also needed in
our proof of the parity theorem:

```
lemma-0 : (m k : ℕ) → suc (m + k) ≡ m + suc k
lemma-0 zero k = refl (suc k)
lemma-0 (suc m) k = ap suc (lemma-0 m k)

lemma-1 : (n m k : ℕ) → n ≡ m + k → suc n ≡ (m + suc k)
lemma-1 n m k p
 = trans (suc n) (suc m + k) (m + suc k) (ap suc p) (lemma-0 m k)
```

Now, let's prove the theorem!

```
parity-proof : ParityTheorem
parity-proof zero = zero , inl (refl zero)
parity-proof (suc zero) = zero , inr (refl 1)
parity-proof (suc (suc n))
 = ∔-nondep-elim l r p
 where
  IH = parity-proof n
  m = fst IH
  p : (n ≡ (m + m)) ∔ (n ≡ suc (m + m))
  p = snd IH
  l : n ≡ (m + m)
    → Σ (λ k → (suc (suc n) ≡ (k + k)) ∔ (suc (suc n) ≡ suc (k + k)))
  l e = (suc m) , (inl (ap suc (lemma-1 n m m e)))
  r : n ≡ suc (m + m)
    → Σ (λ m₁ → (suc (suc n) ≡ (m₁ + m₁)) ∔ (suc (suc n) ≡ suc (m₁ + m₁)))
  r e = {!!}
```
