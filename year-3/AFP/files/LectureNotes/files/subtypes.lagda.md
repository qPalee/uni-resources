<!--
```
{-# OPTIONS --without-K --safe #-}

module subtypes where
open import prelude
open import natural-numbers-functions
```
-->

# There are some exercises in this file

To solve them, create a fresh copy of this file with a name of your choice in the same directory.

# Subtypes

Very often it is useful to consider a subtype of a type. We have seen some examples already, such as the subtype of the natural consisting of the even numbers, the subtype of lists of a given length, the subtype of binary trees consisting of the search trees.

In such a situation it is important to discuss when two elements of a subtype are equal, and this turns out to be a little bit subtle. We need a few new concepts to discuss this:
 1. The function `transport` defined in the file [identity-type](identity-type.lagda.md)
 1. The functions `to-Σ-≡` and `from-Σ-≡` defined in the file [sums-equality](sums.equality.lagda.md)
 1. A function `is-prop` defined here.

## Discussion

Consider the functions `is-even` and `is-odd` defined by the module [natural-numbers-functions](natural-numbers-functions.lagda.md).
In some sense the type `is-even x` is **property** of the number `n`, rather than **data**. This is because `is-even x` is defined to be the type `Σ y ꞉ ℕ , x ≡ 2 * y`, and whereas an element of this `Σ`-type does provide data, there is **at most one** `y` with `x ≡ 2 * y`. So when `y` exists, it is unique. We will regard types that have at most one element as expressing *properties*, with all types, in general, expressing *data*. Of course, types that express property, in particular, express data. For example, the property of being even, expressed as the above type, carries a number. But this number is unique when it exists.

On the other hand, consider type `composite n` defined as follows:
```
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
So the type `composite 30` collects *all* the ways in which 30 can be composite, and so, in some sense, its elements are *data* rather than mere *property*.

We say that a type expresses property, rather than data, if it has at
most one element, that is, any two of its elements are equal.
```
is-prop : Type → Type
is-prop X = (x y : X) → x ≡ y
```

Here are some examples.

**Exercise.**
Falsity as expressed by emptiness is property.
```
𝟘-is-prop : is-prop 𝟘
𝟘-is-prop ()
```
**Exercise.**
Truth as expressed by the unit type is property.
```
𝟙-is-prop : is-prop 𝟙
𝟙-is-prop ⋆ ⋆ = refl ⋆
```
Now the following is harder to prove, and needs the material developed below.
```postpone
being-even-is-prop : (n : ℕ) → is-prop (is-even n)
```
One of the main purposes of this file is to explain how we can prove things such as the above.


**Exercise.**
We also have, in light of the above examples, that being a composite number is not property.
```
being-composite-is-not-prop-in-general : Σ n ꞉ ℕ , ¬ is-prop (composite n)
being-composite-is-not-prop-in-general =
  30 ,
  λ h → 30-composite₀-not-equal-to-30-composite₁ (h 30-composite₀ 30-composite₁)
 where
  3-not-equal-to-10 : ¬ (3 ≡ 10)
  3-not-equal-to-10 ()

  30-composite₀-not-equal-to-30-composite₁ : ¬ (30-composite₀ ≡ 30-composite₁)
  30-composite₀-not-equal-to-30-composite₁ e = 3-not-equal-to-10 (ap fst e)
```
You can take e.g. `n` to be 30, assume that would be property, and get a contradiction (that is, an element of the empty type `𝟘`).

## Things isomorphic to properties are themselves properties

```
open import isomorphisms

iso-preserves-prop : {X Y : Type}
                   → X ≅ Y
                   → is-prop X
                   → is-prop Y
iso-preserves-prop {X} {Y} (Isomorphism f (Inverse g gf fg)) X-is-prop = Y-is-prop
 where
  Y-is-prop : is-prop Y
  Y-is-prop y y' =
   y        ≡⟨ sym (fg y) ⟩
   f (g y)  ≡⟨ ap f (X-is-prop (g y) (g y')) ⟩
   f (g y') ≡⟨ fg y' ⟩
   y'       ∎
```
Notice that the above doesn't use `gf`. This motivates the following.

## Retracts of properties are properties

We define `retract` in the same way as `isomorphism`, but dropping one of the required equations, corresponding `gf` above.
```
retract_of_ : Type → Type → Type
retract Y of X = Σ f ꞉ (X → Y) , Σ g ꞉ (Y → X) , f ∘ g ∼ id
```
The function `f` is called the *retraction* and the function `g` is called the *section*.
Here is an example:
```
open import binary-type

𝟚-is-a-retract-of-ℕ : retract 𝟚 of ℕ
𝟚-is-a-retract-of-ℕ = f , g , fg
 where
  f : ℕ → 𝟚
  f 0       = 𝟎
  f (suc n) = 𝟏

  g : 𝟚 → ℕ
  g 𝟎 = 0
  g 𝟏 = 1

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏
```
Coming back to the above observation about isomorphisms, we have the following.
```
retracts-preserve-prop : {X Y : Type}
                       → retract Y of X
                       → is-prop X
                       → is-prop Y
retracts-preserve-prop {X} {Y} (f , g , fg) X-is-prop = Y-is-prop
 where
  Y-is-prop : is-prop Y
  Y-is-prop y y' =
   y        ≡⟨ sym (fg y) ⟩
   f (g y)  ≡⟨ ap f (X-is-prop (g y) (g y')) ⟩
   f (g y') ≡⟨ fg y' ⟩
   y'       ∎
```
This is useful because in some cases it saves us from proving `gf`.
```
retract-from-iso : {X Y : Type} → X ≅ Y → retract Y of X
retract-from-iso (Isomorphism f (Inverse g _ fg)) = (f , g , fg)

iso-from-retract : {X Y : Type}
                   ((f , g , fg) : retract Y of X)
                 → g ∘ f ∼ id
                 → X ≅ Y
iso-from-retract (f , g , fg) gf = Isomorphism f (Inverse g gf fg)
```

## When equality is property

It is not the case that equality is always property, but it is for most types we are interested in, although we have to prove this. Here we prove it for the natural numbers.
We begin by defining our own equality as we did in the [introduction](introduction.lagda.md) lecture notes.
```
_≣_ : ℕ → ℕ → Type
0     ≣ 0     = 𝟙
0     ≣ suc y = 𝟘
suc x ≣ 0     = 𝟘
suc x ≣ suc y = x ≣ y

≣-is-prop : (x y : ℕ) → is-prop (x ≣ y)
≣-is-prop 0       0       = 𝟙-is-prop
≣-is-prop 0       (suc y) = 𝟘-is-prop
≣-is-prop (suc x) 0       = 𝟘-is-prop
≣-is-prop (suc x) (suc y) = ≣-is-prop x y

open import natural-numbers-functions

ℕ-≡-retract-of-≣ : (x y : ℕ) → retract (x ≡ y) of (x ≣ y)
ℕ-≡-retract-of-≣ x y = f x y , g x y , fg x y
 where
  g : (x y : ℕ) → (x ≡ y) → (x ≣ y)
  g 0       0       (refl 0) = ⋆
  g (suc x) (suc y) p        = g x y (suc-is-injective p)

  f : (x y : ℕ) → (x ≣ y) → (x ≡ y)
  f 0       0       ⋆ = refl 0
  f (suc x) (suc y) p = ap suc (f x y p)

  fg : (x y : ℕ) → f x y ∘ g x y ∼ id
  fg 0       0       (refl 0)        = refl (refl 0)
  fg (suc x) (suc y) (refl .(suc x)) = goal
   where
    IH : f x x (g x x (refl x)) ≡ refl x
    IH = fg x y (refl x)

    goal : ap suc (f x x (g x x (refl x))) ≡ refl (suc x)
    goal = ap (ap suc) IH

ℕ-≡-is-prop : (x y : ℕ) → is-prop (x ≡ y)
ℕ-≡-is-prop x y = retracts-preserve-prop (ℕ-≡-retract-of-≣ x y) (≣-is-prop x y)
```
We actually have an isomorphism, but we don't need this fact for the purposes of our discussion about subtypes:
```
ℕ-≡-iso : (x y : ℕ) → (x ≣ y) ≅ (x ≡ y)
ℕ-≡-iso x y = iso-from-retract (ℕ-≡-retract-of-≣ x y) (gf x y)
 where
  f = λ x y → fst (ℕ-≡-retract-of-≣ x y)
  g = λ x y → fst (snd (ℕ-≡-retract-of-≣ x y))

  gf : (x y : ℕ) → g x y ∘ f x y ∼ id
  gf 0       0       ⋆ = refl ⋆
  gf (suc x) (suc y) p = goal
   where
    IH : g x y (f x y p) ≡ p
    IH = gf x y p

    h : (m n : ℕ) (e : m ≡ n) → ap pred (ap suc e) ≡ e
    h m m (refl m) = refl (refl m)

    goal = g x y (ap pred (ap suc (f x y p))) ≡⟨ ap (g x y) (h x y (f x y p)) ⟩
           g x y (f x y p)                    ≡⟨ IH ⟩
           p                                  ∎
```

**Exercise.**
```
logically-equivalent-props-are-isomorphic : {X Y : Type}
                                          → is-prop X
                                          → is-prop Y
                                          → X ⇔ Y
                                          → X ≅ Y
logically-equivalent-props-are-isomorphic X-is-prop Y-is-prop (f , g) =
  record { bijection = f ;
           bijectivity = record { inverse = g ; η = gf ; ε = fg }
         }
 where
  gf : g ∘ f ∼ id
  gf x = X-is-prop (g (f x)) x

  fg : f ∘ g ∼ id
  fg y = Y-is-prop (f (g y)) y
```

## Sets

We say that a type is a *set* if equality of its elements is property, rather than just data:
```
is-set : Type → Type
is-set X = (x y : X) → is-prop (x ≡ y)

ℕ-is-set : is-set ℕ
ℕ-is-set = ℕ-≡-is-prop
```
**Exercise.** (Hard. You may wish to do ther other ones first and come back to it later, if ever.)
```
trans-is-associative : {X : Type} {x y z w : X}
                       (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                     → trans p (trans q r) ≡ trans (trans p q) r
trans-is-associative p (refl _) (refl _) = refl p

sym-inverse : {X : Type} {x y : X}
              (p : x ≡ y)
            → trans (sym p) p ≡ refl y
sym-inverse (refl x) = refl (refl x)


≡-retract : {X Y : Type}
            ((f , g , h) : retract Y of X)
            (x y : Y)
          → retract (x ≡ y) of (g x ≡ g y)
≡-retract (f , g , h) x y = α , β , αβ
 where
  α : g x ≡ g y → x ≡ y
  α p = x        ≡⟨ sym (h x) ⟩
        f (g x)  ≡⟨ ap f p ⟩
        f (g y)  ≡⟨ h y ⟩
        y        ∎

  β : x ≡ y → g x ≡ g y
  β = ap g

  αβ : α ∘ β ∼ id
  αβ (refl x) =
   trans (sym (h x)) (trans (refl _) (h x)) ≡⟨ trans-is-associative (sym (h x)) (refl _) (h x) ⟩
   trans (sym (h x)) (h x)                  ≡⟨ sym-inverse (h x) ⟩
   refl x                                   ∎


retracts-of-sets-are-sets : {X Y : Type}
                          → retract Y of X
                          → is-set X
                          → is-set Y
retracts-of-sets-are-sets {X} {Y} (f , g , h) X-is-set x y p q =
 p       ≡⟨ sym (αβ p) ⟩
 α (β p) ≡⟨ ap α (X-is-set (g x) (g y) (ap g p) (ap g q)) ⟩
 α (β q) ≡⟨ αβ q ⟩
 q ∎
 where
  α : g x ≡ g y → x ≡ y
  α p = x        ≡⟨ sym (h x) ⟩
        f (g x)  ≡⟨ ap f p ⟩
        f (g y)  ≡⟨ h y ⟩
        y        ∎

  β : x ≡ y → g x ≡ g y
  β = ap g

  αβ : α ∘ β ∼ id
  αβ (refl x) =
   trans (sym (h x)) (trans (refl _) (h x)) ≡⟨ trans-is-associative (sym (h x)) (refl _) (h x) ⟩
   trans (sym (h x)) (h x)                  ≡⟨ sym-inverse (h x) ⟩
   refl x                                   ∎
```
**Exercise.** Use this to conclude that the type `𝟚` is a set.
```
𝟚-is-set : is-set 𝟚
𝟚-is-set = retracts-of-sets-are-sets 𝟚-is-a-retract-of-ℕ ℕ-is-set
```
Alternatively, we could mimick the proof we used to show that `ℕ` is a set. 

## Equality in Σ-types

This is developed in the following file. Click at the name to read it, and then come back to this file.
```
open import sums-equality
```

## Equality in subtypes

Although equality of elements of `Σ`-types is rather complicated, equality of elements of subtypes is quite easy to work with, even though subtypes are defined using `Σ`-types, once one has established some machinery, which is the main purpose of this file.

Recall that we defined a subype of a type `X` to be a type of the form `Σ x ꞉ X , A x` with `A x` a property for every `X`.
```
to-subtype-≡ : {X : Type} {A : X → Type}
             → ((x : X) → is-prop (A x))
             → {x y : X} {a : A x} {b : A y}
             → x ≡ y
             → (x , a) ≡ (y , b)
to-subtype-≡ {X} {A} A-is-prop {x} {y} {a} {b} e =
 (x , a) ≡⟨ to-Σ-≡ (e , I) ⟩
 (y , b) ∎
  where
   I : transport A e a ≡ b
   I = A-is-prop y (transport A e a) b
```
The above says that when considering equality in subtypes, the second component can be ignored. The following is something we already proved, and doesn't require `A x` be a property.
```
from-subtype-≡ : {X : Type} {A : X → Type}
               → {x y : X} {a : A x} {b : A y}
               → (x , a) ≡ (y , b)
               → x ≡ y
from-subtype-≡ = Σ-≡-fst
```

Notice that the above can be equivalently written as
```
to-subtype-≡' : {X : Type} {A : X → Type}
              → ((x : X) → is-prop (A x))
              → {σ τ : Σ x ꞉ X , A x}
              → fst σ ≡ fst τ
              → σ ≡ τ
to-subtype-≡' {X} {A} A-is-prop {x , a} {y , b} = to-subtype-≡ A-is-prop {x} {y} {a} {b}
```

*Side-remark.* One can also show that if `A x` is a property, then the type `(x , a) ≡ (y , b)` is isomorphic to the type `x ≡ y`, but this would take us far afield.
(If you are really interested, here are [lecture notes](https://martinescardo.github.io/HoTT-UF-in-Agda-Lecture-Notes/index.html) that develop this and more, but this is rather advanced.)

## Being even is property

Here is a proof of the above promised example.
```
being-even-is-prop : (x : ℕ) → is-prop (is-even x)
being-even-is-prop x (y , e) (y' , e') = goal
 where
  h : y ≡ y'
  h = mul-by-2-is-cancellable y y'
       (2 * y  ≡⟨ sym e ⟩
        x      ≡⟨ e' ⟩
        2 * y' ∎)

  goal : (y , e) ≡ (y' , e')
  goal = to-subtype-≡ (λ z → ℕ-≡-is-prop x (2 * z)) h
```

## The vector-list-isomorphism

The above machinery was tricky to develop, but once it is developed it
makes our life easier.  A sample application of the above
characterization of equality of subtypes is to get a relatively short
proof of the following.

```
open import List-functions

Vector' : Type → ℕ → Type
Vector' A n = Σ xs ꞉ List A , length xs ≡ n

to-Vector'-≡ : {n : ℕ} {A : Type} {v w : Vector' A n}
             → fst v ≡ fst w
             → v ≡ w
to-Vector'-≡ {n} = to-subtype-≡' (λ xs → ℕ-≡-is-prop (length xs) n)

_:::_ : {n : ℕ} {A : Type} → A → Vector' A n → Vector' A (suc n)
_:::_ {n} x (xs , e) = x :: xs , ap suc e

vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ Vector' A n
vectors-from-lists {A} n = Isomorphism (f n) (Inverse (g n) (gf n) (fg n))
 where
  f : (n : ℕ) → Vector A n → Vector' A n
  f 0       []        = [] , refl 0
  f (suc n) (x :: xs) = x ::: f n xs

  g : (n : ℕ) → Vector' A n → Vector A n
  g 0       ([] , e)      = []
  g (suc n) (x :: xs , e) = x :: g n (xs , suc-is-injective e)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf 0       []        = refl []
  gf (suc n) (x :: xs) = goal
   where
    IH : g n (f n xs) ≡ xs
    IH = gf n xs

    I : (fst (f n xs) , suc-is-injective (ap suc (snd (f n xs))))  ≡ f n xs
    I = to-Vector'-≡ (refl (fst (f n xs)))

    goal =
     g (suc n) (x ::: f n xs)                                  ≡⟨ refl _ ⟩
     g (suc n) (x ::: (fst (f n xs) , snd (f n xs)))           ≡⟨ refl _ ⟩
     x :: g n (fst (f n xs) , ap pred (ap suc (snd (f n xs)))) ≡⟨ ap (λ - → x :: g n -) I ⟩
     x :: g n (f n xs)                                         ≡⟨ ap (x ::_) IH ⟩
     x :: xs                                                   ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg 0 ([] , refl 0)                  = refl ([] , refl 0)
  fg (suc n) (x :: xs , refl (suc n)) = ap (x :::_) (fg n (xs , (refl n)))
```

## Showing that some types are property

**Exercises.**
```agda
×-is-prop : {X Y : Type}
          → is-prop X
          → is-prop Y
          → is-prop (X × Y)
×-is-prop X-is-prop Y-is-prop (x₁ , y₁) (x₂ , y₂) =
 ap₂ _,_ (X-is-prop x₁ x₂) (Y-is-prop y₁ y₂)

∔-is-prop : {X Y : Type}
          → is-prop X
          → is-prop Y
          → ¬ (X × Y)
          → is-prop (X ∔ Y)
∔-is-prop X-is-prop Y-is-prop h (inl x₁) (inl x₂) = ap inl (X-is-prop x₁ x₂)
∔-is-prop X-is-prop Y-is-prop h (inl x)  (inr y)  = 𝟘-elim (h (x , y))
∔-is-prop X-is-prop Y-is-prop h (inr y)  (inl x)  = 𝟘-elim (h (x , y))
∔-is-prop X-is-prop Y-is-prop h (inr y₁) (inr y₂) = ap inr (Y-is-prop y₁ y₂)

∔-is-prop← : {X Y : Type}
           → is-prop X
           → is-prop Y
           → is-prop (X ∔ Y)
           → ¬ (X × Y)
∔-is-prop← {X} {Y} _ _ X∔Y-is-prop (x , y) =
 inl-not-equal-inr x y (X∔Y-is-prop (inl x) (inr y))
 where
  inl-not-equal-inr : (x : X) (y : Y) → ¬ (inl x ≡ inr y)
  inl-not-equal-inr x y ()

Σ-is-prop : {X : Type} {A : X → Type}
          → is-prop X
          → ((x : X) → is-prop (A x))
          → is-prop (Σ x ꞉ X , A x)
Σ-is-prop {X} {A} X-is-prop Ax-is-prop (x₁ , a₁) (x₂ , a₂) = to-Σ-≡ (p , q)
 where
  p : x₁ ≡ x₂
  p = X-is-prop x₁ x₂

  q : transport A (X-is-prop x₁ x₂) a₁ ≡ a₂
  q = Ax-is-prop x₂ (transport A p a₁) a₂

open import function-extensionality

Π-is-prop : FunExt
          → {X : Type} {A : X → Type}
          → ((x : X) → is-prop (A x))
          → is-prop (Π x ꞉ X , A x)
Π-is-prop fe Ax-is-prop f₁ f₂ = fe (λ x → Ax-is-prop x (f₁ x) (f₂ x))
```

Can you come up with similar conditions to show that some types are sets? The conditions won't be exactly the same as above.
