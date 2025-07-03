# Lecture Notes - Week 4

Martin Escardo, 10-12 Feb.

```
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week4 where

open import prelude
open import List-functions
open import natural-numbers-functions
```

### More examples of types that can't be defined in Haskell

The fact that Agda can handle logic can be not only used to prove certain programs correct, but also to define types that reflect more precisely what we have in mind, and avoid "junk".

This can be defined in Haskell.
```agda
data BT (A : Type) : Type where
 leaf : BT A
 branch : A → BT A → BT A → BT A
```

But now we consider a type Binary search trees, which can't be defined in Haskell. For simplicity, (of natural numbers for simplicity, although later will will drop this restriction)

```agda
_<_ _>_ : ℕ → ℕ → Type
x < y = suc x ≤ y
x > y = y < x

all-smaller  : BT ℕ → ℕ → Type
all-smaller leaf           y = 𝟙
all-smaller (branch x l r) y = (x < y)
                             × all-smaller l y
                             × all-smaller r y

all-bigger  : BT ℕ → ℕ → Type
all-bigger leaf           y = 𝟙
all-bigger (branch x l r) y = (x > y)
                            × all-bigger l y
                            × all-bigger r y

is-bst : BT ℕ → Type
is-bst leaf           = 𝟙
is-bst (branch x l r) = all-smaller l x
                      × all-bigger r x
                      × is-bst l
                      × is-bst r
```

The type of binary search trees is that of binary trees that satisfy
`is-bst`.

```agda
BST₀ : Type
BST₀ = Σ t ꞉ BT ℕ , is-bst t
```
Here is a second approach.
```agda
data BST₁ : Type
all-smaller₁ : BST₁ → ℕ → Type
all-bigger₁  : BST₁ → ℕ → Type

data BST₁ where
 leaf : BST₁
 branch : (x : ℕ) (l r : BST₁)
          (s : all-smaller₁ l x) (b : all-bigger₁ r x)
        → BST₁

all-smaller₁ leaf               y = 𝟙
all-smaller₁ (branch x l r s b) y = (x < y) × {!!}

all-bigger₁ leaf               y = 𝟙
all-bigger₁ (branch x l r s b) y = (x > y) × {!!}


insert : ℕ → BST₁ → BST₁
insert = λ z z₁ → z₁ -- We are not going to do this this week.

delete : ℕ → BST₁ → BST₁
delete = λ z z₁ → z₁  -- We are not going to do this this week.
```

### Type isomorphisms

Sometimes types are different but in some sense equivalent for programming purposes. Here are some examples.

 * The two types of BSTs defined above.

 * The three types of vectors discussed last week.

   ```not-to-include-as-code
   Vec₀ : (A : Type) → ℕ → Type
   Vec₀ A n = Σ xs ꞉ List A , is-of-length₀ n xs

   data Vec (A : Type) : ℕ → Type where
    []   : Vec A zero
    _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

   Vec₁ : (A : Type) → ℕ → Type
   Vec₁ A n = Fin n → A
   ```

 * The two types of finite types discussed last week.
   ```not-to-include-as-code
   Fin₀ : ℕ → Type
   Fin₀ zero = 𝟘
   Fin₀ (suc n) = 𝟙 ∔ (Fin₀ n)

  data Fin : ℕ → Type where
   zero : {n : ℕ} → Fin (suc n)
   suc : {n : ℕ} → Fin n → Fin (suc n)
   ```

### First definition of isomorphism

Definition of when a function `f : A → B` is a bijection:
```agda
module one-possible-definition-of-the-type-of-isomorphisms where

 is-bijection : {A B : Type} → (A → B) → Type
 is-bijection {A} {B} f = Σ g ꞉ (B → A) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))
```

The type of isomorphisms. An isomorphism from a type `A` to a type `B`
is a function `f : A → B` together with a proof that it is a
bijection. \cong

```
 _≅_ : Type → Type → Type
 A ≅ B = Σ f ꞉ (A → B) , is-bijection f
```

### Second definition of isomorphism

An equivalent definition using records is more convenient.

f
Inverse g η ε : is-bijection f
b : is-bijective f

inverse b : B → A
η b
ε b

or, equivalently:

b.inverse
b.η
b.ε


```
module the-adopted-definition-of-the-type-of-isomorphisms where

 record is-bijection {A B : Type} (f : A → B) : Type where
  constructor
   Inverse
  field
   inverse : B → A
   η       : inverse ∘ f ∼ id  -- \eta
   ε       : f ∘ inverse ∼ id  -- \varepsilon ε   \epsilon ϵ
```

```agda
 record _≅_ (A B : Type) : Type where
  constructor
   Isomorphism
  field
   bijection   : A → B
   bijectivity : is-bijection bijection

 infix 0 _≅_
```

Actually the second definition is already defined in the following
import (and this is why we hid our repetition inside modules).

```agda
open import isomorphisms hiding (Bool-𝟚-isomorphism ; Bool-𝟚-isomorphism')
```

### Examples

In general, there may be multiple isomorphisms between two types.

```agda
open import Bool
open import binary-type

Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = Isomorphism f (Inverse g gf fg)
 where
  f : Bool → 𝟚
  f true = 𝟏   -- \B1
  f false = 𝟎
  g : 𝟚 → Bool
  g 𝟎 = false
  g 𝟏 = true
  gf : g ∘ f ∼ id
  gf true = refl true
  gf false = refl false
  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

```
To save typing, you can use the file [isomorphism-template](../isomorphism-template.lagda.md), which you can import into an `emacs` file with `C-x i ../isomorphism-template.lagda.md`.

The type ℕ ≅ Bool happens to be empty.


```
Bool-𝟚-isomorphism' : Bool ≅ 𝟚
Bool-𝟚-isomorphism' = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f true = 𝟎
  f false = 𝟏

  g : 𝟚 → Bool
  g 𝟎 = true
  g 𝟏 = false

  gf : g ∘ f ∼ id
  gf true = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


Bool-𝟙∔𝟙-isomorphism'' : Bool ≅ 𝟙 ∔ 𝟙
Bool-𝟙∔𝟙-isomorphism'' = {!!}

open import Maybe hiding (Maybe-isomorphism)

Maybe-isomorphism : {A : Type} → Maybe A ≅ 𝟙 ∔ A
Maybe-isomorphism = {!!}

Maybe-isomorphism' : {A B : Type} → A ≅ B → Maybe A ≅ 𝟙 ∔ B
Maybe-isomorphism' = {!!}

Maybe-Bool-isomorphism : Maybe Bool ≅ 𝟙 ∔ 𝟙 ∔ 𝟙
Maybe-Bool-isomorphism = {!!}

×-comm : {A B C : Type} → A × B ≅ B × A
×-comm  = {!!}

×-assoc : {A B C : Type} → (A × B) × C ≅ A × (B × C)
×-assoc  = {!!}

∔-comm : {A B C : Type} → A ∔ B ≅ B ∔ A
∔-comm  = {!!}

∔-assoc : {A B C : Type} → (A ∔ B) ∔ C ≅ A ∔ (B ∔ C)
∔-assoc {A} {B} {C} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (A ∔ B) ∔ C → A ∔ (B ∔ C)
  f (inl (inl a)) = inl a
  f (inl (inr b)) = inr (inl b)
  f (inr c) = inr (inr c)

  g : A ∔ (B ∔ C) → (A ∔ B) ∔ C
  g (inl a) = inl (inl a)
  g (inr (inl b)) = inl (inr b)
  g (inr (inr c)) = inr c

  gf : g ∘ f ∼ id
  gf (inl (inl a)) = refl (inl (inl a))
  gf (inl (inr b)) = refl (inl (inr b))
  gf (inr c) = refl (inr c)

  fg : f ∘ g ∼ id
  fg (inl a) = refl (inl a)
  fg (inr (inl b)) = refl (inr (inl b))
  fg (inr (inr c)) = refl (inr (inr c))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


×-∔-distributivity : {A X Y : Type} → A × (X ∔ Y) ≅ (A × X) ∔ (A × Y)
×-∔-distributivity = {!!}

open import function-extensionality

function-from-plus-isomorphism : FunExt
                               → {X Y A : Type}
                               → (X ∔ Y → A) ≅ ((X → A) × (Y → A))
function-from-plus-isomorphism fe {X} {Y} {A} =
 record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (X ∔ Y → A) → (X → A) × (Y → A)
  f ϕ = (λ x → ϕ (inl x)) , (λ (y : Y) → ϕ (inr y))

  g : (X → A) × (Y → A) → X ∔ Y → A
  g (γl , γr) (inl x) = γl x
  g (γl , γr) (inr y) = γr y

  gf : g ∘ f ∼ id
  gf ϕ = fe I
   where
    I : g (f ϕ) ∼ ϕ
    I (inl x) = refl (ϕ (inl x))
    I (inr y) = refl (ϕ (inr y))

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


function-to-times-isomorphism : {A X Y : Type}
                              → (A → X × Y) ≅ ((A → X) × (A → Y))
function-to-times-isomorphism = {!!}


curry : {X Y Z : Type} → (X × Y → Z) ≅ (X → (Y → Z))
curry = {!!}

dependent-curry : {X : Type} {Y : X → Type} {Z : Type}
                → ((Σ x ꞉ X , Y x) → Z) ≅ ((x : X) (y : Y x) → Z)
dependent-curry = {!!}

more-dependent-curry : {X : Type} {Y : X → Type} {Z : (x : X) → Y x → Type}
                     → (((x , y) : (Σ x ꞉ X , Y x)) → Z x y)
                     ≅ ((x : X) (y : Y x) → Z x y)
more-dependent-curry = {!!}

Bool-example : Bool ≅ Bool
Bool-example = record { bijection = not ; bijectivity = not-is-bijection }
 where
  notnot : not ∘ not ∼ id
  notnot true = refl true
  notnot false = refl false

  not-is-bijection : is-bijection not
  not-is-bijection = record { inverse = not ; η = notnot ; ε = notnot }

≅-refl : (X : Type) → X ≅ X
≅-refl X = record { bijection = id ; bijectivity = id-is-bijection }
 where
  id-is-bijection : is-bijection id
  id-is-bijection = record { inverse = id ; η = refl ; ε = refl }


≅-trans : (X Y Z : Type) → X ≅ Y → Y ≅ Z → X ≅ Z
≅-trans X Y Z (Isomorphism f (Inverse g η ε)) (Isomorphism f' (Inverse g' η' ε')) =
 Isomorphism (f' ∘ f) (Inverse (g ∘ g') η'' ε'')
  where
   η'' : (x : X) → g (g' (f' (f x))) ≡ x
   η'' x = g (g' (f' (f x))) ≡⟨ ap g (η' (f x)) ⟩
           g (f x)           ≡⟨ η x ⟩
           x                 ∎
           where
            I : g' (f' (f x)) ≡ f x
            I = η' (f x)
            II : g (g' (f' (f x))) ≡ g (f x)
            II = ap g I

   ε'' : (x : Z) → f' (f (g (g' x))) ≡ x
   ε'' x = f' (f (g (g' x))) ≡⟨ ap f' (ε (g' x)) ⟩
           f' (g' x)         ≡⟨ ε' x ⟩
           x                 ∎

   ε''-again : (x : Z) → f' (f (g (g' x))) ≡ x
   ε''-again x = trans (ap f' (ε (g' x))) (ε' x )
```
We can define binary sums using general sums:

Idea: inl a₀     (𝟎 , a₀)
      inr a₁     (𝟏 , a₁)


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
binary-sum-isomorphism A₀ A₁ = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A₀ ∔ A₁ → A₀ ∔' A₁
  f (inl a₀) = 𝟎 , a₀
  f (inr a₁) = 𝟏 , a₁

  g : A₀ ∔' A₁ → A₀ ∔ A₁
  g (𝟎 , a₀) = inl a₀
  g (𝟏 , a₁) = inr a₁

  gf : g ∘ f ∼ id
  gf (inl _) = refl _
  gf (inr _) = refl _

  fg : f ∘ g ∼ id
  fg (𝟎 , _) = refl _
  fg (𝟏 , _) = refl _

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

Similarly, binary products are a particular case of arbitrary products.

(a₀ , a₁) : A₀ × A₁
                code as a function ϕ : (n : 𝟚) → A n
                ϕ 𝟎 = a₀
                ϕ 𝟏 = a₁

(ϕ 𝟎 , ϕ 𝟏)      <-------| ϕ

```agda
_×'_ : Type → Type → Type
A₀ ×' A₁ = Π n ꞉ 𝟚 , A n  -- (n : 𝟚) → A n
 where
  A : 𝟚 → Type
  A 𝟎 = A₀
  A 𝟏 = A₁

infixr 2 _×'_
```
We could have written the type `Π n ꞉ 𝟚 , A n` as simply `(n : 𝟚) → A n`, but we wanted to emphasize that binary products `_×_` are special cases of arbitrary products `Π`.

The construction of the following isomorphism uses *function extensionality*. This is not provable or disprovable in Agda (or MLTT), and hence we have to use it as an assumption. This says that if to functions have equal outputs for all inputs, then they are equal. This is a principle generally used in mathematics and computer science.

```agda
open import isomorphisms

binary-product-isomorphism : FunExt → (A₀ A₁ : Type) → A₀ × A₁ ≅ A₀ ×' A₁
binary-product-isomorphism funext A₀ A₁ = {!!}
```

We can define the types of lists from the type of vectors:

```agda
lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors = {!!}
```
And the type of vectors from the type of lists:
```agda
vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ (Σ xs ꞉ List A , (length xs ≡ n))
vectors-from-lists = {!!}
```

```agda
Vector' : (A : Type) → ℕ → Type
Vector' A 0       = 𝟙
Vector' A (suc n) = A × Vector' A n

[]' : {A : Type} → Vector' A 0
[]' = ⋆

_::'_ : {A : Type} {n : ℕ} → A → Vector' A n → Vector' A (suc n)
x ::' xs = x , xs

List' : Type → Type
List' X = Σ n ꞉ ℕ , Vector' X n

```

```agda
vectors-in-basic-MLTT : {A : Type} (n : ℕ) → Vector A n ≅ Vector' A n
vectors-in-basic-MLTT {A} n = {!!}

lists-in-basic-MLTT : {A : Type} → List A ≅ List' A
lists-in-basic-MLTT {A} = {!!}
```

**Exercise.** Last week we saw various possible definitions of the
              type of vectors. Prove that all of them are isomorphic.

```agda
open import Fin
open import Fin-functions hiding (Fin-isomorphism)

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism = {!!}
```
