# Lecture Notes - Week 4

Martin Escardo, 10-12 Feb.

```
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week4-solutions where

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
{-
data BST₁ : Type
all-smaller₁ all-bigger₁  : BST₁ → ℕ → Type

data BST₁ where
 leaf : BST₁
 branch : (x : ℕ) (l r : BST₁)
          (s : all-smaller₁ l x) (b : all-bigger₁ r x)
        → BST₁

all-smaller₁ leaf               y = 𝟙
all-smaller₁ (branch x l r s b) y = (x < y) × {!!} -- We'll do this later on.

all-bigger₁ leaf               y = 𝟙
all-bigger₁ (branch x l r s b) y = (x > y) × {!!} -- We'll do this later on.


insert : ℕ → BST₁ → BST₁
insert = {!!} -- We are not going to do this this week.

delete : ℕ → BST₁ → BST₁
delete = {!!}   -- We are not going to do this this week.
-}
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
Bool-𝟙∔𝟙-isomorphism'' = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟙 ∔ 𝟙
  f true = inl ⋆
  f false = inr ⋆

  g : 𝟙 ∔ 𝟙 → Bool
  g (inl ⋆) = true
  g (inr ⋆) = false

  gf : g ∘ f ∼ id
  gf true = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr ⋆) = refl (inr ⋆)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


open import Maybe hiding (Maybe-isomorphism)

Maybe-isomorphism : {A : Type} → Maybe A ≅ 𝟙 ∔ A
Maybe-isomorphism {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe A → 𝟙 ∔ A
  f nothing = inl ⋆
  f (just a) = inr a

  g : 𝟙 ∔ A → Maybe A
  g (inl ⋆) = nothing
  g (inr a) = just a

  gf : g ∘ f ∼ id
  gf nothing = refl nothing
  gf (just a) = refl (just a)

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr a) = refl (inr a)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

Maybe-isomorphism' : {A B : Type} → A ≅ B → Maybe A ≅ 𝟙 ∔ B
Maybe-isomorphism' {A} {B} (Isomorphism f (Inverse g η ε)) =
 Isomorphism f' (Inverse g' η' ε')
 where
  f' : Maybe A → 𝟙 ∔ B
  f' nothing = inl ⋆
  f' (just a) = inr (f a)

  g' : 𝟙 ∔ B → Maybe A
  g' (inl ⋆) = nothing
  g' (inr b) = just (g b)

  η' : g' ∘ f' ∼ id
  η' nothing = refl nothing
  η' (just a) = just (g (f a)) ≡⟨ ap just (η a) ⟩
                just a         ∎

  ε' : f' ∘ g' ∼ id
  ε' (inl ⋆) = refl (inl ⋆)
  ε' (inr b) = inr (f (g b)) ≡⟨ ap inr (ε b) ⟩
               inr b         ∎

Maybe-Bool-isomorphism : Maybe Bool ≅ 𝟙 ∔ 𝟙 ∔ 𝟙
Maybe-Bool-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe Bool → 𝟙 ∔ 𝟙 ∔ 𝟙
  f nothing = inl ⋆
  f (just true) = inr (inl ⋆)
  f (just false) = inr (inr ⋆)

  g : 𝟙 ∔ 𝟙 ∔ 𝟙 → Maybe Bool
  g (inl ⋆) = nothing
  g (inr (inl ⋆)) = just true
  g (inr (inr ⋆)) = just false

  gf : g ∘ f ∼ id
  gf nothing = refl nothing
  gf (just true) = refl (just true)
  gf (just false) = refl (just false)


  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr (inl ⋆)) = refl (inr (inl ⋆))
  fg (inr (inr ⋆)) = refl (inr (inr ⋆))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


×-comm : {A B C : Type} → A × B ≅ B × A
×-comm  = Isomorphism
           (λ (a , b) → (b , a))
           (Inverse
             (λ (b , a) → (a , b))
             refl
             refl)

×-assoc : {A B C : Type} → (A × B) × C ≅ A × (B × C)
×-assoc  = Isomorphism
            (λ ((a , b) , c) → (a , (b , c)))
            (Inverse
              (λ (a , (b , c)) → ((a , b) , c))
              refl
              refl)

∔-comm : {A B C : Type} → A ∔ B ≅ B ∔ A
∔-comm  {A} {B} {C} = Isomorphism f (Inverse g gf fg)
 where
  f : A ∔ B → B ∔ A
  f (inl a) = inr a
  f (inr b) = inl b

  g : B ∔ A → A ∔ B
  g (inl b) = inr b
  g (inr a) = inl a

  gf : g ∘ f ∼ id
  gf (inl a) = refl (inl a)
  gf (inr b) = refl (inr b)

  fg : f ∘ g ∼ id
  fg (inl b) = refl (inl b)
  fg (inr a) = refl (inr a)


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
×-∔-distributivity {A} {X} {Y} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A × (X ∔ Y) → (A × X) ∔ (A × Y)
  f (a , inl x) = inl (a , x)
  f (a , inr y) = inr (a , y)

  g : (A × X) ∔ (A × Y) → A × (X ∔ Y)
  g (inl (a , x)) = a , inl x
  g (inr (a , y)) = a , inr y

  gf : g ∘ f ∼ id
  gf (a , inl x) = refl (a , inl x)
  gf (a , inr y) = refl (a , inr y)

  fg : f ∘ g ∼ id
  fg (inl (a , x)) = refl (inl (a , x))
  fg (inr (a , y)) = refl (inr (a , y))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

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
  fg = λ x → refl ((λ x₁ → x .fst x₁) , (λ y → x .snd y))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


function-to-times-isomorphism : FunExt
                              → {A X Y : Type}
                              → (A → X × Y) ≅ ((A → X) × (A → Y))
function-to-times-isomorphism fe {A} {X} {Y} =
 Isomorphism (λ (ϕ : A → X × Y) → (λ (a : A) → fst (ϕ a)) , (λ (a : A) → snd (ϕ a)))
  (Inverse (λ (γ , δ) → λ (a : A) → γ a , (δ a))
   refl
   refl)


curry : {X Y Z : Type} → (X × Y → Z) ≅ (X → (Y → Z))
curry {X} {Y} {Z} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (X × Y → Z) → (X → (Y → Z))
  f ϕ x y = ϕ (x , y)

  g : (X → (Y → Z)) → X × Y → Z
  g γ (x , y) = γ x y

  gf : g ∘ f ∼ id
  gf = refl

  fg : f ∘ g ∼ id
  fg = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

more-dependent-curry : {X : Type} {Y : X → Type} {Z : (x : X) → Y x → Type}
                     → (((x , y) : (Σ x ꞉ X , Y x)) → Z x y)
                     ≅ ((x : X) (y : Y x) → Z x y)
more-dependent-curry {X} {Y} {Z} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (((x , y) : (Σ x ꞉ X , Y x)) → Z x y) → ((x : X) (y : Y x) → Z x y)
  f ϕ x y = ϕ (x , y)

  g : ((x : X) (y : Y x) → Z x y) → (((x , y) : (Σ x ꞉ X , Y x)) → Z x y)
  g γ (x , y) = γ x y

  gf : g ∘ f ∼ id
  gf = refl

  fg : f ∘ g ∼ id
  fg = refl

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

dependent-curry : {X : Type} {Y : X → Type} {Z : Type}
                → ((Σ x ꞉ X , Y x) → Z) ≅ ((x : X) (y : Y x) → Z)
dependent-curry = more-dependent-curry

dependent-curry' : {X : Type} {Y : X → Type} {Z : Type}
                 → ((Σ x ꞉ X , Y x) → Z) ≅ ((x : X) (y : Y x) → Z)
dependent-curry' {X} {Y} {Z} = more-dependent-curry {X} {Y} {λ _ _ → Z}

curry' : {X Y Z : Type} → (X × Y → Z) ≅ (X → (Y → Z))
curry' {X} {Y} {Z} = dependent-curry {X} {λ _ → Y} {Z}

curry'' : {X Y Z : Type} → (X × Y → Z) ≅ (X → (Y → Z))
curry'' = dependent-curry

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
binary-product-isomorphism funext A₀ A₁ =
 record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A₀ × A₁ → A₀ ×' A₁
  f (a₀ , a₁) 𝟎 = a₀
  f (a₀ , a₁) 𝟏 = a₁

  g : A₀ ×' A₁ → A₀ × A₁
  g ϕ = ϕ 𝟎 , ϕ 𝟏

  gf : g ∘ f ∼ id
  gf = refl

  fg : f ∘ g ∼ id
  fg ϕ = funext I
   where
    I : (n : 𝟚) → f (ϕ 𝟎 , ϕ 𝟏) n ≡ ϕ n
    I 𝟎 = refl (ϕ 𝟎)
    I 𝟏 = refl (ϕ 𝟏)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

We can define the types of lists from the type of vectors:

```agda
lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  List' : Type → Type
  List' A = Σ n ꞉ ℕ , Vector A n

  _:::_ : A → List' A → List' A
  x ::: (n , xs) = suc n , x :: xs

  f : List A → List' A
  f [] = 0 , []
  f (x :: xs) = x ::: f xs

  g : (Σ n ꞉ ℕ , Vector A n) → List A
  g (0 , []) = []
  g (suc n , x :: ys) = x :: g (n , ys)

  gf : g ∘ f ∼ id
  gf [] = refl []
  gf (x :: xs) = I
   where
    IH : g (f xs) ≡ xs
    IH = gf xs

    I : x :: g (f xs) ≡ x :: xs
    I = ap (x ::_) IH

-- Agda can't check that the following definition of fg terminates, so
-- we curry it to get fg', and then use fg' to define fg.

{-
  fg : f ∘ g ∼ id
  fg (0 , []) = refl (0 , [])
  fg (suc n , x :: ys) = I
   where
    IH : f (g (n , ys)) ≡ (n , ys)
    IH = fg (n , ys)

    I : (x ::: f (g (n , ys))) ≡ (x ::: (n , ys))
    I = ap (x :::_) IH
-}

  fg' : (n : ℕ) (ys : Vector A n) → f (g (n , ys)) ≡ (n , ys)
  fg' 0 [] = refl (0 , [])
  fg' (suc n) (x :: ys) = I
   where
    IH : f (g (n , ys)) ≡ (n , ys)
    IH = fg' n ys

    I : (x ::: f (g (n , ys))) ≡ (x ::: (n , ys))
    I = ap (x :::_) IH

  fg : f ∘ g ∼ id
  fg (n , ys) = fg' n ys

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```
The above trick is worth remember when Agda gives you "red" indicating that it fails to see that your recursive definition does terminate.

And the type of vectors from the type of lists:
```agda
{- This is done in subtypes.lagda.md
vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ (Σ xs ꞉ List A , length xs ≡ n)
vectors-from-lists {A} n = {!!}
-}
```
We leave the above deliberately unsolved, because it needs new material, to be developed soon, on equality of Sigma types, which is a bit tricky.
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

_:::_ : {A : Type} → A → List' A → List' A
x ::: (n , xs) = suc n , x ::' xs

```

```agda
vectors-in-basic-MLTT : {A : Type} (n : ℕ) → Vector A n ≅ Vector' A n
vectors-in-basic-MLTT {A} n =
 Isomorphism (f n) (Inverse (g n) (gf n) (fg n))
 where
  f : (n : ℕ) → Vector A n → Vector' A n
  f 0 [] = []' {A}
  f (suc n) (x :: xs) = x ::' f n xs

  g : (n : ℕ) → Vector' A n → Vector A n
  g 0 ⋆ = []
  g (suc n) (y , ys) = y :: g n ys

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf 0 [] = refl []
  gf (suc n) (x :: xs) = goal
   where
    IH : g n (f n xs) ≡ xs
    IH = gf n xs

    goal : x :: g n (f n xs) ≡ x :: xs
    goal = ap (x ::_) IH

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg 0 ⋆ = refl ⋆
  fg (suc n) (y , ys) = I
   where
    IH : f n (g n ys) ≡ ys
    IH = fg n ys

    I : (y , f n (g n ys)) ≡ (y , ys)
    I = ap (y ,_) IH

lists-in-basic-MLTT : {A : Type} → List A ≅ List' A
lists-in-basic-MLTT {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → List' A
  f [] = 0 , []' {A}
  f (x :: xs) = x ::: f xs

  g : List' A → List A
  g (0 , xs) = []
  g (suc n , x , xs) = x :: g (n , xs)

  gf : g ∘ f ∼ id
  gf [] = refl []
  gf (x :: xs) = ap (x ::_) (gf xs)

  fg : f ∘ g ∼ id
  fg (0 , xs) = refl (0 , ⋆)
  fg (suc n , x , xs) = ap (x :::_) (fg (n , xs))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

**Exercise.** Last week we saw various possible definitions of the
              type of vectors. Prove that all of them are isomorphic.

```agda
open import Fin
open import Fin-functions hiding (Fin-isomorphism)

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = Isomorphism (f n) (Inverse (g n) (gf n) (fg n))
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero = zero'
  f (suc n) (suc x) = suc' (f n x)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr y) = suc (g n y)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero = refl zero
  gf (suc n) (suc x) = ap suc IH
   where
    IH : g n (f n x) ≡ x
    IH = gf n x

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr y) = ap inr (fg n y)
```
