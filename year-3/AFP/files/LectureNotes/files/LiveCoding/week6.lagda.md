<!--
```agda
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week6 where
open import prelude
open import natural-numbers-functions
open import List-functions
open import unit-type
open import Maybe
```
-->

# Everything About The Fin Type 

```agda
Fin' : ℕ → Type
Fin' zero = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

zero₃ : Fin 3
zero₃ = zero

one₃ : Fin 3
one₃ = suc zero


data Vec (A : Type) : ℕ → Type where
  [] : Vec A 0
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vhead : {A : Type} {n : ℕ} → Vec A (suc n) → A
vhead (x :: v) = x

_!!_ : {A : Type} → List A → ℕ → Maybe A
[] !! zero = nothing
(x :: xs) !! zero = just x
[] !! suc n = nothing
(x :: xs) !! suc n = xs !! n

_!!v_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A
(x :: xs) !!v zero = x
(x :: xs) !!v suc f = xs !!v f

```

```agda
const-true : (n : ℕ) → Vec Bool n
const-true zero = []
const-true (suc n) = true :: const-true n

no-empty-vect-pi : ¬ ((n : ℕ) → Vec 𝟘 n)
no-empty-vect-pi ϕ = vhead (ϕ (suc zero)) 
```

# Review of Subtypes

```agda
is-property : Type → Type
is-property X = (x y : X) → x ≡ y

```

# Monads

## The definition

```agda

--  classs Mnd m where
--    return :: a -> m a
--    bind :: m a -> (a -> m b) -> m b 

record Monad (M : Type → Type) : Type₁ where
  field
    ret : {A : Type} → A → M A
    bind : {A B : Type} →
      M A → (A → M B) → M B 

open Monad

record MonadLaws (M : Type → Type) (μ : Monad M) : Type₁ where
  field
  
    ret-right : {A B : Type} (a : A) (f : A → M B)
      → bind μ (ret μ a) f ≡ f a

    ret-left : {A : Type} (m : M A)
     → bind μ m (ret μ ) ≡ m

    bind-assoc : {A B C : Type} (m : M A)
      → (f : A → M B) (g : B → M C)
      → bind μ (bind μ m f) g  ≡ bind μ m (λ a → bind μ (f a) g)
    
open MonadLaws

```

## The List Monad

```agda

List-ret : {A : Type} → A → List A
List-ret a = a :: []

List-bind : {A B : Type} →
    List A → (A → List B) → List B
List-bind [] f = []
List-bind (x :: xs) f = f x ++ List-bind xs f
      
List-Monad : Monad List
ret List-Monad = List-ret
bind List-Monad = List-bind


List-ret-right : ∀ {A} {B} (a : A) (f : A → List B) →
                 bind List-Monad (ret List-Monad a) f ≡ f a
List-ret-right a f = []-right-neutral (f a)                  

List-ret-left : ∀ {A} (m : List A) →
                bind List-Monad m (ret List-Monad) ≡ m
List-ret-left [] = refl _
List-ret-left (x :: xs) = ap (λ y → x :: y)  (List-ret-left xs) 

List-bind-assoc : ∀ {A} {B} {C} (m : List A) (f : A → List B)
                    (g : B → List C) →
                  bind List-Monad (bind List-Monad m f) g ≡
                  bind List-Monad m (λ a → bind List-Monad (f a) g)
List-bind-assoc [] f g = refl _
List-bind-assoc (x :: m) f g =
  List-bind (f x ++ List-bind m f) g ≡⟨ {!!} ⟩
  List-bind (f x) g ++ List-bind (List-bind m f) g ≡⟨ ap (λ y → List-bind (f x) g ++ y) (List-bind-assoc m f g) ⟩ 
  List-bind (f x) g ++ List-bind m (λ a → List-bind (f a) g) ∎ 


List-Monad-Laws : MonadLaws List List-Monad
ret-right List-Monad-Laws = List-ret-right
ret-left List-Monad-Laws = List-ret-left
bind-assoc List-Monad-Laws = List-bind-assoc

```






