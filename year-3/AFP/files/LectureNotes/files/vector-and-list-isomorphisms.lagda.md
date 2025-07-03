<!--
```agda
{-# OPTIONS --without-K --safe #-}

module vector-and-list-isomorphisms where

open import prelude
```
-->
# Vector and list isomorphisms

We will do this handout in the lab. We will solve some of the problems, and you will solve the remaining ones.

## The type of lists can be defined from that of vectors

```agda
open import isomorphisms

lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → Σ n ꞉ ℕ , Vector A n
  f [] = 0 , []
  f (x :: xs) = goal
   where
    IH : Σ n ꞉ ℕ , Vector A n
    IH = f xs
    goal : Σ n ꞉ ℕ , Vector A n
    goal = suc (fst IH) , x :: snd (IH)

  g : (Σ n ꞉ ℕ , Vector A n) → List A
  g (0 , []) = []
  g (suc n , x :: xs) = x :: g (n , xs)

  gf : g ∘ f ∼ id
  gf = {!!}

  fg : f ∘ g ∼ id
  fg (0 , []) = refl _
  fg (suc n , x :: xs) = {!!}
   where
    IH : f (g (n , xs)) ≡ (n , xs)
    IH = fg (n , xs)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

## The type of vectors can be defined from that of lists

```agda
open import List-functions

vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ (Σ xs ꞉ List A , (length xs ≡ n))
vectors-from-lists {A} n = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : {!!} → {!!}
  f = {!!}

  g : {!!} → {!!}
  g = {!!}

  gf : g ∘ f ∼ id
  gf = {!!}

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

## The types of lists and vectors can be defined in basic MLTT

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
vectors-in-basic-MLTT {A} n = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : {!!} → {!!}
  f = {!!}

  g : {!!} → {!!}
  g = {!!}

  gf : g ∘ f ∼ id
  gf = {!!}

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

```
lists-in-basic-MLTT : {A : Type} → List A ≅ List' A
lists-in-basic-MLTT {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : {!!} → {!!}
  f = {!!}

  g : {!!} → {!!}
  g = {!!}

  gf : g ∘ f ∼ id
  gf = {!!}

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
