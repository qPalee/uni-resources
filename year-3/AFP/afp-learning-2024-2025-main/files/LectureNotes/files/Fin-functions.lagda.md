<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin-functions where

open import prelude
```
-->

# Isomorphism of Fin n with a Basic MLTT type

```agda
Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

open import Fin
open import isomorphisms

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = zero'
  f (suc n) (suc k) = suc' (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = γ
   where
    IH : g n (f n k) ≡ k
    IH = gf n k

    γ = g (suc n) (f (suc n) (suc k)) ≡⟨ refl _ ⟩
        g (suc n) (suc' (f n k))      ≡⟨ refl _ ⟩
        suc (g n (f n k))             ≡⟨ ap suc IH ⟩
        suc k                         ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr k) = γ
   where
    IH : f n (g n k) ≡ k
    IH = fg n k

    γ = f (suc n) (g (suc n) (suc' k)) ≡⟨ refl _ ⟩
        f (suc n) (suc (g n k))        ≡⟨ refl _ ⟩
        suc' (f n (g n k))             ≡⟨ ap suc' IH ⟩
        suc' k                         ∎

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```

**Exercise.** Show that the type `Fin n` is isormorphic to the type `Σ k : ℕ , k < n`.

# Fin n has decidable equality

```agda
open import decidability
open import negation

Fin-zero-is-not-suc : {n : ℕ} (y : Fin n) → zero ≢ suc y
Fin-zero-is-not-suc {n} y ()

Fin-suc-is-not-zero : {n : ℕ} (x : Fin n) → suc x ≢ zero
Fin-suc-is-not-zero {n} x e = Fin-zero-is-not-suc x (sym e)

Fin-pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
Fin-pred {n} zero = zero
Fin-pred {n} (suc x) = x

Fin-suc-injective : {n : ℕ} (x y : Fin n) → suc x ≡ suc y → x ≡ y
Fin-suc-injective {n} zero zero e = refl zero
Fin-suc-injective {suc n} (suc x) (suc y) e = ap Fin-pred e

Fin-has-decidable-equality : {n : ℕ} (x y : Fin n) → is-decidable (x ≡ y)
Fin-has-decidable-equality {n} zero zero = inl (refl zero)
Fin-has-decidable-equality {n} zero (suc y) = inr (Fin-zero-is-not-suc y)
Fin-has-decidable-equality {n} (suc x) zero = inr (Fin-suc-is-not-zero x)
Fin-has-decidable-equality {suc n} (suc x) (suc y) =
 map-decidable
  (ap suc)
  (Fin-suc-injective x y)
  (Fin-has-decidable-equality x y)
```

# argmin

```
open import natural-numbers-functions

argmin-existence : {k : ℕ} (p : Fin (suc k) → ℕ)
                 → Σ x ꞉ Fin (suc k) , ((y : Fin (suc k)) → p x ≤ p y)
argmin-existence {0} p = zero , α
 where
  α : (y : Fin 1) → p zero ≤ p y
  α zero = ≤-refl (p zero)
argmin-existence {suc k} p = γ
 where
  IH : Σ x ꞉ Fin (suc k) , ((y : Fin (suc k)) → p (suc x) ≤ p (suc y))
  IH = argmin-existence {k} (p ∘ suc)

  x = fst IH
  ϕ = snd IH

  γ : Σ x' ꞉ Fin (suc (suc k)) , ((y : Fin (suc (suc k))) → p x' ≤ p y)
  γ = h (≤-decidable (p zero) (p (suc x)))
   where
    h : is-decidable (p zero ≤ p (suc x)) → type-of γ
    h (inl l) = zero , α
     where
      α : (y : (Fin (suc (suc k)))) → p zero ≤ p y
      α zero    = ≤-refl (p zero)
      α (suc y) = ≤-trans (p zero) (p (suc x)) (p (suc y)) l (ϕ y)
    h (inr ν) = suc x , α
     where
      α : (y : (Fin (suc (suc k)))) → p (suc x) ≤ p y
      α zero    = ¬-≤-flip (p zero) (p (suc x)) ν
      α (suc y) = ϕ y


argmin : {k : ℕ} → (Fin (suc k) → ℕ) → Fin (suc k)
argmin p = fst (argmin-existence p)

argmin-property : {k : ℕ}
                  (p : Fin (suc k) → ℕ)
                  (y : Fin (suc k))
                → p (argmin p) ≤ p y
argmin-property p = snd (argmin-existence p)
```

# Counting

```
Bool-to-ℕ : Bool → ℕ
Bool-to-ℕ true  = 1
Bool-to-ℕ false = 0

Bool-to-ℕ-property₀ : (b : Bool) → Bool-to-ℕ b ≡ 0 → b ≡ false
Bool-to-ℕ-property₀ false e = refl false

Bool-to-ℕ-property₁ : (b : Bool) → Bool-to-ℕ b ≡ 1 → b ≡ true
Bool-to-ℕ-property₁ true e = refl true

count-true : {n : ℕ} → (Fin n → Bool) → ℕ
count-true {0} f = 0
count-true {suc n} f = Bool-to-ℕ (f zero) + count-true {n} (f ∘ suc)

count-true-zero-implies-all-false : (n : ℕ)
                                    (f : Fin n → Bool)
                                  → count-true f ≡ 0
                                  → (k : Fin n) → f k ≡ false
count-true-zero-implies-all-false (suc n) f e zero = goal
 where
  e₀ : Bool-to-ℕ (f zero) ≡ 0
  e₀ = zero-addition-gives-left-zero (Bool-to-ℕ (f zero)) (count-true (f ∘ suc)) e

  goal : f zero ≡ false
  goal = Bool-to-ℕ-property₀ (f zero) e₀

count-true-zero-implies-all-false (suc n) f e (suc k) = IH
 where
  e₁ : count-true (f ∘ suc) ≡ 0
  e₁ = zero-addition-gives-right-zero (Bool-to-ℕ (f zero)) (count-true (f ∘ suc)) e

  IH : f (suc k) ≡ false
  IH = count-true-zero-implies-all-false n (f ∘ suc) e₁ k
```
