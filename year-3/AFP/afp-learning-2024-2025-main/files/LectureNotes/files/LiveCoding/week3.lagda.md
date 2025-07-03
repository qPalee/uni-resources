# Lecture Notes - Week 3

Eric Finster, Feb 4-5 2025.

```
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week3 where

open import prelude
open import List-functions
```

## Replacing Booleans with Types

```
-- Conjunction
andBool : Bool → Bool → Bool
andBool true y = y
andBool false y = false

andType : Type → Type → Type
andType X Y = X × Y

-- Disjunction
orBool : Bool → Bool → Bool
orBool true y = true
orBool false y = y 

orType : Type → Type → Type
orType X Y = X ∔ Y

-- Implication
impliesBool : Bool → Bool → Bool
impliesBool true true = true
impliesBool true false = false
impliesBool false y = true

impliesType : Type → Type → Type
impliesType X Y = X → Y 

-- Constants
trueBool : Bool
trueBool = true 

trueType : Type
trueType = 𝟙

falseBool : Bool
falseBool = false

falseType : Type
falseType = 𝟘

-- Quantification?
forallBool : (A : Type) (P : A → Bool) → Bool
forallBool A P = {!!}

forallType : (A : Type) (P : A → Type) → Type
forallType A P = (a : A) → P a

existsBool : (A : Type) (P : A → Bool) → Bool
existsBool A P = {!!}

existsType : (A : Type) (P : A → Type) → Type
existsType A P = Σ a ꞉ A , P a

```

Propositions as types = replace "truth" (i.e. booleans) with "provability" (elements of types) 

# Predicates and Relations

### Haskell
 1. Predicate : A → Bool  (example: even :: Int → Bool)
 2. Relation : A → A → Bool (example: Eq a  (==) :: a → a → Bool)

### Agda
 1. Predicate : A → Type
 2. Relation : A → A → Type 

#  Decidability

```
is-decidable : Type → Type 
is-decidable A = A ∔ ¬ A

is-decidable-predicate : {A : Type} (P : A → Type) → Type
is-decidable-predicate {A} P = (a : A) → is-decidable (P a) 

is-decidable-relation : {A : Type} (R : A → A → Type) → Type
is-decidable-relation {A} R = (a₀ a₁ : A) → is-decidable (R a₀ a₁) 

-- Examples
ℕ-decidable : is-decidable ℕ
ℕ-decidable = inl (suc (suc zero)) 

𝟙-decidable : is-decidable 𝟙
𝟙-decidable = inl ⋆

𝟘-decidable : is-decidable 𝟘
𝟘-decidable = inr (λ z → z)

-- A non-decidable relation
eq-ℕ-Bool : (ℕ → Bool) → (ℕ → Bool) → Type
eq-ℕ-Bool f g = f ≡ g 


-- Characterization of decidability

false-is-not-true : false ≡ true → 𝟘
false-is-not-true ()

true-is-not-false : true ≡ false → 𝟘
true-is-not-false () 

thm : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
thm A = to , from 

  where
    to : is-decidable A → Sigma Bool (λ b → A ⇔ b ≡ true)
    to (inl a) = true , α , β
      where
        α : A → true ≡ true
        α _ = refl _

        β : true ≡ true → A
        β _ = a 

    to (inr ¬a) = false , α , β

      where
        α : A → false ≡ true
        α a = 𝟘-nondep-elim (¬a a) 

        β : false ≡ true → A
        β ft = 𝟘-nondep-elim (false-is-not-true ft)
        
    from : Sigma Bool (λ b → A ⇔ b ≡ true) → is-decidable A
    from (true , ϕ , ψ) = inl (ψ (refl true))
    from (false , ϕ , ψ) = inr (λ a → false-is-not-true (ϕ a))
    
```

# Decidable Predicates and Relations

```
thm-predicate : {A : Type} (P : A → Type)
  → is-decidable-predicate P ⇔ Σ Q ꞉ (A → Bool) , ((a : A) → P a ⇔ (Q a ≡ true))
thm-predicate = {!!}


```

## Decidability of Equality

```
has-decidable-equality : Type → Type 
has-decidable-equality A = is-decidable-relation (_≡_ {A})

Bool-has-decidable-equaltiy : has-decidable-equality Bool
Bool-has-decidable-equaltiy true true = inl (refl _)
Bool-has-decidable-equaltiy true false = inr true-is-not-false
Bool-has-decidable-equaltiy false true = inr false-is-not-true
Bool-has-decidable-equaltiy false false = inl (refl false)

zero-is-not-suc : {m : ℕ} → zero ≡ suc m → 𝟘
zero-is-not-suc ()

suc-is-not-zero : {m : ℕ} → suc m ≡ zero → 𝟘
suc-is-not-zero ()

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality zero zero = inl (refl zero)
ℕ-has-decidable-equality zero (suc n) = inr zero-is-not-suc
ℕ-has-decidable-equality (suc m) zero = inr suc-is-not-zero
ℕ-has-decidable-equality (suc m) (suc n) = 
  ∔-nondep-elim
    (λ m≡n → inl (ap suc m≡n))
    (λ ¬m≡n → inr (λ sm≡sn → ¬m≡n (ap pred sm≡sn)))
    IH
  
  where
    IH : (m ≡ n) ∔ ¬ (m ≡ n)
    IH = ℕ-has-decidable-equality m n 

-- Claim from above:
-- ℕ→Bool-not-has-decidable-equality : ¬ (has-decidable-equality (ℕ → Bool))
-- ℕ→Bool-not-has-decidable-equality = {!!} 

```

# Defining predicates and Relations

## Even Numbers

```
is-even : ℕ → Type
is-even n = Σ k ꞉ ℕ , 2 * k ≡ n

check-even : ℕ → Bool
check-even zero = true
check-even (suc zero) = false
check-even (suc (suc n)) = check-even n 

is-even₀ : ℕ → Type
is-even₀ zero = 𝟙
is-even₀ (suc zero) = 𝟘
is-even₀ (suc (suc n)) = is-even₀ n

is-even₁ : ℕ → Type
is-even₁ n = check-even n ≡ true

data is-even₂ : ℕ → Type where
  zero-is-even : is-even₂ zero
  suc-suc-is-even : {n : ℕ} → is-even₂ n → is-even₂ (suc (suc n))

4-is-even : is-even 4
4-is-even = 2 , refl 4

4-is-even₀ : is-even₀ 4
4-is-even₀ = ⋆

4-is-even₁ : is-even₁ 4
4-is-even₁ = refl true

4-is-even₂ : is-even₂ 4
4-is-even₂ = suc-suc-is-even (suc-suc-is-even zero-is-even) 

evens : Type
evens = Σ n ꞉ ℕ , is-even n  

```

## Vectors

```

is-of-length₀ : {A : Type} → ℕ → List A → Type
is-of-length₀ zero [] = 𝟙
is-of-length₀ zero (_ :: _) = 𝟘
is-of-length₀ (suc n) [] = 𝟘
is-of-length₀ (suc n) (_ :: xs) = is-of-length₀ n xs


is-of-length₁ : {A : Type} → ℕ → List A → Type
is-of-length₁ n xs = length xs ≡ n

data is-of-length₂ {A : Type} : ℕ → List A → Type where
  empty-has-length-zero : is-of-length₂ zero []
  cons-has-length-suc : {n : ℕ} (x : A) (xs : List A)
    → is-of-length₂ n xs
    → is-of-length₂ (suc n) (x :: xs)

Vec₀ : (A : Type) → ℕ → Type
Vec₀ A n = Σ xs ꞉ List A , is-of-length₀ n xs

data Vec (A : Type) : ℕ → Type where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n) 

ex₀ : Vec₀ ℕ 2
ex₀ = 0 :: 3 :: [] , ⋆

ex₁ : Vec ℕ 2
ex₁ = 0 :: 3 :: [] 

Fin₀ : ℕ → Type
Fin₀ zero = 𝟘
Fin₀ (suc n) = 𝟙 ∔ (Fin₀ n) 

fin2-0 : Fin₀ 2
fin2-0 = inl ⋆

fin2-1 : Fin₀ 2
fin2-1 = inr (inl ⋆)

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

fin2-0' : Fin 2
fin2-0' = zero

fin2-1' : Fin 2
fin2-1' = suc zero 
  
Vec₁ : (A : Type) → ℕ → Type
Vec₁ A n = Fin n → A 

```

