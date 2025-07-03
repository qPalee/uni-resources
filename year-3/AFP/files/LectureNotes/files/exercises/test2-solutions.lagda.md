# Test 2

```agda
{-# OPTIONS --without-K --auto-inline --safe #-}

module exercises.test2-solutions where

open import prelude
open import function-extensionality
open import isomorphisms
open import subtypes
open import BST
open import partial-orders
open import List-functions
```
## Test Instructions.

 1. The test is 1hr 50min long.
 1. Make sure you submit on Canvas from time to time. The last submission will be marked.
 1. Submissions close at 12:50 sharp.
 1. Late submissions are strictly not accepted.
 1. Make sure you give Canvas time to process your submission. The submission time is included in the time allocated for the test.
 1. Please check your Canvas submission after you have submitted.
 1. RAP students get extra time as usual (to be set on Canvas) based on the information that the Welfare Team sends us.
 1. You will need to sign attendance in the lab (in addition to the university online attendance).
 1. You need to **bring your student id** and have it on the desk for us to check.
 1. You should use your own machine. (You can also use one of the 6 lab machines, if you wish, provided you installed Agda in advance.)
 1. The test is open book.
    * You are allowed to use the module material on GitLab. This includes sample solutions.
    * You are allowed to use the Agda manual online, as well as the emacs cheatsheet and the resources we gave you on GitLab.
    * You are allowed to use your own solutions and notes.
 1. What you are **not** allowed.
    *  You are **not** allowed to use your phone (other than for authentication at the beginning of the test), google search, stackoverflow, chat, email etc.
    * Please put your phone on silent mode inside your bag under the table.
    * You are **not** allowed to use any kind of AI.
 1. By signing the attendance sheet, you declare that you are submitting your own work.

## Question 1 

Consider the following definition of a prefix relation `_≼_` on lists:

```agda
data _≼_ {X : Type} : List X → List X → Type where
  []-≼ : {ys : List X} → [] ≼ ys
  ::-≼ : (x : X) {xs ys : List X} → xs ≼ ys → (x :: xs) ≼ (x :: ys)
```

For example, we have 

```agda
example : (2 :: 5 :: []) ≼ (2 :: 5 :: 14 :: [])
example = ::-≼ 2 (::-≼ 5 []-≼)

counter-example : ¬ ((2 :: 5 :: []) ≼ (14 :: 2 :: 5 :: []))
counter-example ()
```
Show that this relation is reflexive and transitive.

```agda
≼-reflexive : {X : Type} (xs : List X) → xs ≼ xs
≼-reflexive [] = []-≼
≼-reflexive (x :: xs) = ::-≼ x (≼-reflexive xs)

≼-transitive : {X : Type} {xs ys zs : List X} → xs ≼ ys  → ys ≼ zs → xs ≼ zs
≼-transitive []-≼ β = []-≼
≼-transitive (::-≼ x α) (::-≼ .x β) = ::-≼ x (≼-transitive α β)
```

## Question 2

Show that `xs ≼ ys` implies that we can find a list `zs` such that `xs ++ zs ≡ ys`.

```agda
≼-is-prefix : {X : Type} (xs ys : List X) → xs ≼ ys → Σ zs ꞉ List X , xs ++ zs ≡ ys 
≼-is-prefix .[] ys []-≼ = ys , (refl _)
≼-is-prefix (x :: xs) (x :: ys) (::-≼ x α) =
  let (zs , e) = ≼-is-prefix xs ys α in
  zs , ap (x ::_) e
```

## Question 3

(a) Show that if funext holds, negated types are props.

```agda
¬-are-props : FunExt → (X : Type) → is-prop (¬ X)
¬-are-props fe X α β = fe (λ x → 𝟘-nondep-elim (α x)) 
```

(b) Using the above, show that < is prop valued for any partial order.

```agda
module _ (X : Type) (ρ : PartialOrder X) where

  open PartialOrder ρ 

  <-is-prop : FunExt → (x y : X) → is-prop (x < y)
  <-is-prop fe x y = ×-is-prop (≤-is-prop x y) (¬-are-props fe (x ≡ y)) 
```

## Question 4

Complete the following record `BST-deletion-spec` to specify the
intended behavior of the operation `delete : BST → X → BST` that
removes a single given element from the given BST.  You **do not**
need to provide an instance, only define the record.

You might want to look at the specifications of
[sorting](../sorting.lagda.md) and
[bijections](../isomorphisms.lagda.md) for inspiration.

```agda
record BST-deletion-spec (X : Type) (ρ : PartialOrder X) (trichotomy : trichotomous ρ) : Type where
  open first-approach X ρ trichotomy 
  field
    delete : BST → X → BST
    delete-deletes : (x : X) (t : BST) → ¬ (x ∈ₛ' delete t x)
    delete-preserves : (x y : X) (t : BST) → ¬ (x ≡ y) → (y ∈ₛ' t) ≅ (y ∈ₛ' (delete t x))
```

## Question 5

Finish the proof that `_≼_` is a partial order.

```agda
module _ (X : Type) (X-is-set : is-set X) where

  ≼-tail : {x y : X} {xs ys : List X} → (x :: xs) ≼ (y :: ys) → xs ≼ ys
  ≼-tail (::-≼ x α) = α

  ≼-head : {x y : X} {xs ys : List X} → (x :: xs) ≼ (y :: ys) → x ≡ y
  ≼-head (::-≼ x α) = refl x

  ≼-antisymmetric : {xs ys : List X} → (xs ≼ ys) × (ys ≼ xs) → xs ≡ ys
  ≼-antisymmetric {[]}      {[]}      (α , β) = refl []
  ≼-antisymmetric {x :: xs} {y :: ys} (α , β) =
   ap₂ _::_ (≼-head α) (≼-antisymmetric(≼-tail α , ≼-tail β))

  ≼-η-rule : {x y : X} {xs ys : List X} (α : (x :: xs) ≼ (y :: ys))
      → α ≡ transport (λ z → (x :: xs) ≼ (z :: ys)) (≼-head α) (::-≼ x (≼-tail α))
  ≼-η-rule (::-≼ x α) = refl (::-≼ x α)

  ≼-is-prop : (xs ys : List X) → is-prop (xs ≼ ys)
  ≼-is-prop [] ys []-≼ []-≼ = refl []-≼
  ≼-is-prop (x :: xs) (y :: ys) α β =
   α ≡⟨ ≼-η-rule α ⟩
   transport (λ z → (x :: xs) ≼ (z :: ys)) (≼-head α) (::-≼ x (≼-tail α))
     ≡⟨ ap₂ (λ p q → transport (λ z → (x :: xs) ≼ (z :: ys)) p (::-≼ x q)) aux IH ⟩
   transport (λ z → (x :: xs) ≼ (z :: ys)) (≼-head β) (::-≼ x (≼-tail β))
     ≡⟨ sym (≼-η-rule β) ⟩
   β ∎
   where
    aux : ≼-head α ≡ ≼-head β
    aux = X-is-set x y (≼-head α) (≼-head β)

    IH : ≼-tail α ≡ ≼-tail β
    IH = ≼-is-prop xs ys (≼-tail α) (≼-tail β)


  ≼-univalent : {xs ys : List X} (p : xs ≡ ys) →
                ≼-antisymmetric (≡-nondep-elim (λ xs ys → (xs ≼ ys) × (ys ≼ xs))
                                         (λ xs → ≼-reflexive xs , ≼-reflexive xs)
                                         xs ys p)
                ≡ p
  ≼-univalent {[]}      (refl [])        = refl (refl [])
  ≼-univalent {x :: xs} (refl (x :: xs)) =
   ap₂ _::_ (refl x) (≼-antisymmetric (≼-reflexive xs , ≼-reflexive xs)) ≡⟨ aux ⟩
   ap₂ _::_ (refl x) (refl xs)                                 ≡⟨ refl _ ⟩
   refl (x :: xs)                                              ∎

   where
    IH : ≼-antisymmetric(≼-reflexive xs , ≼-reflexive xs) ≡ refl xs
    IH = ≼-univalent (refl xs)

    aux = ap (ap₂ _::_ (refl x)) IH

  prefix-PartialOrder : PartialOrder (List X)
  prefix-PartialOrder = record
                         { _≤_           = _≼_
                         ; ≤-is-prop     = ≼-is-prop
                         ; reflexive     = ≼-reflexive
                         ; transitive    = ≼-transitive
                         ; antisymmetric = ≼-antisymmetric
                         ; univalent     = ≼-univalent
                         }
```
