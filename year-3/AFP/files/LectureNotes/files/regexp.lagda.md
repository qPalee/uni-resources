<!--
```agda
{-# OPTIONS --without-K --safe #-}
module regexp where

open import prelude
open import isomorphisms
open import List
open import List-functions
open import Maybe
open import decidability

open Maybe-Monad
```
-->

# Regular Expressions

This is based on the paper [Intrinsic Verification of a Regular Expression Matcher](https://dlicata.wescreates.wesleyan.edu/pubs/ktl16regexp/ktl16regexp.pdf).

We start by defining our basic regular expressions.  The type `A` here
will serve as the alphabet.  Because we will want to compare elements
of `A` for equality later on, we also assume that `A` has decidable
equality.


```agda
module Regexp (A : Type) (compare : has-decidable-equality A) where

  data RegExp : Type where
    ∅ : RegExp
    `_ : A → RegExp
    _·_ : RegExp → RegExp → RegExp
    _∪_ : RegExp → RegExp → RegExp
    _+ : RegExp → RegExp

```

```agda
  data _accepts_ : RegExp → List A → Type where

    acc-` : (a : A) → (` a) accepts (a :: [])

    acc-∙ : {ρ σ : RegExp} {as bs : List A}
      → ρ accepts as
      → σ accepts bs
      → (ρ · σ) accepts (as ++ bs)

    acc-∪-inl : {ρ σ : RegExp} {as : List A}
      → ρ accepts as → (ρ ∪ σ) accepts as
    acc-∪-inr : {ρ σ : RegExp} {as : List A}
      → σ accepts as → (ρ ∪ σ) accepts as

    acc-+-one : {ρ : RegExp} {as : List A}
      → ρ accepts as
      → (ρ +) accepts as
    acc-+-many : {ρ : RegExp} {as bs : List A}
      → ρ accepts as
      → (ρ +) accepts bs
      → (ρ +) accepts (as ++ bs)

  String : Type
  String = List A

  Stack : Type
  Stack = List RegExp

  _stack-accepts_ : Stack → String → Type

  record MatchResult (ρ : RegExp) (ρs : List RegExp) (inp : List A) : Type where
    constructor ⟪_,_,_,_,_⟫
    inductive
    eta-equality
    field
      hd : List A
      tl : List A
      hd-acc : ρ accepts hd
      tl-acc : ρs stack-accepts tl
      recons : inp ≡ hd ++ tl

  open MatchResult

  [] stack-accepts [] = 𝟙
  [] stack-accepts (_ :: _) = 𝟘
  (ρ :: ρs) stack-accepts inp = MatchResult ρ ρs inp

  match : (ρ : RegExp) (ρs : List RegExp) (inp : List A) → Maybe (MatchResult ρ ρs inp)
  match-stack : (ρs : List RegExp) (inp : List A) → Maybe (ρs stack-accepts inp)

  match ∅ ρs inp = nothing
  match (` x) ρs [] = nothing
  match (` x) ρs (y :: inp) = ∔-nondep-elim eq-case neq-case (compare x y)

    where eq-case : x ≡ y → Maybe (MatchResult (` x) ρs (y :: inp))
          eq-case x≡y = match-stack ρs inp >>= (λ ρs-acc-inp →
            just ⟪ (x :: []) , inp , acc-` x , ρs-acc-inp , ap (λ z → z :: inp) (sym x≡y) ⟫)

          neq-case : ¬ (x ≡ y) → Maybe (MatchResult (` x) ρs (y :: inp))
          neq-case _ = nothing

  match (ρ · σ) ρs inp =
    match ρ (σ :: ρs) inp >>= λ mr →

      let eq = inp                                         ≡⟨ recons mr ⟩
               hd mr ++ tl mr                              ≡⟨ ap (λ z → hd mr ++ z) (recons (tl-acc mr)) ⟩
               hd mr ++ hd (tl-acc mr) ++ tl (tl-acc mr)   ≡⟨ sym (++-assoc (hd mr) (hd (tl-acc mr)) (tl (tl-acc mr))) ⟩
               (hd mr ++ hd (tl-acc mr)) ++ tl (tl-acc mr) ∎ in

      just ⟪ hd mr ++ hd (tl-acc mr)
           , tl (tl-acc mr)
           , acc-∙ (hd-acc mr) (hd-acc (tl-acc mr))
           , tl-acc (tl-acc mr)
           , eq ⟫

  match (ρ ∪ σ) ρs inp =
    (match ρ ρs inp >>= λ mr → just ⟪ hd mr , tl mr , acc-∪-inl (hd-acc mr) , tl-acc mr , recons mr ⟫) orElse
    (match σ ρs inp >>= λ mr → just ⟪ hd mr , tl mr , acc-∪-inr (hd-acc mr) , tl-acc mr , recons mr ⟫)

  match (ρ +) ρs inp =
    (match ρ ρs inp >>= λ mr → just ⟪ hd mr , tl mr , acc-+-one (hd-acc mr) , tl-acc mr , recons mr ⟫) orElse
    (match ρ ((ρ +) :: ρs) inp >>= λ mr →

      let eq = inp                                         ≡⟨ recons mr ⟩
               hd mr ++ tl mr                              ≡⟨ ap (λ z → hd mr ++ z) (recons (tl-acc mr)) ⟩
               hd mr ++ hd (tl-acc mr) ++ tl (tl-acc mr)   ≡⟨ sym (++-assoc (hd mr) (hd (tl-acc mr)) (tl (tl-acc mr))) ⟩
               (hd mr ++ hd (tl-acc mr)) ++ tl (tl-acc mr) ∎ in

      just ⟪ hd mr ++ hd (tl-acc mr)
           , tl (tl-acc mr)
           , acc-+-many (hd-acc mr) (hd-acc (tl-acc mr))
           , tl-acc (tl-acc mr)
           , eq ⟫)

  match-stack [] [] = just ⋆
  match-stack [] (x :: inp) = nothing
  match-stack (ρ :: ρs) inp = match ρ ρs inp


module Example where

  data Alph : Type where
    A : Alph
    B : Alph

  compare-Alph : has-decidable-equality Alph
  compare-Alph A A = inl (refl _)
  compare-Alph A B = inr λ { () }
  compare-Alph B A = inr λ { () }
  compare-Alph B B = inl (refl _)

  open Regexp Alph compare-Alph

  AorB : RegExp
  AorB = (((` A) ∪ (` B)) +)

  example : AorB accepts (A :: A :: B :: [])
  example = acc-+-many (acc-∪-inl (acc-` A))
            (acc-+-many ((acc-∪-inl (acc-` A)))
            (acc-+-one (acc-∪-inr (acc-` B))))
```
