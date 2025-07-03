<!--
```agda
{-# OPTIONS --without-K --safe #-}

module quick-sort-lemmas where 

open import prelude
open import List-functions
open import isomorphisms
open import isomorphism-functions
open import iso-utils
open import strict-total-order
open import sorting

open _IsPermutationOf_
open _≅_
open is-bijection

```
-->

## Positions in Concatenated Lists

First, we will need to know that the positions of the concatenation of
two lists are isomorphic to just the binary sum of the positions of
the individual lists.  This is straightforward to prove by induction
using the various binary sum isomorphisms defined in
[iso-utils](iso-utils.lagda.md).

```agda
++-pos : {X : Type} (xs ys : List X) →
  Pos (xs ++ ys) ≅ Pos xs ∔ Pos ys
++-pos [] ys = ∔-unit-left-iso (Pos ys)
++-pos (x :: xs) ys =
  Pos ((x :: xs) ++ ys) ≅⟨ ∔-pair-iso (id-iso 𝟙) (++-pos xs ys) ⟩
  𝟙 ∔ (Pos xs ∔ Pos ys) ≅⟨ ∔-assoc-iso 𝟙 (Pos xs) (Pos ys) ⟩ 
  Pos (x :: xs) ∔ Pos ys ∎ᵢ

←-++-pos : {X : Type} (xs ys : List X) → Pos xs ∔ Pos ys → Pos (xs ++ ys)
←-++-pos xs ys = inverse (bijectivity (++-pos xs ys ))

→-++-pos : {X : Type} (xs ys : List X) → Pos (xs ++ ys) → Pos xs ∔ Pos ys 
→-++-pos xs ys = bijection (++-pos xs ys)
```

We also prove two lemmas about how the inhabitants are compatible with
the previous isomorphism.

```agda
++-inhab-inl : {X : Type} (xs ys : List X) (p : Pos xs)
  → Inhab (xs ++ ys) (←-++-pos xs ys (inl p)) ≡
    Inhab xs p  
++-inhab-inl (x :: xs) ys (inl ⋆) = refl x
++-inhab-inl (x :: xs) ys (inr p) = ++-inhab-inl xs ys p

++-inhab-inr : {X : Type} (xs ys : List X) (p : Pos ys)
  → Inhab (xs ++ ys) (←-++-pos xs ys (inr p)) ≡
    Inhab ys p  
++-inhab-inr [] ys p = refl (Inhab ys p)
++-inhab-inr (x :: xs) ys p = ++-inhab-inr xs ys p

```

## Concatenating Permutations

Using the previous decomposition of the positions of a concatenation,
we can show that we if have two permutations, then they can be
concatenated to give a permutation of the concatenated lists.

```agda
++-perm : {X : Type} {xs xs' ys ys' : List X}
  → xs IsPermutationOf xs'
  → ys IsPermutationOf ys'
  → (xs ++ ys) IsPermutationOf (xs' ++ ys')
++-perm {xs = xs} {xs'} {ys} {ys'} isp-xs isp-ys =
  record { pos-iso = ++-pos-iso ; inhab-eq = ++-inhab-eq }

  where ++-pos-iso : Pos (xs ++ ys) ≅ Pos (xs' ++ ys')
        ++-pos-iso = Pos (xs ++ ys) ≅⟨ ++-pos xs ys ⟩
                     Pos xs ∔ Pos ys ≅⟨ ∔-pair-iso (pos-iso isp-xs) (pos-iso isp-ys) ⟩
                     Pos xs' ∔ Pos ys' ≅⟨ iso-utils.≅-sym (++-pos xs' ys') ⟩ 
                     Pos (xs' ++ ys') ∎ᵢ 

        lemma : (p : Pos xs ∔ Pos ys)
          → Inhab (xs ++ ys) (←-++-pos xs ys p) ≡
            Inhab (xs' ++ ys') (←-++-pos xs' ys' (bijection (∔-pair-iso (pos-iso isp-xs) (pos-iso isp-ys)) p))
            
        lemma (inl px) = Inhab (xs ++ ys) (←-++-pos xs ys (inl px))                                   ≡⟨ ++-inhab-inl xs ys px ⟩
                         Inhab xs px                                                                  ≡⟨ inhab-eq isp-xs px ⟩
                         Inhab xs' (bijection (pos-iso isp-xs) px)                                    ≡⟨ sym (++-inhab-inl xs' ys' (bijection (pos-iso isp-xs) px)) ⟩ 
                         Inhab (xs' ++ ys') (←-++-pos xs' ys' (inl (bijection (pos-iso isp-xs) px)))  ∎
                         
        lemma (inr py) = Inhab (xs ++ ys) (←-++-pos xs ys (inr py))                                   ≡⟨ ++-inhab-inr xs ys py ⟩
                         Inhab ys py                                                                  ≡⟨ inhab-eq isp-ys py ⟩
                         Inhab ys' (bijection (pos-iso isp-ys) py)                                    ≡⟨ sym (++-inhab-inr xs' ys' (bijection (pos-iso isp-ys) py)) ⟩ 
                         Inhab (xs' ++ ys') (←-++-pos xs' ys' (inr (bijection (pos-iso isp-ys) py)))  ∎

        ++-inhab-eq : (p : Pos (xs ++ ys)) →
          Inhab (xs ++ ys) p ≡ Inhab (xs' ++ ys') (bijection ++-pos-iso p)
        ++-inhab-eq p = Inhab (xs ++ ys) p ≡⟨ ap (Inhab (xs ++ ys)) (sym (η (bijectivity (++-pos xs ys)) p)) ⟩
                        Inhab (xs ++ ys) (←-++-pos xs ys (→-++-pos xs ys p)) ≡⟨ lemma (→-++-pos xs ys p) ⟩
                        Inhab (xs' ++ ys') (bijection ++-pos-iso p) ∎ 
```

## Some Basic Permutations

Here we develop some basic permutations and ways of combining them:
every list gives rise to an identity permutation, permutations can be
composed, the empty list is a permutation of itself, and we can extend
a given permutation by adding a fixed element to the head of a list.

```agda
id-perm : {X : Type} (xs : List X) → xs IsPermutationOf xs
id-perm xs = record { pos-iso = id-iso (Pos xs) ; inhab-eq = λ p → refl _ }

∙-perm : {X : Type} {xs ys zs : List X}
  → xs IsPermutationOf ys
  → ys IsPermutationOf zs
  → xs IsPermutationOf zs
∙-perm {xs = xs} {ys} {zs} xy-perm yz-perm =
  record { pos-iso = ∙-pos-iso ; inhab-eq = ∙-inhab-eq } 

    where ∙-pos-iso : Pos xs ≅ Pos zs
          ∙-pos-iso = pos-iso yz-perm ∘ᵢ (pos-iso xy-perm)

          ∙-inhab-eq : (p : Pos xs) → Inhab xs p ≡ Inhab zs (bijection ∙-pos-iso p)
          ∙-inhab-eq p = Inhab xs p                               ≡⟨ inhab-eq xy-perm p ⟩
                         Inhab ys (bijection (pos-iso xy-perm) p) ≡⟨ inhab-eq yz-perm (bijection (pos-iso xy-perm) p) ⟩ 
                         Inhab zs (bijection ∙-pos-iso p) ∎ 

[]-perm : {X : Type} → _IsPermutationOf_ {X} [] []
[]-perm = record { pos-iso = id-iso 𝟘 ; inhab-eq = 𝟘-elim }

::-perm : {X : Type} {x : X} {xs ys : List X}
  → xs IsPermutationOf ys
  → (x :: xs) IsPermutationOf (x :: ys)
::-perm {x = x} {xs} {ys} is-perm = record { pos-iso = ::-pos-iso ; inhab-eq = ::-inhab-eq } 

  where ::-pos-iso : 𝟙 ∔ Pos xs ≅ 𝟙 ∔ Pos ys
        ::-pos-iso = ∔-pair-iso (id-iso 𝟙) (pos-iso is-perm) 

        ::-inhab-eq : (p : 𝟙 ∔ Pos xs) → Inhab (x :: xs) p ≡ Inhab (x :: ys) (bijection ::-pos-iso p)
        ::-inhab-eq (inl ⋆) = refl x
        ::-inhab-eq (inr p) = inhab-eq is-perm p
```

Finally, the following two permutations are used in the definition of quick-sort:

```agda
head-swap-perm : {X : Type} (x y : X) (xs : List X)
  → (x :: y :: xs) IsPermutationOf (y :: x :: xs)
head-swap-perm x y xs = record { pos-iso = ∔-left-swap-iso 𝟙 𝟙 (Pos xs)
                               ; inhab-eq = i-eq }

  where i-eq : (p : 𝟙 ∔ 𝟙 ∔ Pos xs)
           → Inhab (x :: y :: xs) p ≡
             Inhab (y :: x :: xs) (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) p)
        i-eq (inl ⋆) = refl x
        i-eq (inr (inl ⋆)) = refl y
        i-eq (inr (inr p)) = refl _


intercal-perm : {X : Type} (x y : X) (xs ys : List X)
  → (xs ++ (x :: y :: ys)) IsPermutationOf ((y :: xs) ++ (x :: ys))
intercal-perm x y [] ys = head-swap-perm x y ys
intercal-perm x y (z :: xs) ys =
  ∙-perm (::-perm {x = z} (intercal-perm x y xs ys))
    ((++-perm (head-swap-perm z y xs) (id-perm (x :: ys))))
```

## Lemmas about Sorted Lists

<!--
```agda
module _ {X : Type} (τ : StrictTotalOrder X) where
  open StrictTotalOrder τ
```
-->

Here we show that if we have an element `x` which is less than or equal to every element of
a list `xs` and `xs` is sorted, then the extended list `x :: xs` is also sorted.

```agda
  ::-sorted : {x : X} {xs : List X}
    → (lte : (p : Pos xs) → (Inhab xs p ≡ x) ∔ (x < Inhab xs p))  -- x ≤ Inhab xs p
    → Sorted τ xs → Sorted τ (x :: xs)
  ::-sorted lt nil-sorted = sing-sorted
  ::-sorted lt sing-sorted = adj-sorted sing-sorted (lt (inl ⋆))
  ::-sorted lt (adj-sorted s y≤z) = adj-sorted (adj-sorted s y≤z) (lt (inl ⋆))
```

A slight variation on the previous lemma is that, if we have two
sorted lists `xs` and `ys` and we know that every element of `xs` is
less than or equal to every element of `ys`, then the concatenation
`xs ++ ys` is again sorted.

```agda
  ++-sorted : {xs ys : List X}
    → Sorted τ xs → Sorted τ ys
    → (lte : (p : Pos xs) (q : Pos ys) → (Inhab ys q ≡ Inhab xs p) ∔ (Inhab xs p < Inhab ys q))
    → Sorted τ (xs ++ ys)
  ++-sorted nil-sorted ys-s lte = ys-s
  ++-sorted {ys = ys} (sing-sorted {x}) ys-s lte = ::-sorted (λ p → lte (inl ⋆) p) ys-s
  ++-sorted {ys = ys} (adj-sorted {y} {z} {xs} xs-s y≤z) ys-s lte =
    adj-sorted (++-sorted {xs = z :: xs} {ys} xs-s ys-s (λ p q → lte (inr p) q)) y≤z
```

We will see in the definition of quick-sort that sometimes we need to
apply the previous lemmas two **permutations** of a given list.  The following
helper functions will make this more convenient:

```agda 
  <-perm-inv : (x : X) {xs ys : List X}
    → ys IsPermutationOf xs
    → (ϕ : (p : Pos xs) → x < Inhab xs p)
    → (p : Pos ys) → x < Inhab ys p
  <-perm-inv x is-perm ϕ p = transport (λ y → x < y) (sym (inhab-eq is-perm p))
    (ϕ (bijection (pos-iso is-perm) p)) 

  ≤-perm-inv : (x : X) {xs ys : List X}
    → ys IsPermutationOf xs
    → (ϕ : (p : Pos xs) → (x ≡ Inhab xs p) ∔ (Inhab xs p < x))
    → (p : Pos ys) → (x ≡ Inhab ys p) ∔ (Inhab ys p < x)
  ≤-perm-inv x is-perm ϕ p = transport (λ y → (x ≡ y) ∔ (y < x)) (sym (inhab-eq is-perm p))
    (ϕ (bijection (pos-iso is-perm) p))

  <-perm-sep : {xs xs' ys ys' : List X}
    → xs IsPermutationOf xs'
    → ys IsPermutationOf ys'
    → (ϕ : (p : Pos xs') (q : Pos ys') → Inhab xs' p < Inhab ys' q)
    → (p : Pos xs) (q : Pos ys) → Inhab xs p < Inhab ys q
  <-perm-sep {xs} {ys' = ys'} is-perm-xs is-perm-ys ϕ p q =
    let p' = bijection (pos-iso is-perm-xs) p
        q' = bijection (pos-iso is-perm-ys) q
        lt = ϕ p' q' 
    in transport (Inhab xs p <_) (sym (inhab-eq is-perm-ys q))
        (transport (_< Inhab ys' q') (sym (inhab-eq is-perm-xs p)) lt) 

```
