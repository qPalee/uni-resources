<!--
```agda
{-# OPTIONS --without-K --safe #-}

module quick-sort where

open import prelude
open import isomorphisms
open import List-functions
open import iso-utils
open import strict-total-order
open import sorting
open import well-founded
open import quick-sort-lemmas

module _ (X : Type) (τ : StrictTotalOrder X) where

  open StrictTotalOrder τ
  open <ₗ-wf X
  open _IsPermutationOf_
  open _≅_

```
-->

## Partitioning with a Pivot

We start with a pair of functions partitioning a list into a left and
right list using a *pivot* element.

```agda
  partition-lte : X → List X → List X
  partition-lte x [] = []
  partition-lte x (y :: xs) with trichotomy x y
  partition-lte x (y :: xs) | inl x<y = partition-lte x xs
  partition-lte x (y :: xs) | inr y≤x = y :: partition-lte x xs

  partition-gt : X → List X → List X
  partition-gt x [] = []
  partition-gt x (y :: xs) with trichotomy x y
  partition-gt x (y :: xs) | inl x<y = y :: partition-gt x xs
  partition-gt x (y :: xs) | inr y≤x = partition-gt x xs
```

We will need to know that the lists obtained by the previous functions
are always shorter than the list obtained by simply adjoining the pivot.

```agda
  partition-lte-shorter : (x : X) (xs : List X)
                        → partition-lte x xs <ₗ (x :: xs)
  partition-lte-shorter x [] = <-zero
  partition-lte-shorter x (y :: xs) with trichotomy x y
  partition-lte-shorter x (y :: xs) | inl x<y =
    <ₙ-trans (partition-lte-shorter x xs)
             (<ₙ-lem (suc (length xs)))
  partition-lte-shorter x (y :: xs) | inr y≤x =
    <-suc (partition-lte-shorter x xs)

  partition-gt-shorter : (x : X) (xs : List X)
                       → partition-gt x xs <ₗ (x :: xs)
  partition-gt-shorter x [] = <-zero
  partition-gt-shorter x (y :: xs) with trichotomy x y
  partition-gt-shorter x (y :: xs) | inl x<y =
    <-suc (partition-gt-shorter x xs)
  partition-gt-shorter x (y :: xs) | inr y≤x =
    <ₙ-trans (partition-gt-shorter x xs)
              (<ₙ-lem (suc (length xs)))
```

Next, putting the pivot element *between* the two partitions yields a
permutation of the list obtained by simply adjoining the pivot.  This
is not hard if we use the various permutation combinators from
[quick-sort-lemmas](quick-sort-lemmas.lagda.md).

```agda
  partition-perm : (x : X) (xs : List X)
                 → (partition-lte x xs ++ (x :: partition-gt x xs))
                     IsPermutationOf (x :: xs)
  partition-perm x [] = ::-perm []-perm
  partition-perm x (y :: ys) with trichotomy x y
  partition-perm x (y :: xs) | inl x<y =
   ∙-perm (∙-perm (intercal-perm x y _ _)
                  (::-perm {x = y}
                           (partition-perm x xs)))
          (head-swap-perm y x xs)
  partition-perm x (y :: xs) | inr y≤x =
   ∙-perm (::-perm {x = y} (partition-perm x xs))
          (head-swap-perm y x xs)
```

Every element of the `partition-lte` is less than or equal to the pivot, and
every element of the `partition-gt` is strictly larger than the pivot.  As
a consequence, we have that every element of the left list is strictly
smaller than every element of the right.

```agda
  partition-lte-is-lte : (x : X) (xs : List X)
                         (p : Pos (partition-lte x xs))
                       → Inhab (partition-lte x xs) p ≤ x
  partition-lte-is-lte x (y :: xs) p with trichotomy x y
  partition-lte-is-lte x (y :: xs) p | inl x<y =
   partition-lte-is-lte x xs p
  partition-lte-is-lte x (y :: xs) (inl ⋆) | inr y≤x = y≤x
  partition-lte-is-lte x (y :: xs) (inr p) | inr y≤x =
   partition-lte-is-lte x xs p

  partition-gt-is-gt : (x : X) (xs : List X)
                       (p : Pos (partition-gt x xs))
                     → x < Inhab (partition-gt x xs) p
  partition-gt-is-gt x (y :: xs) p with trichotomy x y
  partition-gt-is-gt x (y :: xs) (inl ⋆) | inl x<y = x<y
  partition-gt-is-gt x (y :: xs) (inr p) | inl x<y =
   partition-gt-is-gt x xs p
  partition-gt-is-gt x (y :: xs) p | inr y≤x =
   partition-gt-is-gt x xs p

  partition-split : (x : X) (xs : List X)
                    (p : Pos (partition-lte x xs))
                    (q : Pos (partition-gt x xs))
                  → Inhab (partition-lte x xs) p
                  < Inhab (partition-gt x xs) q
  partition-split x xs p q =
   lte-lt {y = x}
          (partition-lte-is-lte x xs p)
          (partition-gt-is-gt x xs q)

    where lte-lt : {x y z : X}
                 → ((y ≡ x) ∔ (x < y))
                 → (y < z) → (x < z)
          lte-lt (inl (refl _)) lt = lt
          lte-lt (inr x<y) y<z = transitive x<y y<z
```

## Quick-sort

Since the naive quick-sort algorithm does not pass the termination
checker, we will have to use well-founded induction.  It will be
convient, therefore, to construct all the information for the sorting
(the sorted list, the proof that it is sorted and the permutation) at
once.  We can make this easier by defining the notion of a `SortingOf`
a fixed list `xs`.


```agda
  record SortingOf (xs : List X) : Type where
    field
      sort-of : List X
      is-sorted : Sorted τ sort-of
      is-perm : sort-of IsPermutationOf xs

  open SortingOf
```
We now construct a sorting for any list by well-founded induction:

```agda

  quick-sort-sorting : (xs : List X) → SortingOf xs
  quick-sort-sorting = wf-ind (_<ₗ_) SortingOf <ₗ-WF ih
   where
    ih : (xs : List X)
       → ((ys : List X) → ys <ₗ xs → SortingOf ys)
       → SortingOf xs
    ih        [] qs-ih = record { sort-of = [] ;
                                  is-sorted = nil-sorted ;
                                  is-perm = []-perm }
    ih (x :: xs) qs-ih = record { sort-of = quick-sort-of ;
                                  is-sorted = quick-is-sorted ;
                                  is-perm = quick-is-perm }

     where  -- First, we call the inductive hypothesis to sort the smaller
            -- and larger elements ...
      smaller-sorting : SortingOf (partition-lte x xs)
      smaller-sorting = qs-ih (partition-lte x xs) (partition-lte-shorter x xs)

      bigger-sorting : SortingOf (partition-gt x xs)
      bigger-sorting = qs-ih (partition-gt x xs) (partition-gt-shorter x xs)

      -- Now we assemble the results into a sorting of the whole list ...
      quick-sort-of : List X
      quick-sort-of = sort-of smaller-sorting ++ (x :: sort-of bigger-sorting)

      -- Next to show the result is sorted.
      quick-is-sorted : Sorted τ quick-sort-of
      quick-is-sorted = ++-sorted τ (is-sorted smaller-sorting)
                                    (::-sorted τ x≤bigger (is-sorted bigger-sorting))
                                    smaller≤x::bigger
        where
         x≤bigger : (p : Pos (sort-of bigger-sorting))
                  → x ≤ Inhab (sort-of bigger-sorting) p
         x≤bigger p = inr (<-perm-inv τ x (is-perm bigger-sorting) (partition-gt-is-gt x xs) p)

         smaller≤x::bigger : (p : Pos (sort-of smaller-sorting))
                             (q : Pos (x :: sort-of bigger-sorting))
                           → Inhab (sort-of smaller-sorting) p
                           ≤ Inhab (x :: sort-of bigger-sorting) q
         smaller≤x::bigger p (inl ⋆) = ≤-perm-inv τ x
                                        (is-perm smaller-sorting)
                                        (partition-lte-is-lte x xs)
                                        p
         smaller≤x::bigger p (inr q) = inr (<-perm-sep τ
                                             (is-perm smaller-sorting)
                                             (is-perm bigger-sorting)
                                             (partition-split x xs)
                                             p
                                             q)
 -- Now show that it is a permutation
      quick-is-perm : quick-sort-of IsPermutationOf (x :: xs)
      quick-is-perm = ∙-perm (++-perm (is-perm smaller-sorting)
                                      (::-perm (is-perm bigger-sorting)))
                             (partition-perm x xs)
```

And finally we can finish the definition of the quick sort algorithm
by simply extracting the components obtained from the well-founded
induction above.

```agda
  quick-sort-algorithm : SortingAlgorithm τ
  quick-sort-algorithm =
    record { sort = λ xs → sort-of (quick-sort-sorting xs)
           ; sort-is-sorted = λ xs → is-sorted (quick-sort-sorting xs)
           ; sort-is-permutation = λ xs → is-perm (quick-sort-sorting xs) }
```
