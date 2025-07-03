<!--
```agda
{-# OPTIONS --without-K --safe #-}

module insertion-sort where 

open import prelude
open import isomorphisms
open import List-functions
open import iso-utils
open import partial-orders
open import sorting
```
-->

## Insertion Sort

Our first sorting algorithm is called the *insertion sort*.  The idea
is quite simple: we will define a function `insert` which attempts to
add a new element to the list by starting at the head and asking, for
each element it encounters, whether the the given element is larger
than the head element or not.  If the given element is smaller, it
becomes the new head, while if it is larger (or equal) we continue
trying to insert it in the tail.  In this way, larger elements are
accumulated at the end of the list and smaller elements at the
beginning.  We obtain a sorting algorithm by repeatedly inserting the
elements of a given list into the empty list.

Let's now put this into action.  We begin with the insert function.
Notice that we need the order to be total in order to decide at each
step whether to 

```agda
module InsertionSort {X : Type} (ρ : PartialOrder X) (τ : is-total ρ) where
  open PartialOrder ρ
  open _≅_

  -- Definition of insertion sort
  insert : X → List X → List X
  perform-insertion : (x y : X) (xs : List X) → (x ≤ y) ∔ (y ≤ x)  → List X
  
  insert x [] = x :: []
  insert x (y :: xs) = perform-insertion x y xs (τ x y)

  perform-insertion x y xs (inl x≤y) = x :: y :: xs
  perform-insertion x y xs (inr y≤x) = y :: insert x xs
```

In the second clause of `insert`, where we need to discriminate
between the two cases, we do this in a separate helper function which
is defined simultaneously.  This will make properties of this function
easier to prove below.

Next we write a simple auxillary algorithm to iteratively insert a list
of elements in another list.

```agda
  insert-all : List X → List X → List X
  insert-all [] ys = ys
  insert-all (x :: xs) ys = insert x (insert-all xs ys)
```

And now we obtain our insertion sort by iteratively inserting the elements of
our list into the empty list.

```agda
  insertion-sort : List X → List X
  insertion-sort xs = insert-all xs []
```

## Proving the insertion sort produces a sorted list

Our first task is to show that this process always produces a sorted
list.

We begin with a pair of lemmas describing how the `insert` and
`perform-insertion` functions preserve sorted lists.

The proofs are essentially straightforward unwindings of the
definitions with one subtlety: because the last constructor of
`Sorted` datatype needs *two* elements of the list, we have to unfold
the definitions twice for the recursion to close.  You can see this in
the structure of the lemmas below, where the subscripts indicate the
level of unfolding.  Moreover, since `insert` and `perform-insertion`
are defined mutually, we prove their properties mutually as well.

```agda
  insertion-lemma₁ : (x : X) (xs : List X)
    → Sorted ρ xs
    → Sorted ρ (insert x xs)
  
  perform-insertion-lemma₁ : (x y : X) (xs : List X)
    → (α : (x ≤ y) ∔ (y ≤ x))
    → Sorted ρ (y :: xs)
    → Sorted ρ (perform-insertion x y xs α)

  insertion-lemma₂ : (x y : X) (xs : List X)
    → y ≤ x
    → Sorted ρ (y :: xs)
    → Sorted ρ (y :: insert x xs)
  
  perform-insertion-lemma₂ : (x y z : X) (xs : List X) 
    → y ≤ x → (t : (x ≤ z) ∔ (z ≤ x))
    → Sorted ρ (y :: z :: xs)
    → Sorted ρ (y :: perform-insertion x z xs t)

  insertion-lemma₁ x [] s = sing-sorted x
  insertion-lemma₁ x (y :: xs) s = perform-insertion-lemma₁ x y xs (τ x y) s

  perform-insertion-lemma₁ x y xs (inl x≤y) s = adj-sorted xs x≤y s
  perform-insertion-lemma₁ x y xs (inr y≤x) s = insertion-lemma₂ x y xs y≤x s

  insertion-lemma₂ x y [] y≤x s = adj-sorted [] y≤x (sing-sorted x)
  insertion-lemma₂ x y (z :: xs) y≤x s = perform-insertion-lemma₂ x y z xs y≤x (τ x z) s

  perform-insertion-lemma₂ x y z xs y≤x (inl x≤z) (adj-sorted xs y≤z s) =
    adj-sorted (z :: xs) y≤x (adj-sorted xs x≤z s)
  perform-insertion-lemma₂ x y z xs y≤x (inr z≤x) (adj-sorted xs y≤z s) =
    adj-sorted (insert x xs) y≤z (insertion-lemma₂ x z xs z≤x s)
```

With the above lemmas in place, proving that the insertion sort produces
a sorted list becomes a straightforward induction:

```agda 
  insertion-sort-is-sorted : (xs : List X) → Sorted ρ (insertion-sort xs)
  insertion-sort-is-sorted [] = nil-sorted
  insertion-sort-is-sorted (x :: xs) =
    insertion-lemma₁ x (insertion-sort xs) (insertion-sort-is-sorted xs) 
```

## Constructing the Permutation

Our next step is to construct a permutation for the sorted list.  To
do so, we will make use of some auxilliary isomorphisms defined
[here](iso-utils.lagda.md).  In particular, we exploit the fact
that we can use equational reasoning with isomorphisms just like
we can for equality.  This allows us to construct the required
isomorphisms in steps without writing out explicitly the functions
in each direction.

We start with a pair of lemmas describing a how the functions `insert` and
`perform-insertion` modify the positions of a list.

```agda
  insert-pos-iso : (x : X) (xs : List X)
    → Pos (insert x xs) ≅ 𝟙 ∔ Pos xs

  perform-insertion-pos-iso : (x y : X) (xs : List X) (t : (x ≤ y) ∔ (y ≤ x))
    → Pos (perform-insertion x y xs t) ≅ 𝟙 ∔ 𝟙 ∔ Pos xs

  insert-pos-iso x [] = id-iso (𝟙 ∔ 𝟘) 
  insert-pos-iso x (y :: xs) = perform-insertion-pos-iso x y xs (τ x y)

  perform-insertion-pos-iso x y xs (inl x≤y) = id-iso (𝟙 ∔ 𝟙 ∔ Pos xs)
  perform-insertion-pos-iso x y xs (inr y≤x) =
    𝟙 ∔ Pos (insert x xs) ≅⟨ ∔-pair-iso (id-iso 𝟙) (insert-pos-iso x xs) ⟩
    𝟙 ∔ 𝟙 ∔ Pos xs        ≅⟨ ∔-left-swap-iso 𝟙 𝟙 (Pos xs) ⟩ 
    𝟙 ∔ 𝟙 ∔ Pos xs ∎ᵢ 
```

The key point which makes these isomorphisms non-trivial is the last
clause of the definition of `perform-insertion-pos-iso`.  This is the
case where we are pushing one element past another, and so we have to
compose the inductive hypothesis with the isomorphism swapping the two
exposed positions.  This will be crucial below to show that these
isomorphisms preserve elements.

Now, combining these lemmas, we can show that the positions of a sorted list are
isomorphic to the positions of the original.

```agda
  insertion-sort-pos-iso : (xs : List X) → Pos (insertion-sort xs) ≅ Pos xs 
  insertion-sort-pos-iso [] = id-iso 𝟘
  insertion-sort-pos-iso (x :: xs) =
    Pos (insert x (insertion-sort xs)) ≅⟨ insert-pos-iso x (insertion-sort xs) ⟩
    𝟙 ∔ Pos (insertion-sort xs)        ≅⟨ ∔-pair-iso (id-iso 𝟙) (insertion-sort-pos-iso xs) ⟩ 
    𝟙 ∔ Pos xs ∎ᵢ
```

Now we have to show that the inhabitants are preserved by our choice
of permutation.  The first lemma here shows how inhabitants interact
with the swapping isomorphism used above.

```agda
  pos-swap-lemma : (x y : X) (xs : List X)
    → (p : Pos (y :: xs))
    → (x :: y :: xs) !! (inr p) ≡
      (y :: x :: xs) !! (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) (inr p))
  pos-swap-lemma x y xs (inl ⋆) = refl y
  pos-swap-lemma x y xs (inr p) = refl (xs !! p)
```

With the above lemma, we can complete the calculation of the equality
of inhabitants with respect to the insert function.  We follow the same
pattern of simultaneously proving two lemmas, one for `insert` and one
for the helper function `perform-insertion`.

```agda
  insert-el-eq : (x : X) (xs : List X)
    → (p : Pos (insert x xs))
    → (insert x xs) !! p ≡ (x :: xs) !! (bijection (insert-pos-iso x xs) p)

  perform-insertion-el-eq : (x y : X) (xs : List X) (t : (x ≤ y) ∔ (y ≤ x))
    → (p : Pos (perform-insertion x y xs t))
    → (perform-insertion x y xs t !! p) ≡
      ((x :: y :: xs) !! bijection (perform-insertion-pos-iso x y xs t) p)
      
  insert-el-eq x [] (inl ∙) = refl x
  insert-el-eq x (y :: xs) p = perform-insertion-el-eq x y xs (τ x y) p

  perform-insertion-el-eq x y xs (inl x≤y) p = refl _
  perform-insertion-el-eq x y xs (inr y≤x) (inl ∙) = refl _
  perform-insertion-el-eq x y xs (inr y≤x) (inr p) = 
    insert x xs !! p
      ≡⟨ insert-el-eq x xs p ⟩
    ((x :: xs) !! bijection (insert-pos-iso x xs) p)
      ≡⟨ pos-swap-lemma y x xs (bijection (insert-pos-iso x xs) p) ⟩ 
    (((x :: y :: xs) !! bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs))
       (inr (bijection (insert-pos-iso x xs) p)))) ∎
```

After a quick lemma showing how to extend a collection of inhabitant
equalities when a new element is added to the list, we can show that
elements are preserved by the permutation produced above.

```agda
  el-eq-ext-lemma : (x : X) (xs ys : List X) 
    → (α : Pos xs ≅ Pos ys)
    → (e : (p : Pos xs) → xs !! p ≡ ys !! (bijection α p))
    → (p : Pos (x :: xs))
    → (x :: xs) !! p ≡ (x :: ys) !! (bijection (∔-pair-iso (id-iso 𝟙) α) p)
  el-eq-ext-lemma x xs ys α e (inl ⋆) = refl x
  el-eq-ext-lemma x xs ys α e (inr p) = e p


  insertion-sort-el-eq : (xs : List X) (p : Pos (insertion-sort xs)) →
    (insertion-sort xs !! p) ≡
    (xs !! bijection (insertion-sort-pos-iso xs) p)
  insertion-sort-el-eq (x :: xs) p = 
    insert x (insertion-sort xs) !! p

      ≡⟨ insert-el-eq x (insertion-sort xs) p ⟩
      
    (x :: insertion-sort xs) !! (bijection (insert-pos-iso x (insertion-sort xs)) p)

      ≡⟨ el-eq-ext-lemma x (insertion-sort xs) xs (insertion-sort-pos-iso xs)
          (insertion-sort-el-eq xs)
          (bijection (insert-pos-iso x (insertion-sort xs)) p)  ⟩
    
    (x :: xs) !! bijection (∔-pair-iso (id-iso 𝟙) (insertion-sort-pos-iso xs))
                  (bijection (insert-pos-iso x (insertion-sort xs)) p)

       ≡⟨ refl _ ⟩
                  
    (x :: xs) !! bijection (insertion-sort-pos-iso (x :: xs)) p ∎ 

```

Together, the previous functions show that the insertion sort gives a
permutation of the list being sorted.

```agda
  insertion-permutation : (xs : List X) → (insertion-sort xs) is-permutation-of xs 
  insertion-permutation xs = record { pos-iso = insertion-sort-pos-iso xs
                                    ; same-el = insertion-sort-el-eq xs 
                                    } 
```

And there we have it!  We can now wrap up all the work we have done
into our definition of sorting algorithm:

```agda
  insertion-sort-algorithm : SortingAlgorithm ρ 
  insertion-sort-algorithm =
    record { sort = insertion-sort
           ; sort-is-sorted = insertion-sort-is-sorted
           ; sort-is-permutation = insertion-permutation
           } 
```
