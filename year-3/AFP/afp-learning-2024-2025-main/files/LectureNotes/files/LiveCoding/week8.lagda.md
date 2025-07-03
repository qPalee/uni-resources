```agda
{-# OPTIONS --without-K --safe #-}

module LiveCoding.week8 where

open import prelude
open import partial-orders
open import decidability
open import natural-numbers-functions
open import List-functions
```

In this file, we will first define the type of *binary trees* (BTs),
as well as define some operations on this type and prove some
properties about them.

Then, we will define binary *search* trees in three ways. The first
approach defines BSTs as BTs that satisfy certain conditions. The
second and third approaches define BSTs from the ground up as a type
that *only* permits the construction of BSTs. The second and third
approaches differ in that the third approach is more efficient.

# Binary Trees

First, we define the type of BTs. A BT over type A is either:
 * a leaf containing no data,
 * a branch containing some data that has a left and right subtree.

```agda
data BT (A : Type) : Type where
 leaf   : BT A
 branch : A → BT A → BT A → BT A
```

For example,

```code
branch 5
  (branch 8
    leaf
    (branch 9
      (branch 1
        (branch 2
          leaf
          leaf)
        leaf)
      leaf))
  (branch 2 leaf leaf)
```

constructs the tree visualised below:

```code
       5
      / \
     /   \
    8     2
     \
      \
       9
      /
     /
    1
   /
  /
 2
```

## Size

The size of a BT is how many items of data it contains.

```agda
size : {A : Type} → BT A → ℕ
size = {!!}
```

Emptiness and nonemptiness can be defined using size.

```agda
empty' nonempty' : {A : Type} → BT A → Type
empty'    t = {!!}
nonempty' t = {!!}
```

## Membership

We define the type `x ∈ t` which is inhabited if `x : A` is a member of
the tree `t : BT A`.

```agda
_∈_ : {A : Type} → A → BT A → Type
x ∈ leaf = {!!}
x ∈ branch y l r = {!!}
```

Emptiness and nonemptiness can also be defined using membership.

```agda
nonempty empty : {A : Type} → BT A → Type
nonempty {A} t = {!!}
empty        t = {!!}
```

We prove that both definitions of emptiness and nonemptiness are the
same.

```agda
empty-is-empty' : {A : Type} (t : BT A) → empty t ⇔ empty' t
empty-is-empty' = {!!}

nonempty-is-nonempty' : {A : Type} (t : BT A)
                      → nonempty t ⇔ nonempty' t
nonempty-is-nonempty' = {!-- Lab exercise!!}
```

## Mirroring

Trees can be mirrored.

```agda
mirror : {A : Type} → BT A → BT A
mirror = {!!}
```

Mirroring the same tree twice gives back the original tree. Let's
prove that!

```agda
mirror-is-involutive : {A : Type} → mirror ∘ mirror ∼ id {BT A}
mirror-is-involutive = {!!}
```

## Flattening

By performing an in-order traversal of a binary tree, we can 'flatten'
it to a list.

```agda
flatten : {A : Type} → BT A → List A
flatten = {!!}
```

Furthermore, we can prove that flattening a mirrored tree is the same
as reversing a flattened tree.

```agda
reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
reverse-++-lemma = {!-- Lab exercise!!}

flatten-mirror-is-reverse-flatten
 : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
flatten-mirror-is-reverse-flatten = {!-- Lab exercise!!}
```

# Binary Search Trees - First Approach

A binary search tree is a binary tree such that, at every branch:
 * the left subtrees values are smaller than the branch's value,
 * the right subtrees values are bigger than the branch's value.

Therefore, we require a strict total order on the type of the tree's
values.

```agda
module first-approach (X : Type) (ρ : PartialOrder X) (trichotomy : trichotomous ρ) where

 open PartialOrder ρ
```

## Definition

We now define the predicates `all-smaller` and `all-bigger`, which in
turn allow us to define `is-bst`.

```agda
 all-smaller  : BT X → X → Type
 all-smaller = {!!}

 all-bigger  : BT X → X → Type
 all-bigger = {!!}

 is-bst : BT X → Type
 is-bst = {!!}
```
The type of binary search trees are those binary trees that satisfy
`is-bst`.

```agda
 BST : Type
 BST = {!!}
```

## Efficient membership

We can define the `_∈_` relation on BSTs by simply using the one on
BTs.

```agda
 _∈ₛ'_ : X → BST → Type
 x ∈ₛ' t = {!!}
```

However, this is clearly inefficient --- consider checking whether `5`
is in the below BST:

```code
       4
      / \
     /   \
    2     5
   / \
  /   \
 1     3
```

Once we see that `4` is the value of the first branch, we can use a
binary search method to only consider the right tree, without ever
checking the left.

To implement this, we will need to use proofs of trichotomy.

```agda
 Trichotomy : X → X → Type
 Trichotomy x y = (x < y) ∔ (x ≡ y) ∔ (x > y)
```

The base case is easy, clearly nothing is in an empty tree.
For the inductive case, we compare whether the branch value `x` is
is smaller than, equal to, or larger than the searched-for value `y`:
 * If `x < y` then we search only the right subtree,
 * If `x ≡ y` then `y` is in the tree,
 * if `x > y` then we search only the left subtree.

```agda
 _∈ₛ_ : X → BST → Type
 x ∈ₛ t = {!!}
``` 

Let's prove that the more efficient version implies the original
version.

```agda
 membership-implies-membership' : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ (t , i) → y ∈ₛ' (t , i)
 membership-implies-membership' = {!-- Lab exercise!!}
```

Aditionally, we can prove that being a member of a BST is decidable.

```agda
 being-in-is-decidable : (y : X) (t : BST) → is-decidable (y ∈ₛ t)
 being-in-is-decidable = {!!}
```

## Insert

The insert function is also defined using proofs of trichotomy.

```agda
 insert : X → BST → BST
```

In order to define `insert`, we will:
 1. First define what it does on the underlying BT,
 2. Prove that it preserves `is-smaller` and `is-bigger`, and therefore
    that it preserves `is-bst`.
 3. Use the above constructions to define `insert`.

So let's first define what `insert` does on the underlying BT.

```agda
 insert' : X → BT X → BT X
 insert' = {!!}
```

Second, we prove that `insert'` preserves `is-smaller` and `is-bigger`
and, thus, `is-bst`.

```agda
 insert'-preserves-all-smaller : (y x : X) (t : BT X)
                               → y < x
                               → all-smaller t x
                               → all-smaller (insert' y t) x
 insert'-preserves-all-smaller = {!!}

 insert'-preserves-all-bigger : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger = {!-- Lab exercise!!}

 insert'-preserves-being-bst
  : (y : X) (t : BT X) → is-bst t → is-bst (insert' y t)
 insert'-preserves-being-bst = {!!}
```

We can now define `insert` on the type of BSTs.

```agda
 insert x (t , i) = insert' x t , insert'-preserves-being-bst x t i
```

Additionally, we can prove that being a BST is decidable.

```agda
 all-smaller-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable = {!-- Lab exercise!!}

 all-bigger-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable = {!-- Lab exercise!!}

 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable = {!-- Lab exercise!!}
```

## More properties about insert

We have defined insert. Now we will prove various properties about it,
using proofs of trichotomy.

```agda
 insert-same-tree-property : (x : X) (t : BT X) (i : is-bst t)
                           → x ∈ₛ (t , i)
                           → fst (insert x (t , i)) ≡ t
 insert-same-tree-property = {!-- Lab exercise!!}

 insert-size-property : (x : X) (t : BT X) (i : is-bst t)
                  → (size (fst (insert x (t , i))) ≡ size t)
                  ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property = {!-- Lab exercise!!}

 insert-membership-property : (x : X) (t : BT X) (i : is-bst t)
                            → x ∈ₛ insert x (t , i)
 insert-membership-property = {!-- Lab exercise!!}

 membership-insert-property : (x y : X) (t : BT X) (i : is-bst t)
                            → y ∈ₛ insert x (t , i)
                            → (y ≡ x) ∔ (y ∈ₛ (t , i))
 membership-insert-property = {!-- Lab exercise!!}
```

# Binary Search Trees - Second Approach

For our second approach to BSTs, we define a type `BST` not as a
'subtype' of `BT X` but from the ground up.

By doing this, we define a type that only permits the construction of
binary search trees --- i.e., we no longer use a predicate `is-bst`.

```agda
module second-approach
 (X : Type) (ρ : PartialOrder X) (trichotomy : trichotomous ρ) where

 open PartialOrder ρ
 open first-approach X ρ trichotomy using (Trichotomy)
```

## Definition

We will reuse much of the code of the first approach, but this time we
must define the type `BST` *at the same time* as we define what the
predicates `all-smaller` and `all-bigger`.

```agda
 data BST : Type
 all-smaller : BST → X → Type
 all-bigger  : BST → X → Type
```

This is because the `branch` constructor of `BST` must take in proofs
that:
 * the left subtrees values are smaller than the branch's value,
 * the right subtrees values are bigger than the branch's value.

Rather than these proofs being required at a later stage, they are
used at the point we construct the binary search tree. This is called
*mutual recursion*.

```agda
 data BST where
  leaf : BST
  branch : (x : X) (l r : BST)
           (G : all-smaller l x) (S : all-bigger r x) → BST

 all-smaller = {!!}

 all-bigger = {!!}
```

## Insert

To define `insert`, the following four functions (from the first
approach) must be defined mutually recursively.

```agda
 insert : X → BST → BST

 insert-branch
  : (y x : X) (l r : BST)
    (G : all-smaller l x) (S : all-bigger r x) → Trichotomy x y → BST

 insert-preserves-all-smaller : (y x : X) (t : BST)
                               → y < x
                               → all-smaller t x
                               → all-smaller (insert y t) x

 insert-preserves-all-bigger : (y x : X) (t : BST)
                             → y > x
                             → all-bigger t x
                             → all-bigger (insert y t) x
```

The order that we define these functions often matters as to whether
Agda can solve the constraints of the problems we're dealing with.

Try to re-order the following definitions and see what happens.

```agda
 insert = {!!}

 insert-branch = {!!}

 insert-preserves-all-smaller = {!!}

 insert-preserves-all-bigger = {!!}
```

# Binary Search Trees - Third Approach

Our third approach follows our second approach in that we define a
type `BST` that can only construct binary search trees.

```agda
module third-approach
 (X : Type) (ρ : PartialOrder X) (trichotomy : trichotomous ρ) where

 open PartialOrder ρ
 open first-approach X ρ trichotomy using (Trichotomy)

```

## Definition

In fact, the initial code and indeed the definition of `BST` is exactly
the same as in the second approach.

```agda
 data BST : Type
 all-smaller : BST → X → Type
 all-bigger  : BST → X → Type

 data BST where
  leaf : BST
  branch : (x : X) (l r : BST)
           (G : all-smaller l x) (S : all-bigger r x) → BST
```

The difference comes with our definition of `all-smaller` and
`all-bigger`.

For `all-smaller`, in the branch case, rather than checking that
*every* element of both subtrees is smaller than `y`, we can compare
`y` *only with* the largest value currently in the tree.

This will be the rightmost value of the tree.

```agda
 all-smaller = ?
```

In the above, we use `r@` to pattern match on `r` while still allowing
us to use `r` to refer to the whole pattern.

We follow the same approach for `all-bigger`:

```agda
 all-bigger = ?
```

But actually, defining insert is incredibly tedious with this method.

So we stop here :-)
