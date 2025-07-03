```agda
{-# OPTIONS --without-K --safe #-}

module BST where

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
 branch : (x : A) → (l : BT A) → (r : BT A) → BT A
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
size leaf = 0
size (branch x l r) = 1 + size l + size r
```

Emptiness and nonemptiness can be defined using size.

```agda
empty' nonempty' : {A : Type} → BT A → Type
empty'    t = size t ≡ 0
nonempty' t = ¬ (empty' t)
```

## Membership

We define the type `x ∈ t` which is inhabited if `x : A` is a member of
the tree `t : BT A`.

```agda
_∈_ : {A : Type} → A → BT A → Type
x ∈ leaf = 𝟘
x ∈ branch y l r = (x ≡ y) ∔ (x ∈ l) ∔ (x ∈ r)
```

Emptiness and nonemptiness can also be defined using membership.

```agda
nonempty empty : {A : Type} → BT A → Type
nonempty {A} t = Σ x ꞉ A , x ∈ t
empty        t = ¬ (nonempty t)
```

We prove that both definitions of emptiness and nonemptiness are the
same.

```agda
empty-is-empty' : {A : Type} (t : BT A) → empty t ⇔ empty' t
empty-is-empty' {A} t = left t , right t
 where
  left : (t : BT A) → empty t → empty' t
  left leaf f = refl 0
  left (branch x l r) f = 𝟘-nondep-elim (f (x , (inl (refl x))))
  right : (t : BT A) → empty' t → empty t
  right leaf e (x , p) = p
  right (branch y l r) e (x , p) = suc-is-not-zero e

nonempty-is-nonempty' : {A : Type} (t : BT A)
                      → nonempty t ⇔ nonempty' t
nonempty-is-nonempty' {A} leaf = ltr , rtl
 where
  ltr : nonempty leaf → nonempty' {A} leaf
  ltr (x , ())
  rtl : nonempty' {A} leaf → nonempty leaf
  rtl f = 𝟘-nondep-elim (f (refl 0))
nonempty-is-nonempty' {A} (branch x l r) = ltr , rtl
 where
  ltr : nonempty (branch x l r) → nonempty' (branch x l r)
  ltr _ ()
  rtl : nonempty' (branch x l r) → nonempty (branch x l r)
  rtl f = x , (inl (refl x))
```

## Mirroring

Trees can be mirrored.

```agda
mirror : {A : Type} → BT A → BT A
mirror leaf = leaf
mirror (branch x l r) = branch x (mirror r) (mirror l)
```

Mirroring the same tree twice gives back the original tree. Let's
prove that!

```agda
mirror-is-involutive : {A : Type} → mirror ∘ mirror ∼ id {BT A}
mirror-is-involutive leaf = refl leaf
mirror-is-involutive (branch x l r)
 = ap₂ (branch x) (mirror-is-involutive l) (mirror-is-involutive r)
```

## Flattening

By performing an in-order traversal of a binary tree, we can 'flatten'
it to a list.

```agda
flatten : {A : Type} → BT A → List A
flatten leaf = []
flatten (branch x l r) = flatten l ++ [ x ] ++ flatten r
```

Furthermore, we can prove that flattening a mirrored tree is the same
as reversing a flattened tree.

```agda
reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
reverse-++-lemma r x [] = refl (reverse r ++ [ x ])
reverse-++-lemma r x (y :: l)
 = reverse r ++ [ x ] ++ reverse (y :: l)
     ≡⟨ refl _ ⟩
   reverse r ++ ([ x ] ++ (reverse l ++ [ y ]))
     ≡⟨ ap (reverse r ++_) (++-assoc [ x ] (reverse l) [ y ]) ⟩
   reverse r ++ (([ x ] ++ reverse l) ++ [ y ])
     ≡⟨ sym (++-assoc (reverse r) ([ x ] ++ reverse l) [ y ]) ⟩
  (reverse r ++ [ x ] ++ reverse l) ++ [ y ]
     ≡⟨ ap (_++ [ y ]) (reverse-++-lemma r x l) ⟩
   reverse (l ++ [ x ] ++ r) ++ [ y ]
     ≡⟨ refl _ ⟩ 
   reverse ([ y ] ++ l ++ [ x ] ++ r) ∎

flatten-mirror-is-reverse-flatten
 : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
flatten-mirror-is-reverse-flatten leaf = refl []
flatten-mirror-is-reverse-flatten (branch x l r)
 =  flatten (mirror r) ++ [ x ] ++ flatten (mirror l)
     ≡⟨ ap (λ - → - ++ [ x ] ++ flatten (mirror l))
           (flatten-mirror-is-reverse-flatten r) ⟩
   reverse (flatten r) ++ [ x ] ++ flatten (mirror l)
     ≡⟨ ap (λ - → reverse (flatten r) ++ [ x ] ++ -)
           (flatten-mirror-is-reverse-flatten l) ⟩
   reverse (flatten r) ++ [ x ] ++ reverse (flatten l)
     ≡⟨ reverse-++-lemma (flatten r) x (flatten l) ⟩
    reverse (flatten l ++ [ x ] ++ flatten r) ∎
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
 all-smaller leaf x = 𝟙
 all-smaller (branch y l r) x
  = (y < x) × all-smaller l x × all-smaller r x
 
 all-bigger  : BT X → X → Type
 all-bigger leaf x = 𝟙
 all-bigger (branch y l r) x
  = (y > x) × all-bigger l x × all-bigger r x

 is-bst : BT X → Type
 is-bst leaf = 𝟙
 is-bst (branch x l r)
  = all-smaller l x × all-bigger r x × is-bst l × is-bst r
```
The type of binary search trees are those binary trees that satisfy
`is-bst`.

```agda
 BST : Type
 BST = Σ t ꞉ BT X , is-bst t
```

For example,

```code
 t : BT ℕ
 t = branch 4
  (branch 1
    leaf
    (branch 3
      (branch 2
        leaf
        leaf)
      leaf))
  (branch 5 leaf leaf)
```

constructs the tree visualised below:

```code
       4
      / \
     /   \
    1     5
     \
      \
       3
      /
     /
    2
```




## Efficient membership

We can define the `_∈_` relation on BSTs by simply using the one on
BTs.

```agda
 _∈ₛ'_ : X → BST → Type
 x ∈ₛ' (t , p) = x ∈ t
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
 _∈ₛ-bst_ : X → BT X → Type

 ∈ₛ-branch : (y x : X) → (l r : BT X) → Trichotomy y x → Type
 ∈ₛ-branch y x l r (inl      y<x)  = y ∈ₛ-bst l
 ∈ₛ-branch y x l r (inr (inl y≡x)) = 𝟙
 ∈ₛ-branch y x l r (inr (inr y>x)) = y ∈ₛ-bst r

 y ∈ₛ-bst leaf = 𝟘
 y ∈ₛ-bst (branch x l r)
  = ∈ₛ-branch y x l r (trichotomy y x)

 _∈ₛ_ : X → BST → Type
 x ∈ₛ (t , _) = x ∈ₛ-bst t
``` 

Let's prove that the more efficient version implies the original
version.

```agda
 membership-implies-membership' : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ (t , i) → y ∈ₛ' (t , i)
 membership-implies-membership' y (branch x l r) (s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x l r γ
        → (y ≡ x) ∔ (y ∈ l) ∔ (y ∈ r)
   goal (inl      y<x)  y∈t
    = inr (inl (membership-implies-membership' y l il y∈t))
   goal (inr (inl y≡x)) y∈t = inl y≡x
   goal (inr (inr y>x)) y∈t
    = inr (inr (membership-implies-membership' y r ir y∈t))
```

Aditionally, we can prove that being a member of a BST is decidable.

```agda
 being-in-is-decidable : (y : X) (t : BST) → is-decidable (y ∈ₛ t)
 being-in-is-decidable y (leaf , p) = 𝟘-is-decidable
 being-in-is-decidable y (branch x l r , sl , br , il , ir)
  = being-in-branch-is-decidable y x (l , il) (r , ir) (trichotomy y x)
  where
   being-in-branch-is-decidable
    : (y x : X) ((l , il) (r , ir) : BST)
    → (γ : Trichotomy y x)
    → is-decidable (∈ₛ-branch y x l r γ)
   being-in-branch-is-decidable y x l r (inl      y<x )
    = being-in-is-decidable y l
   being-in-branch-is-decidable y x l r (inr (inl y≡x))
    = 𝟙-is-decidable
   being-in-branch-is-decidable y x l r (inr (inr y>x))
    = being-in-is-decidable y r
```

## Insert

The insert function is also defined using proofs of trichotomy.

```agda
```

In order to define `insert`, we will:
 1. First define what it does on the underlying BT,
 2. Prove that it preserves `is-smaller` and `is-bigger`, and therefore
    that it preserves `is-bst`.
 3. Use the above constructions to define `insert`.

So let's first define what `insert` does on the underlying BT.

```agda
 insert' : X → BT X → BT X

 insert'-branch : (y x : X) (l r : BT X) → Trichotomy y x → BT X
 insert'-branch y x l r (inl      y<x )
  = branch x (insert' y l) r
 insert'-branch y x l r (inr (inl y≡x))
  = branch x l             r
 insert'-branch y x l r (inr (inr y>x))
  = branch x l             (insert' y r)

 insert' y leaf = branch y leaf leaf
 insert' y (branch x l r) = insert'-branch y x l r (trichotomy y x)
   
```

Second, we prove that `insert'` preserves `is-smaller` and `is-bigger`
and, thus, `is-bst`.

```agda
 insert'-preserves-all-smaller : (y x : X) (t : BT X)
                               → y < x
                               → all-smaller t x
                               → all-smaller (insert' y t) x
 insert'-preserves-all-smaller y x leaf y<x p
  = y<x , ⋆ , ⋆
  -- all-smaller (insert' y leaf) x
  -- all-smaller (branch y leaf leaf) x
  -- (y < x) × all-smaller leaf x × all-smaller leaf x
  -- (y < x) × 𝟙 × 𝟙
 insert'-preserves-all-smaller y x (branch x' l r) y<x (x'<x , sl , sr)
  = goal (trichotomy y x')
  -- p : all-smaller (branch x' l r) x
  -- p : x' < x × (all-smaller l x) × (all-smaller r x)
  where
   goal : (γ : Trichotomy y x')
        → all-smaller (insert'-branch y x' l r γ) x
   goal (inl      y<x' )
    = x'<x , insert'-preserves-all-smaller y x l y<x sl , sr
   goal (inr (inl y≡x'))
    = x'<x , sl , sr
   goal (inr (inr y>x'))
    = x'<x , sl , insert'-preserves-all-smaller y x r y<x sr

 insert'-preserves-all-bigger : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger y x leaf y>x b = y>x , ⋆ , ⋆
 insert'-preserves-all-bigger y x (branch x' l r) y>x (x'>x , bl , br)
  = goal (trichotomy y x')
  where
   goal : (γ : Trichotomy y x')
        → all-bigger (insert'-branch y x' l r γ) x
   goal (inl      y<x' )
    = x'>x , insert'-preserves-all-bigger y x l y>x bl , br
   goal (inr (inl y≡x'))
    = x'>x , bl , br
   goal (inr (inr y>x'))
    = x'>x , bl , insert'-preserves-all-bigger y x r y>x br

 insert'-preserves-being-bst
  : (y : X) (t : BT X) → is-bst t → is-bst (insert' y t)
 insert'-preserves-being-bst y leaf i = ⋆ , ⋆ , ⋆ , ⋆
 insert'-preserves-being-bst y (branch x l r) i
  = insert'-preserves-branch-being-bst y x l r i (trichotomy y x)
  where
   insert'-preserves-branch-being-bst
    : (y x : X) (l r : BT X)
    → is-bst (branch x l r)
    → (γ : Trichotomy y x)
    → is-bst (insert'-branch y x l r γ)
   insert'-preserves-branch-being-bst y x l r (sl , br , il , ir) (inl      y<x )
    = insert'-preserves-all-smaller y x l y<x sl , br , insert'-preserves-being-bst y l il , ir
   insert'-preserves-branch-being-bst y x l r i@(sl , br , il , ir) (inr (inl y≡x))
    = i
   insert'-preserves-branch-being-bst y x l r (sl , br , il , ir) (inr (inr y>x))
    = sl , insert'-preserves-all-bigger y x r y>x br , il , insert'-preserves-being-bst y r ir
```

We can now define `insert` on the type of BSTs.

```agda
 insert : X → BST → BST
 insert y (t , i) = (insert' y t) , (insert'-preserves-being-bst y t i)
```

Additionally, we can prove that being a BST is decidable.

```agda
 <-is-decidable : (x y : X) → is-decidable (x < y)
 <-is-decidable = trichotomous-implies-<-decidable ρ trichotomy
 
 all-smaller-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable leaf   y = 𝟙-is-decidable
 all-smaller-is-decidable (branch x l r) y =
    ×-preserves-decidability (<-is-decidable x y)
   (×-preserves-decidability (all-smaller-is-decidable l y)
                             (all-smaller-is-decidable r y))

 all-bigger-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable leaf   y = 𝟙-is-decidable
 all-bigger-is-decidable (branch x l r) y =
    ×-preserves-decidability (<-is-decidable y x)
   (×-preserves-decidability (all-bigger-is-decidable l y)
                             (all-bigger-is-decidable r y))
                             
 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable leaf   = 𝟙-is-decidable
 being-bst-is-decidable (branch x l r) =
   ×-preserves-decidability (all-smaller-is-decidable l x)
  (×-preserves-decidability (all-bigger-is-decidable r x)
  (×-preserves-decidability (being-bst-is-decidable l)
                            (being-bst-is-decidable r)))
```

## More properties about insert

We have defined insert. Now we will prove various properties about it,
using proofs of trichotomy. (

```agda
 insert-same-tree-property : (y : X) (t : BT X) (i : is-bst t)
                           → y ∈ₛ (t , i)
                           → fst (insert y (t , i)) ≡ t
 insert-same-tree-property y (branch x l r) (s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x l r γ
        → insert'-branch y x l r γ ≡ branch x l r
   goal (inl      y<x)  x∈ₛt
    = ap (λ - → branch x - r) (insert-same-tree-property y l il x∈ₛt)
   goal (inr (inl y≡x)) x∈ₛt
    = refl (branch x l r)
   goal (inr (inr x<y)) x∈ₛt
    = ap (branch x l) (insert-same-tree-property y r ir x∈ₛt)
 -- Slightly harder proof: insert x (t , i) ≡ (t , i)
 -- (You'll probably have to assume X is a set)

 insert-size-property : (x : X) (t : BT X) (i : is-bst t)
                      → (size (fst (insert x (t , i))) ≡ size t)
                      ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property y leaf i = inr (refl 1)
 insert-size-property y t@(branch x l r) (s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → (size (insert'-branch y x l r γ) ≡ size t)
        ∔ (size (insert'-branch y x l r γ) ≡ size t + 1)
   goal (inl y<x)
    = ∔-nondep-elim
        (λ e → inl (ap (λ - → suc (- + size r)) e))
        (λ e → inr (ap suc
                     (trans (ap (_+ size r) e)
                     (trans (+-assoc (size l) 1 (size r))
                     (trans (ap (size l +_) (+-comm 1 (size r)))
                       (sym (+-assoc (size l) (size r) 1)))))))
        (insert-size-property y l il)
   goal (inr (inl y≡x)) = inl (refl _)
   goal (inr (inr y>x))
    = ∔-nondep-elim
        (λ e → inl (ap (λ - → suc (size l + -)) e))
        (λ e → inr (ap suc
                     (trans (ap (size l +_) e)
                     (sym (+-assoc (size l) (size r) 1)))))
        (insert-size-property y r ir)

 ∈ₛ-branch-left : (y x : X) (l r : BT X)
               → (γ : Trichotomy y x)
               → y < x
               → y ∈ₛ-bst l
               → ∈ₛ-branch y x l r γ
 ∈ₛ-branch-left y x l r (inl y<x) _ y∈l
  = y∈l
 ∈ₛ-branch-left y x l r (inr (inl y≡x)) y<x y∈l
  = 𝟘-nondep-elim (<-irreflexive' ρ y≡x y<x) 
 ∈ₛ-branch-left y x l r (inr (inr y>x)) y<x y∈l
  = 𝟘-nondep-elim (<-antisymmetric ρ y x y<x y>x)

 ∈ₛ-branch-middle : (y x : X) (l r : BT X)
                 → (γ : Trichotomy y x)
                 → y ≡ x
                 → ∈ₛ-branch y x l r γ
 ∈ₛ-branch-middle x x l r (inl y<x) (refl x)
  = 𝟘-nondep-elim (<-irreflexive ρ x y<x) 
 ∈ₛ-branch-middle x x l r (inr (inl y≡x)) (refl x)
  = ⋆
 ∈ₛ-branch-middle x x l r (inr (inr y>x)) (refl x)
  = 𝟘-nondep-elim (<-irreflexive ρ x y>x)
  
 ∈ₛ-branch-right : (y x : X) (l r : BT X)
                → (γ : Trichotomy y x)
                → y > x
                → y ∈ₛ-bst r
                → ∈ₛ-branch y x l r γ
 ∈ₛ-branch-right x y l r (inl y<x) y>x y∈r
  = 𝟘-nondep-elim (<-antisymmetric ρ x y y<x y>x )
 ∈ₛ-branch-right x y l r (inr (inl y≡x)) y>x y∈r
  = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡x) y>x) 
 ∈ₛ-branch-right x y l r (inr (inr y>x)) _ y∈r
  = y∈r

 insert-membership-property : (x : X) (t : BT X) (i : is-bst t)  
                            → x ∈ₛ insert x (t , i)
 insert-membership-property x leaf i = goal (trichotomy x x)
  where
   goal : (γ : Trichotomy x x)
        → ∈ₛ-branch x x leaf leaf γ
   goal (inl x<x) = <-irreflexive ρ x x<x 
   goal (inr (inl x≡x)) = ⋆
   goal (inr (inr x<x)) = <-irreflexive ρ x x<x 
 insert-membership-property x (branch y l r) (s , b , il , ir)
  = goal (trichotomy x y)
  where
   goal : (γ : Trichotomy x y)
        → x ∈ₛ-bst insert'-branch x y l r γ
   goal (inl x<y)
    = ∈ₛ-branch-left x y (insert' x l) r
        (trichotomy x y) x<y (insert-membership-property x l il)
   goal (inr (inl x≡y))
    = ∈ₛ-branch-middle x y l r (trichotomy x y) x≡y
   goal (inr (inr x>y))
    = ∈ₛ-branch-right x y l (insert' x r)
        (trichotomy x y) x>y (insert-membership-property x r ir)

 ∈ₛ-branch-left' : (y x : X) (l r : BT X)
                 → (γ : Trichotomy y x)
                 → y < x
                 → ∈ₛ-branch y x l r γ
                 → y ∈ₛ-bst l
 ∈ₛ-branch-left' y x l r (inl y<x) _ y∈l
  = y∈l
 ∈ₛ-branch-left' y x l r (inr (inl y≡x)) y<x y∈l
  = 𝟘-nondep-elim (<-irreflexive' ρ y≡x y<x) 
 ∈ₛ-branch-left' y x l r (inr (inr y>x)) y<x y∈l
  = 𝟘-nondep-elim (<-antisymmetric ρ y x y<x y>x) 

 ∈ₛ-branch-right' : (y x : X) (l r : BT X)
                 → (γ : Trichotomy y x)
                 → y > x
                 → ∈ₛ-branch y x l r γ
                 → y ∈ₛ-bst r
 ∈ₛ-branch-right' y x l r (inl y<x) y>x y∈r
  = 𝟘-nondep-elim (<-antisymmetric ρ y x y<x y>x) 
 ∈ₛ-branch-right' y x l r (inr (inl y≡x)) y>x y∈r
  = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡x) y>x) 
 ∈ₛ-branch-right' y x l r (inr (inr y>x)) _ y∈r
  = y∈r
  
 membership-insert-property : (x y : X) (t : BT X) (i : is-bst t)
                               → y ∈ₛ insert x (t , i)
                               → (y ≡ x) ∔ (y ∈ₛ (t , i))
 membership-insert-property x y leaf i
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x leaf leaf γ
        → (y ≡ x) ∔ 𝟘
   goal (inl y<x) ()
   goal (inr (inl y≡x)) ⋆ = inl y≡x
   goal (inr (inr y>x)) ()
 membership-insert-property x y (branch z l r) (s , b , il , ir)
  = goal (trichotomy x z) (trichotomy y z)
  where
   goal : (γ : Trichotomy x z)
        → (ζ : Trichotomy y z)
        → y ∈ₛ-bst insert'-branch x z l r γ
        → (y ≡ x) ∔ ∈ₛ-branch y z l r ζ
   goal (inl x<z) (inl y<z) y∈t
    = membership-insert-property x y l il
        (∈ₛ-branch-left' y z (insert' x l) r (trichotomy y z) y<z y∈t)
   goal (inl x<z) (inr (inl (refl _))) y∈t
    = inr ⋆
   goal (inl x<z) (inr (inr y>z)) y∈t
    = inr (∈ₛ-branch-right' y z (insert' x l) r (trichotomy y z) y>z y∈t)
   goal (inr (inl (refl _))) (inl y<z) y∈t
    = inr (∈ₛ-branch-left' y z l r (trichotomy y x) y<z y∈t)
   goal (inr (inr x>z)) (inl y<z) y∈t
    = inr (∈ₛ-branch-left' y z l (insert' x r) (trichotomy y z) y<z y∈t)
   goal (inr (inl (refl _))) (inr (inl (refl _))) y∈t
    = inl (refl x)
   goal (inr (inl (refl _))) (inr (inr y>z)) y∈t
    = inr (∈ₛ-branch-right' y z l r (trichotomy y z) y>z y∈t)
   goal (inr (inr x>z)) (inr (inl (refl _))) y∈t
    = inr ⋆
   goal (inr (inr x>z)) (inr (inr y>z)) y∈t
    = membership-insert-property x y r ir
        (∈ₛ-branch-right' y z l (insert' x r) (trichotomy y z) y>z y∈t)
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
           (S : all-smaller l x) (G : all-bigger r x) → BST

 all-smaller leaf y = 𝟙
 all-smaller (branch x l r _ _) y
  = x < y × all-smaller l y × all-smaller r y
  
 all-bigger leaf y = 𝟙
 all-bigger (branch x l r _ _) y
  = x > y × all-bigger l y × all-bigger r y
```

## Insert

To define `insert`, the following four functions (from the first
approach) must be defined mutually recursively.

```agda
 insert : X → BST → BST

 insert-branch
  : (y x : X) (l r : BST)
    (S : all-smaller l x) (G : all-bigger r x) → Trichotomy y x → BST

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
 insert y leaf = branch y leaf leaf ⋆ ⋆
 insert y (branch x l r S G) = insert-branch y x l r S G (trichotomy y x)

 insert-branch y x l r S G (inl      y<x )
  = branch x (insert y l) r (insert-preserves-all-smaller y x l y<x S) G
 insert-branch y x l r S G (inr (inl y≡x))
  = branch x l r S G
 insert-branch y x l r S G (inr (inr y>x))
  = branch x l (insert y r) S (insert-preserves-all-bigger y x r y>x G)
  -- branch x l (insert' y r)

 insert-preserves-all-smaller y x leaf y<x S = y<x , ⋆ , ⋆
 insert-preserves-all-smaller y x (branch x' l r S' G') y<x S@(x'<x , Sl , Sr)
  = goal (trichotomy y x')
  where
   goal : (γ : Trichotomy y x')
        → all-smaller (insert-branch y x' l r S' G' γ) x
   goal (inl      y<x' ) = x'<x , insert-preserves-all-smaller y x l y<x Sl , Sr
   goal (inr (inl y≡x')) = S
   goal (inr (inr y>x')) = x'<x , Sl , insert-preserves-all-smaller y x r y<x Sr
   
 insert-preserves-all-bigger y x leaf y<x S = y<x , ⋆ , ⋆
 insert-preserves-all-bigger y x (branch x' l r S' G') y<x G@(x'>x , Gl , Gr)
  = goal (trichotomy y x')
  where
   goal : (γ : Trichotomy y x')
        → all-bigger (insert-branch y x' l r S' G' γ) x
   goal (inl      y<x' ) = x'>x , insert-preserves-all-bigger y x l y<x Gl , Gr
   goal (inr (inl y≡x')) = G
   goal (inr (inr y>x')) = x'>x , Gl , insert-preserves-all-bigger y x r y<x Gr
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
           (S : all-smaller l x) (G : all-bigger r x) → BST
```

The difference comes with our definition of `all-smaller` and
`all-bigger`.

For `all-smaller`, in the branch case, rather than checking that
*every* element of both subtrees is smaller than `y`, we can compare
`y` *only with* the largest value currently in the tree.

This will be the rightmost value of the tree.

```agda
 all-smaller leaf y = 𝟙
 all-smaller (branch x l leaf G S) y = x < y
 all-smaller (branch x l r@(branch x' l' r' S' G') S G) y
  = all-smaller r y
```

In the above, we use `r@` to pattern match on `r` while still allowing
us to use `r` to refer to the whole pattern.

We follow the same approach for `all-bigger`:

```agda
 all-bigger leaf y = 𝟙
 all-bigger (branch x leaf r S G) y = x > y
 all-bigger (branch x l@(branch _ _ _ _ _) r S G) y
  = all-bigger l y
```

But actually, defining insert is incredibly tedious with this method.

So we stop here :-)
