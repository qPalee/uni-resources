# Week 9 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab9-solutions where

open import prelude
open import partial-orders
open import decidability
open import natural-numbers-functions hiding (_≤_)
open import List-functions
open import sorting

open import BST
 hiding (nonempty-is-nonempty'
       ; reverse-++-lemma
       ; flatten-mirror-is-reverse-flatten)
```

# Part 1 - Binary Trees

## Exercise 1.1

**Prove** that the two definitions of nonemptiness are logically
equivalent.

```agda
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

## Exercise 1.2

**Prove** the following lemma about reverse and append.

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
```

## Exercise 1.3

Use `reverse-++-lemma` to **prove** that flattening a mirrored tree is
the same as reversing a flattened tree.

```agda
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

## Exercise 1.4

The function `flatten` performs an inorder traversal of the given tree.
Now **define** the functions of type `BT X → List X` that perform
preorder and postorder traversals of the given tree.

```agda
preorder  : {X : Type} → BT X → List X
preorder leaf = []
preorder (branch x l r) = x :: (preorder l ++ preorder r)

postorder : {X : Type} → BT X → List X
postorder leaf = []
postorder (branch x l r) = postorder l ++ postorder r ++ [ x ]
```

## Exercise 1.5

**Prove** that performing a preorder traversal of a tree is the same as
reversing a postorder traversal of the mirror of that tree.

*Hint:* First prove and use the lemma below.

```agda
reverse-++-lemma' : {X : Type} (l r : List X)
                  → reverse l ++ reverse r ≡ reverse (r ++ l)
reverse-++-lemma' l [] = []-right-neutral (reverse l)
reverse-++-lemma' l (x :: r)
 = reverse l ++ (reverse r ++ [ x ])
     ≡⟨ sym (++-assoc (reverse l) (reverse r) ([ x ])) ⟩
   (reverse l ++ reverse r) ++ [ x ]
     ≡⟨ ap (_++ [ x ]) (reverse-++-lemma' l r) ⟩
   reverse (r ++ l) ++ [ x ] ∎ 

preorder-is-reverse-of-postorder-mirror
 : {X : Type} → preorder {X} ∼ reverse ∘ postorder ∘ mirror
preorder-is-reverse-of-postorder-mirror leaf
 = refl []
preorder-is-reverse-of-postorder-mirror (branch x l r)
 = x :: (preorder l ++ preorder r)
     ≡⟨ ap (x ::_) (ap₂ _++_
                     (preorder-is-reverse-of-postorder-mirror l)
                     (preorder-is-reverse-of-postorder-mirror r)) ⟩
   x :: (reverse (postorder (mirror l)))
     ++ (reverse (postorder (mirror r)))
     ≡⟨ ap (_++ reverse (postorder (mirror r)))
           (reverse-++-lemma' [ x ] (postorder (mirror l))) ⟩ 
      reverse (postorder (mirror l) ++ [ x ])
   ++ reverse (postorder (mirror r))
     ≡⟨ reverse-++-lemma'
          (postorder (mirror l) ++ [ x ]) (postorder (mirror r)) ⟩
   reverse (postorder (mirror r) ++ postorder (mirror l) ++ [ x ])  ∎
```

# Part 2 - Binary Search Trees

We work with the subtype `BST` (i.e. the first approach to Binary
Search Trees) defined in the lecture.

```agda
module _
 (X : Type) (ρ : PartialOrder X) (trichotomy : trichotomous ρ) where

 open PartialOrder ρ
 open first-approach X ρ trichotomy
  hiding (<-is-decidable
         ; ∈ₛ-branch-left
         ; ∈ₛ-branch-middle
         ; ∈ₛ-branch-right
         ; ∈ₛ-branch-left'
         ; ∈ₛ-branch-right')
```

## Exercise 2.1

**Prove** that `insert' : X → BT X → BT X` preserves `all-bigger`.

```agda
 insert'-preserves-all-bigger' : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger' y x leaf y>x b = y>x , ⋆ , ⋆
 insert'-preserves-all-bigger' y x (branch x' l r) y>x (x'>x , bl , br)
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
```

## Exercise 2.2

**Prove** that `all-smaller` and `all-bigger` are decidable properties.

```agda
 <-is-decidable : (x y : X) → is-decidable (x < y)
 <-is-decidable = trichotomous-implies-<-decidable ρ trichotomy

 all-smaller-is-decidable-ex
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable-ex leaf   y = 𝟙-is-decidable
 all-smaller-is-decidable-ex (branch x l r) y =
    ×-preserves-decidability (<-is-decidable x y)
   (×-preserves-decidability (all-smaller-is-decidable l y)
                             (all-smaller-is-decidable r y))

 all-bigger-is-decidable-ex
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable-ex leaf   y = 𝟙-is-decidable
 all-bigger-is-decidable-ex (branch x l r) y =
    ×-preserves-decidability (<-is-decidable y x)
   (×-preserves-decidability (all-bigger-is-decidable l y)
                             (all-bigger-is-decidable r y))
```

Hence, prove that it is decidable whether or not a `BT X` is a BST.

```agda
 being-bst-is-decidable-ex : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable-ex leaf   = 𝟙-is-decidable
 being-bst-is-decidable-ex (branch x l r) =
   ×-preserves-decidability (all-smaller-is-decidable-ex l x)
  (×-preserves-decidability (all-bigger-is-decidable-ex r x)
  (×-preserves-decidability (being-bst-is-decidable-ex l)
                            (being-bst-is-decidable-ex r)))
```

## Exercise 2.3

**Prove** that if we insert an item into a BST that is already in that
tree, then the resulting tree is identical to the original tree.

*Hint:* Use a proof of trichotomy! We have filled in the structure for
you.

```agda
 insert-same-tree-property-ex : (y : X) (t : BT X) (i : is-bst t)
                              → y ∈ₛ (t , i)
                              → fst (insert y (t , i)) ≡ t
 insert-same-tree-property-ex y (branch x l r) (s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x l r γ
        → insert'-branch y x l r γ ≡ branch x l r
   goal (inl      y<x)  x∈ₛt
    = ap (λ - → branch x - r) (insert-same-tree-property-ex y l il x∈ₛt)
   goal (inr (inl y≡x)) x∈ₛt
    = refl (branch x l r)
   goal (inr (inr x<y)) x∈ₛt
    = ap (branch x l) (insert-same-tree-property-ex y r ir x∈ₛt)
```

## Exercise 2.5

In the lecture, we prove that the efficient membership implies the
original membership on BSTs.

Now, **prove** the other direction of this.

```agda

 all-smaller-means-smaller
  : (y x : X) (l : BT X) → all-smaller l x → y ∈ l → y < x
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inl      y≡z )
  = transport (_< x) (sym y≡z) z<x
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inr (inl y∈l))
  = all-smaller-means-smaller y x l sl y∈l
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inr (inr y∈r))
  = all-smaller-means-smaller y x r sr y∈r

 all-bigger-means-bigger
  : (y x : X) (r : BT X) → all-bigger r x → y ∈ r → y > x
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inl      y≡z )
  = transport (_> x) (sym y≡z) z>x
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inr (inl y∈l))
  = all-bigger-means-bigger y x l bl y∈l
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inr (inr y∈r))
  = all-bigger-means-bigger y x r br y∈r
 
 membership'-implies-membership : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ' (t , i) → y ∈ₛ (t , i)
 membership'-implies-membership y t@(branch x l r) i@(s , b , il , ir)
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → y ∈ₛ' (t , i)
        → ∈ₛ-branch y x l r γ
   goal (inl      y<x ) (inl      y≡x )
    = 𝟘-nondep-elim (<-irreflexive' ρ y≡x y<x)
   goal (inl      y<x ) (inr (inl y∈l))
    = membership'-implies-membership y l il y∈l
   goal (inl      y<x ) (inr (inr y∈r))
    = 𝟘-nondep-elim (<-antisymmetric ρ y x y<x
        (all-bigger-means-bigger y x r b y∈r))
   goal (inr (inl y≡x)) _ = ⋆
   goal (inr (inr y>x)) (inl      y≡x )
    = 𝟘-nondep-elim (<-irreflexive' ρ (sym y≡x) y>x)
   goal (inr (inr y>x)) (inr (inl y∈l))
    = 𝟘-nondep-elim (<-antisymmetric ρ x y y>x
        (all-smaller-means-smaller y x l s y∈l))
   goal (inr (inr y>x)) (inr (inr y∈r))
    = membership'-implies-membership y r ir y∈r
```

## Exercise 2.6

**Prove** that if we insert an item into a binary search tree, the
size either remains the same or increases by one.

```agda
 insert-size-property-ex : (x : X) (t : BT X) (i : is-bst t)
                         → (size (fst (insert x (t , i))) ≡ size t)
                         ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property-ex y leaf i = inr (refl 1)
 insert-size-property-ex y t@(branch x l r) (s , b , il , ir)
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
        (insert-size-property-ex y l il)
   goal (inr (inl y≡x)) = inl (refl _)
   goal (inr (inr y>x))
    = ∔-nondep-elim
        (λ e → inl (ap (λ - → suc (size l + -)) e))
        (λ e → inr (ap suc
                     (trans (ap (size l +_) e)
                     (sym (+-assoc (size l) (size r) 1)))))
        (insert-size-property-ex y r ir)
```

## Exercise 2.7

**Prove** that if an item is a member of a binary search tree that it
is inserted into.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda
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

 insert-membership-property-ex : (x : X) (t : BT X) (i : is-bst t)  
                               → x ∈ₛ insert x (t , i)
 insert-membership-property-ex x leaf i = goal (trichotomy x x)
  where
   goal : (γ : Trichotomy x x)
        → ∈ₛ-branch x x leaf leaf γ
   goal (inl x<x) = <-irreflexive ρ x x<x 
   goal (inr (inl x≡x)) = ⋆
   goal (inr (inr x<x)) = <-irreflexive ρ x x<x 
 insert-membership-property-ex x (branch y l r) (s , b , il , ir)
  = goal (trichotomy x y)
  where
   goal : (γ : Trichotomy x y)
        → x ∈ₛ-bst insert'-branch x y l r γ
   goal (inl x<y)
    = ∈ₛ-branch-left x y (insert' x l) r
        (trichotomy x y) x<y (insert-membership-property-ex x l il)
   goal (inr (inl x≡y))
    = ∈ₛ-branch-middle x y l r (trichotomy x y) x≡y
   goal (inr (inr x>y))
    = ∈ₛ-branch-right x y l (insert' x r)
        (trichotomy x y) x>y (insert-membership-property-ex x r ir)
```

## Exercise 2.8

**Prove** that if an element `y` is in the tree `insert x t`, then `y`
is either equal to `x` or is in the tree `t`.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda

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
  
 membership-insert-property-ex : (x y : X) (t : BT X) (i : is-bst t)
                               → y ∈ₛ insert x (t , i)
                               → (y ≡ x) ∔ (y ∈ₛ (t , i))
 membership-insert-property-ex x y leaf i
  = goal (trichotomy y x)
  where
   goal : (γ : Trichotomy y x)
        → ∈ₛ-branch y x leaf leaf γ
        → (y ≡ x) ∔ 𝟘
   goal (inl y<x) ()
   goal (inr (inl y≡x)) ⋆ = inl y≡x
   goal (inr (inr y>x)) ()
 membership-insert-property-ex x y (branch z l r) (s , b , il , ir)
  = goal (trichotomy x z) (trichotomy y z)
  where
   goal : (γ : Trichotomy x z)
        → (ζ : Trichotomy y z)
        → y ∈ₛ-bst insert'-branch x z l r γ
        → (y ≡ x) ∔ ∈ₛ-branch y z l r ζ
   goal (inl x<z) (inl y<z) y∈t
    = membership-insert-property-ex x y l il
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
    = membership-insert-property-ex x y r ir
        (∈ₛ-branch-right' y z l (insert' x r) (trichotomy y z) y>z y∈t)
```

# Bonus Exercise - Part 1

```
 all-smaller-list : List X → X → Type
 all-smaller-list [] y = 𝟙
 all-smaller-list (x :: xs) y = x < y × all-smaller-list xs y

 all-bigger-list : List X → X → Type
 all-bigger-list [] y = 𝟙
 all-bigger-list (x :: xs) y = x > y × all-bigger-list xs y

 flatten-preserves-all-smaller
  : (y : X) (t : BT X)
  → all-smaller t y
  → all-smaller-list (flatten t) y
 flatten-preserves-all-smaller y leaf ⋆ = ⋆
 flatten-preserves-all-smaller y (branch x l r) (x<y , sl , sr)
  = goal (flatten l) (flatten r)
         (flatten-preserves-all-smaller y l sl)
         (flatten-preserves-all-smaller y r sr) x<y
  where
   goal : (as bs : List X)
        → all-smaller-list as y
        → all-smaller-list bs y
        → x < y
        → all-smaller-list (as ++ [ x ] ++ bs) y
   goal [] bs as<y bs<y x<y
    = x<y , bs<y
   goal (a :: as) bs (a<y , as<y) bs<y x<y
    = a<y , goal as bs as<y bs<y x<y

 flatten-preserves-all-bigger
  : (y : X) (t : BT X)
  → all-bigger t y
  → all-bigger-list (flatten t) y
 flatten-preserves-all-bigger y leaf ⋆ = ⋆
 flatten-preserves-all-bigger y (branch x l r) (x>y , bl , br)
  = goal (flatten l) (flatten r)
         (flatten-preserves-all-bigger y l bl)
         (flatten-preserves-all-bigger y r br) x>y
  where
   goal : (as bs : List X)
        → all-bigger-list as y
        → all-bigger-list bs y
        → x > y
        → all-bigger-list (as ++ [ x ] ++ bs) y
   goal [] bs as>y bs>y x>y
    = x>y , bs>y
   goal (a :: as) bs (a>y , as>y) bs>y x>y
    = a>y , goal as bs as>y bs>y x>y

 sorted-double-append
  : (x : X)
  → (as bs : List X) → Sorted ρ as → Sorted ρ bs
  → all-smaller-list as x → all-bigger-list bs x 
  → Sorted ρ (as ++ [ x ] ++ bs)
 sorted-double-append x [] [] Sa Sb as<x bs>x = sing-sorted x
 sorted-double-append x [] (b :: bs) Sa Sb as<x (b>x , bs>x)
  = adj-sorted bs (fst b>x) Sb
 sorted-double-append x (a :: []) [] Sa Sb (a<x , as<x) bs>x
  = adj-sorted _ (fst a<x) (sing-sorted x)
 sorted-double-append x (a :: []) (b :: bs) Sa Sb (a<x , as<x) (b>x , bs>x)
  = adj-sorted _ (fst a<x) (adj-sorted _ (fst b>x) Sb)
 sorted-double-append x (a :: a' :: as) bs (adj-sorted _ a≤a' Sa) Sb
   (a<x , a'<x , as<x) bs>x
  = adj-sorted _ a≤a' (sorted-double-append x (a' :: as) bs Sa Sb
    (a'<x , as<x) bs>x)

 flattened-BST-is-sorted : (t : BT X) → is-bst t → Sorted ρ (flatten t)
 flattened-BST-is-sorted leaf i = nil-sorted
 flattened-BST-is-sorted (branch x l r) (s , b , il , ir)
  = sorted-double-append x
      (flatten l) (flatten r)
      (flattened-BST-is-sorted l il) (flattened-BST-is-sorted r ir)
      (flatten-preserves-all-smaller x l s)
      (flatten-preserves-all-bigger x r b)
```
