```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

open import prelude
open import Fin
open import natural-numbers-functions
open import searchability hiding (min)
open import decidability
open import Maybe
open import List-functions
open import negation

module Dijkstra (#vertices : ℕ) where
```

# Dijkstra's algorithm for finding shortest distances in a weighted graph

We use
[Wikipedia](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm),
filling the gaps and removing imprecisions.

## Simplified form of Dijkstra's algorithm

```pseudocode
 1 function Dijkstra(Graph, source):
 2
 3      for each vertex v in Graph.Vertices:
 4          dist[v] ← INFINITY
 5          prev[v] ← UNDEFINED
 6          add v to Q
 7      dist[source] ← 0
 8
 9      while Q is not empty:
10          u ← vertex in Q with minimum dist[u]
11          remove u from Q
12
13          for each neighbor v of u still in Q:
14              alt ← dist[u] + Graph.Edges(u, v)
15              if alt < dist[v]:
16                  dist[v] ← alt
17                  prev[v] ← u
18
19      return dist[], prev[]
```

## Informal proof

What we want to prove is that, at the end of the algorithm, the following *specification* holds.
1. `dist[u]` is the shortest distance from `source` to `u`.
1. `prev[u]` is the last vertex visited on the way from `source` to `u` in the shortest path associated to the above shortest distance.

For the sake of simplicity, we will not discuss the second condition
here, focusing our attention on arguing that this algorithm
does indeed compute shortest *distances*.

In order to do that, we use the following proof technique.

1. We define an *invarian2t* as follows.
   1. For each visited node `v`, we have that `dist[v]` is the shortest distance from `source` to `v`.
   1. For each unvisited node `u`, we have that `dist[u]` is the shortest distance from source to u when traveling via visited nodes only, or infinity if no such path exists.

1. The initial state satisfies the invariant.

1. If the invariant holds at the beginning of the while look body, then it also holds at the end of the body.

1. When the queue is empty, the invariant implies the specification.

## Disjkstra using a priority queue

```pseudocode
1   function Dijkstra(Graph, source):
2       create vertex priority queue Q
3
4       dist[source] ← 0                          // Initialization
5       Q.add_with_priority(source, 0)            // associated priority equals dist[·]
6
7       for each vertex v in Graph.Vertices:
8           if v ≠ source
9               prev[v] ← UNDEFINED               // Predecessor of v
10              dist[v] ← INFINITY                // Unknown distance from source to v
11              Q.add_with_priority(v, INFINITY)
12
13
14      while Q is not empty:                     // The main loop
15          u ← Q.extract_min()                   // Remove and return best vertex
16          for each neighbor v of u:             // Go through all v neighbors of u
17              alt ← dist[u] + Graph.Edges(u, v)
18              if alt < dist[v]:
19                  prev[v] ← u
20                  dist[v] ← alt
21                  Q.decrease_priority(v, alt)
22
23      return dist, prev
```

# Extending the type of natural numbers with a point at infinity

```
data Weight : Type where
 finite : ℕ → Weight
 ∞      : Weight

data is-finite : Weight → Type where
 finite : (n : ℕ) → is-finite (finite n)

data is-infinite : Weight → Type where
 infinite : is-infinite ∞

_+ʷ_ : Weight → Weight → Weight
finite m +ʷ finite n = finite (m + n)
finite m +ʷ ∞        = ∞
∞        +ʷ y        = ∞

data _≤ʷ_ : Weight → Weight → Type where
 finite   : (m n : ℕ) → m ≤ n → finite m ≤ʷ finite n
 infinite : (x : Weight) → x ≤ʷ ∞

≤ʷ-refl : (x : Weight) → x ≤ʷ x
≤ʷ-refl (finite x) = finite x x (≤-refl x)
≤ʷ-refl ∞ = infinite ∞

≤ʷ-trans : (x y z : Weight) → x ≤ʷ y → y ≤ʷ z → x ≤ʷ z
≤ʷ-trans (finite m) (finite n) (finite k) (finite .m .n a) (finite .n .k b) = finite m k (≤-trans m n k a b)
≤ʷ-trans (finite m) (finite n) ∞ a b = infinite (finite m)
≤ʷ-trans (finite m) ∞ ∞ a b = a
≤ʷ-trans ∞ ∞ ∞ a b = a

¬-≤ʷ-flip : (x y : Weight) → ¬ (x ≤ʷ y) → y ≤ʷ x
¬-≤ʷ-flip (finite m) (finite n) f = finite n m (¬-≤-flip m n (contrapositive (finite m n) f))
¬-≤ʷ-flip ∞ (finite n) f = infinite (finite n)
¬-≤ʷ-flip (finite x) ∞ f = 𝟘-elim (f (infinite (finite x)))
¬-≤ʷ-flip ∞ ∞ f = infinite ∞

≤-cancel-finite : (m n : ℕ) → finite m ≤ʷ finite n → m ≤ n
≤-cancel-finite m n (finite .m .n l) = l

∞-not-≤-finite : (n : ℕ) → ¬ (∞ ≤ʷ finite n)
∞-not-≤-finite n ()

≤ʷ-decidable : (x y : Weight) → is-decidable (x ≤ʷ y)
≤ʷ-decidable (finite m) (finite n) =
 ∔-nondep-elim
  (λ (l : m ≤ n)
        → inl (finite m n l))
  (λ (ν : ¬ (m ≤ n))
        → inr (λ (l : finite m ≤ʷ finite n) → ν (≤-cancel-finite m n l)))
  (≤-decidable m n)
≤ʷ-decidable (finite m) ∞ = inl (infinite (finite m))
≤ʷ-decidable ∞ (finite n) = inr (λ (l : ∞ ≤ʷ finite n) → ∞-not-≤-finite n l)
≤ʷ-decidable ∞ ∞ = inl (infinite ∞)

minʷ : Weight → Weight → Weight
minʷ (finite x) (finite y) = finite (min x y)
minʷ (finite x) ∞ = finite x
minʷ ∞ y = y
```

## The types of vertices, edges, graphs and paths

```agda

module graph-notions (#vertices : ℕ) where

 Vertex : Type
 Vertex = Fin #vertices

 Edge : Type
 Edge = Vertex × Vertex

 Graph : Type
 Graph = Edge → Weight

 data path-from_to_ : Vertex → Vertex → Type where
  -- empty : (v : Vertex) → path-from v to v
  singl : (u v : Vertex) → path-from u to v
  cons  : (u v {w} : Vertex)
        → path-from v to w
        → path-from u to w

 Path : Type
 Path = Σ (u , v) ꞉ Vertex × Vertex , path-from u to v

 path-distance : Graph → {u v : Vertex} → path-from u to v → Weight
 path-distance g (singl u v) = g (u , v)
 path-distance g (cons u v p) = g (u , v) +ʷ path-distance g p

module wikipedia-example where

 open graph-notions 7

 pattern 𝟎     = zero
 pattern 𝟏     = suc 𝟎
 pattern 𝟐     = suc 𝟏
 pattern 𝟑     = suc 𝟐
 pattern 𝟒     = suc 𝟑
 pattern 𝟓     = suc 𝟒
 pattern 𝟔     = suc 𝟓

 g : Graph
 g (𝟏 , 𝟐) = finite 7
 g (𝟏 , 𝟑) = finite 9
 g (𝟏 , 𝟔) = finite 14
 g (𝟐 , 𝟏) = finite 7
 g (𝟐 , 𝟑) = finite 10
 g (𝟐 , 𝟒) = finite 15
 g (𝟑 , 𝟏) = finite 7
 g (𝟑 , 𝟐) = finite 10
 g (𝟑 , 𝟒) = finite 11
 g (𝟑 , 𝟔) = finite 2
 g (𝟒 , 𝟐) = finite 15
 g (𝟒 , 𝟑) = finite 11
 g (𝟒 , 𝟓) = finite 6
 g (𝟓 , 𝟒) = finite 6
 g (𝟓 , 𝟔) = finite 9
 g (𝟏 , 𝟏) = finite 𝟎
 g (𝟐 , 𝟐) = finite 𝟎
 g (𝟑 , 𝟑) = finite 𝟎
 g (𝟒 , 𝟒) = finite 𝟎
 g (𝟓 , 𝟓) = finite 𝟎
 g (𝟔 , 𝟔) = finite 𝟎
 g _ = ∞

 -- 1 3 4 5
 path-example : path-from 𝟏 to 𝟓
 path-example = cons 𝟏 𝟑 (cons 𝟑 𝟒 (singl 𝟒 𝟓))

```

# Dijkstra's state for simplified algorithm

To be filled during the lecture.

# Dijkstra's specification for simplified algorithm

# Dijkstra's invariant for simplified algorithm

# Updating a function

```agda
module updater
        (X : Type)
        (δ : has-decidable-equality X)
        {Y : Type}
        (f : X → Y)
        (x₀ : X) (y₀ : Y)
       where

 update-lemma : Σ f' ꞉ (X → Y)
                     , (f' x₀ ≡ y₀)
                     × ((x : X) → x ≢ x₀ → f' x ≡ f x)
 update-lemma = f' , I (δ x₀ x₀) , (λ x → II x (δ x x₀))
  where
   h : (x : X) → is-decidable (x ≡ x₀) → Y
   h x (inl _) = y₀
   h x (inr _) = f x

   f' : X → Y
   f' x = h x (δ x x₀)

   I : (d : is-decidable (x₀ ≡ x₀)) → h x₀ d ≡ y₀
   I (inl e) = refl (h x₀ (inl e))
   I (inr ν) = 𝟘-nondep-elim (ν (refl x₀))

   II : (x : X) (d : is-decidable (x ≡ x₀)) → x ≢ x₀ → h x d ≡ f x
   II x (inl e) ν = 𝟘-nondep-elim (ν e)
   II x (inr _) _ = refl (f x)

 update : X → Y
 update = fst update-lemma

 private
  f' = update

 update₀ : f' x₀ ≡ y₀
 update₀ = fst (snd update-lemma)

 update₁ : (x : X) → x ≢ x₀ → f' x ≡ f x
 update₁ = snd (snd update-lemma)

```

# Dijkstra' algorithm without priority queues

```agda
open graph-notions #vertices
open import Fin-functions
open updater Vertex Fin-has-decidable-equality

dijkstra-spec : Type
dijkstra-spec =
   (g : Graph) (source dest : Vertex)
 → Σ p ꞉ path-from source to dest
 , ((q : path-from source to dest) → path-distance g p ≤ʷ path-distance g q)

module dijkstra-implementation
        (g : Graph)
        (condition : (u v : Vertex) → g (u , v) ≡ finite 0 ⇔ u ≡ v)
        (source : Vertex)
       where

 dState : Type
 dState = (Vertex → Weight) × (Vertex → Bool) × (Vertex → Maybe Vertex)

 _is-shortest-distance-from_to_ : (x : Weight) (u v : Vertex) → Type
 x is-shortest-distance-from u to v =
  (p : path-from u to v) → x ≤ʷ path-distance g p

 path_visits-only_ : {u v : Vertex}
                     (p : path-from u to v)
                     (visited : Vertex → Bool)
                   → Type
 path (singl u v) visits-only visited
  = (visited u ≡ true) × (visited v ≡ true)
 path (cons u v p) visits-only visited
  = (visited u ≡ true) × (path p visits-only visited)

 _is-shortest-distance-from_to_when-travelling-via_
  : (x : Weight)
    (u v : Vertex)
    (visited : Vertex → Bool)
  → Type
 x is-shortest-distance-from u to v when-travelling-via visited
   = (p : path-from u to v)
   → path p visits-only visited
   → x ≤ʷ path-distance g p

 initial-dState : dState
 initial-dState = (λ _ → ∞) , (λ _ → false) , (λ _ → nothing)

 has-unvisited-vertex : dState → Type
 has-unvisited-vertex (dist , visited , prev)
  = Σ v ꞉ Vertex , visited v ≡ false

 has-unvisited-vertex-is-decidable
  : (s : dState) → is-decidable (has-unvisited-vertex s)
 has-unvisited-vertex-is-decidable (dist , visited , prev)
  = Fin-is-searchable
     #vertices
     (λ v → visited v ≡ false)
     (λ v → Bool-has-decidable-equality (visited v) false)

 is-final : dState → Type
 is-final (dist , visited , prev) = (v : Vertex) → visited v ≡ true

 dijkstra-step : (s : dState) → has-unvisited-vertex s → dState
 dijkstra-step = {!!}

 dijkstra-loop : {!!}
 dijkstra-loop = {!!}

 doesnt-have-unvisited-nodes-implies-is-final
  : (s : dState)
  → ¬ has-unvisited-vertex s
  → is-final s
 doesnt-have-unvisited-nodes-implies-is-final
  = {!!}

 invariant : dState → Type
 invariant (dist , visited , prev) =
    ((v : Vertex)
        → visited v ≡ true
        → dist v is-shortest-distance-from source to v)

  × ((v : Vertex)
        → visited v ≡ false
        → dist v is-shortest-distance-from source to v when-travelling-via visited)

 initial-dState-satisfies-invariant : invariant initial-dState
 initial-dState-satisfies-invariant = {!!}

 dijkstra-step-preserves-invariant : (s : dState)
                                   → invariant s
                                   → (h : has-unvisited-vertex s)
                                   → invariant (dijkstra-step s h)
 dijkstra-step-preserves-invariant = {!!}

 invariant-and-all-visited-gives-dist-correctness
   : (s@(dist , visited , prev) : dState)
   → invariant s
   → is-final s
   → (v : Vertex) → dist v is-shortest-distance-from source to v
 invariant-and-all-visited-gives-dist-correctness = {!!}
```

# min-priority-queues

```
record pQueue (A : Type) : Type₁ where
 field
  Q : Type
  ⟨⟩ : Q
  _∈_ : A → Q → Type
```

# Dijkstra' algorithm with priority queues

```
module dijkstra-implementation-with-pQueue
        (G : Graph)
        (source : Vertex)
        (pQueue-implementation : pQueue Vertex)
       where

 open pQueue pQueue-implementation

 dState : Type
 dState = (Vertex → Weight) × Q × (Vertex → Maybe Vertex)

```
