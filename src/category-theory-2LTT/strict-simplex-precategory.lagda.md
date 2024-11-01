# Strict simplex precategory

```agda
module category-theory-2LTT.strict-simplex-precategory where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-subprecategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.presheaf-categoriesᵉ
open import category-theory.representable-functors-precategoriesᵉ
open import category-theory.yoneda-lemma-precategoriesᵉ

open import category-theory-2LTT.inverse-precategories

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.strict-inequality-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.category-of-setsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-2LTT.coercing-inner-types
open import foundation-2LTT.exotypes

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definitions

### The strict simplex category

```agda
obj-strict-simplex-Precategoryᵉ : UUᵉ lzero
obj-strict-simplex-Precategoryᵉ = ℕᵉ

hom-strict-simplex-Precategoryᵉ :
  obj-strict-simplex-Precategoryᵉ →
  obj-strict-simplex-Precategoryᵉ →
  UUᵉ lzero
hom-strict-simplex-Precategoryᵉ n m =
  Σᵉ (Finᵉ (succ-ℕᵉ n) → Finᵉ (succ-ℕᵉ m))
    (λ f → preserves-le-Finᵉ (succ-ℕᵉ n) (succ-ℕᵉ m) f)

hom-set-strict-simplex-Precategoryᵉ :
  obj-strict-simplex-Precategoryᵉ →
  obj-strict-simplex-Precategoryᵉ →
  Setᵉ lzero
pr1ᵉ (hom-set-strict-simplex-Precategoryᵉ n m) =
  hom-strict-simplex-Precategoryᵉ n m
pr2ᵉ (hom-set-strict-simplex-Precategoryᵉ n m) =
  is-set-exotypeᵉ _

id-strict-simplex-Precategoryᵉ :
  (n : obj-strict-simplex-Precategoryᵉ) →
  hom-strict-simplex-Precategoryᵉ n n
pr1ᵉ (id-strict-simplex-Precategoryᵉ n) = idᵉ
pr2ᵉ (id-strict-simplex-Precategoryᵉ n) a b m = m

comp-hom-strict-simplex-Precategoryᵉ :
  {m n o : obj-strict-simplex-Precategoryᵉ} →
  hom-strict-simplex-Precategoryᵉ n o →
  hom-strict-simplex-Precategoryᵉ m n →
  hom-strict-simplex-Precategoryᵉ m o
pr1ᵉ (comp-hom-strict-simplex-Precategoryᵉ (g ,ᵉ pg) (f ,ᵉ pf)) = g ∘ᵉ f
pr2ᵉ (comp-hom-strict-simplex-Precategoryᵉ {m} {n} {o} (g ,ᵉ pg) (f ,ᵉ pf)) =
  comp-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) (succ-ℕᵉ o) g f pf pg

strict-simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
strict-simplex-Precategoryᵉ =
  make-Precategoryᵉ
    obj-strict-simplex-Precategoryᵉ
    hom-set-strict-simplex-Precategoryᵉ
    comp-hom-strict-simplex-Precategoryᵉ
    id-strict-simplex-Precategoryᵉ
    ( λ h g f → reflᵉ)
    ( λ f → reflᵉ)
    ( λ f → reflᵉ)

op-strict-simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
op-strict-simplex-Precategoryᵉ =
  opposite-Precategoryᵉ strict-simplex-Precategoryᵉ
```

### Some useful morphisms in the strict simplex category

```agda
⟨0⟩₁-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨0⟩₁-strict-simplex-Precategoryᵉ x = zero-Finᵉ 1ᵉ
pr2ᵉ ⟨0⟩₁-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨1⟩₁-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨1⟩₁-strict-simplex-Precategoryᵉ x = succ-Finᵉ 2ᵉ (zero-Finᵉ 1ᵉ)
pr2ᵉ ⟨1⟩₁-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨02⟩₂-strict-simplex-Precategoryᵉ :
  hom-strict-simplex-Precategoryᵉ 1ᵉ 2ᵉ
pr1ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ starᵉ)) = zero-Finᵉ 2ᵉ
pr1ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inrᵉ starᵉ) =
  succ-Finᵉ 3ᵉ (succ-Finᵉ 3ᵉ (zero-Finᵉ 2ᵉ))
pr2ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ x)) (inlᵉ (inrᵉ y)) p = p
pr2ᵉ ⟨02⟩₂-strict-simplex-Precategoryᵉ (inlᵉ (inrᵉ x)) (inrᵉ starᵉ) p = x
```

### Strict simplicial set

```agda
strict-simplicial-set : UUᵉ (lsuc lzero)
strict-simplicial-set =
  presheaf-Precategoryᵉ strict-simplex-Precategoryᵉ lzero

obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → Setᵉ lzero
obj-strict-simplicial-set =
  obj-functor-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)

type-obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → UUᵉ lzero
type-obj-strict-simplicial-set X n =
  type-Setᵉ (obj-strict-simplicial-set X n)
```

### The standard strict simplex

```agda
bounded-strict-simplex-Full-Subcategoryᵉ :
    ℕᵉ → Full-Subprecategoryᵉ (lzero ⊔ lzero) (strict-simplex-Precategoryᵉ)
pr1ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = le-ℕᵉ x n
pr2ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = is-prop-le-ℕᵉ x n

bounded-strict-simplex-Precategoryᵉ : ℕᵉ → Precategoryᵉ lzero lzero
bounded-strict-simplex-Precategoryᵉ n =
  precategory-Full-Subprecategoryᵉ
    ( strict-simplex-Precategoryᵉ)
    ( bounded-strict-simplex-Full-Subcategoryᵉ n)

standard-strict-simplex :
  ℕᵉ → strict-simplicial-set
standard-strict-simplex n =
  representable-functor-Precategoryᵉ op-strict-simplex-Precategoryᵉ n
```

### The horns

```agda
-- This is the type of k-cells of the horn Λʲₙ
record type-obj-horn-strict-simplex (j n k : ℕᵉ) : UUᵉ lzero where
  constructor mk-type-obj-horn-strict-simplex
  field
    hom-type-obj-horn-strict-simplex : hom-strict-simplex-Precategoryᵉ k n

  map-hom-type-obj-horn-strict-simplex : Finᵉ (succ-ℕᵉ k) → Finᵉ (succ-ℕᵉ n)
  map-hom-type-obj-horn-strict-simplex = pr1ᵉ hom-type-obj-horn-strict-simplex

  preserves-le-hom-type-obj-horn-strict-simplex :
    preserves-le-Finᵉ (succ-ℕᵉ k) (succ-ℕᵉ n)
      map-hom-type-obj-horn-strict-simplex
  preserves-le-hom-type-obj-horn-strict-simplex =
    pr2ᵉ hom-type-obj-horn-strict-simplex

  field
    hole-type-obj-horn-strict-simplex : Finᵉ (succ-ℕᵉ n)
    is-hole-hole-type-obj-horn-strict-simplex :
      ¬ᵉ (hole-type-obj-horn-strict-simplex ＝ᵉ mod-succ-ℕᵉ n j)
    empty-fiber-hole-type-obj-horn-strict-simplex :
      ¬ᵉ
        ( fiberᵉ
          map-hom-type-obj-horn-strict-simplex
          hole-type-obj-horn-strict-simplex)

open type-obj-horn-strict-simplex public

hom-horn-strict-simplex :
  (j n k l : ℕᵉ) →
  hom-Precategoryᵉ op-strict-simplex-Precategoryᵉ k l →
  type-obj-horn-strict-simplex j n k →
  type-obj-horn-strict-simplex j n l
hom-horn-strict-simplex j n k l (f ,ᵉ pf) g =
  mk-type-obj-horn-strict-simplex
    ( pairᵉ
      ( map-hom-type-obj-horn-strict-simplex g ∘ᵉ f)
      ( comp-preserves-le-Finᵉ (succ-ℕᵉ l) (succ-ℕᵉ k) (succ-ℕᵉ n)
          ( map-hom-type-obj-horn-strict-simplex g)
          ( f)
          ( pf)
          ( preserves-le-hom-type-obj-horn-strict-simplex g)))
    ( hole-type-obj-horn-strict-simplex g)
    ( is-hole-hole-type-obj-horn-strict-simplex g)
    ( λ (s ,ᵉ ps) →
      empty-fiber-hole-type-obj-horn-strict-simplex g (f s ,ᵉ ps))

-- The jth horn
horn-strict-simplex :
  ℕᵉ → ℕᵉ →
  strict-simplicial-set
pr1ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = type-obj-horn-strict-simplex j n k
pr2ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = is-set-exotypeᵉ _
pr1ᵉ (pr2ᵉ (horn-strict-simplex j n)) {x} {y} f =
  hom-horn-strict-simplex j n x y f
pr1ᵉ (pr2ᵉ (pr2ᵉ (horn-strict-simplex j n))) g f = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (horn-strict-simplex j n))) x = reflᵉ
```

### Strict simplicial maps

```agda
strict-simplicial-map :
  strict-simplicial-set →
  strict-simplicial-set →
  UUᵉ lzero
strict-simplicial-map =
  natural-transformation-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)

comp-strict-simplicial-map :
  (X Y Z : strict-simplicial-set) →
  strict-simplicial-map Y Z →
  strict-simplicial-map X Y →
  strict-simplicial-map X Z
comp-strict-simplicial-map X Y Z g f =
  comp-natural-transformation-Precategoryᵉ
    op-strict-simplex-Precategoryᵉ
    (Set-Precategoryᵉ lzero)
    X Y Z g f

horn-inclusion-strict-simplex :
  (j n : ℕᵉ) →
  strict-simplicial-map
    (horn-strict-simplex j n)
    (standard-strict-simplex n)
pr1ᵉ (horn-inclusion-strict-simplex j n) x g =
  hom-type-obj-horn-strict-simplex g
pr2ᵉ (horn-inclusion-strict-simplex j n) fᵉ = reflᵉ

strict-simplicial-map-hom-strict-simplex-Precategoryᵉ :
  (m n : ℕᵉ) →
  hom-strict-simplex-Precategoryᵉ m n →
  strict-simplicial-map
    (standard-strict-simplex m)
    (standard-strict-simplex n)
strict-simplicial-map-hom-strict-simplex-Precategoryᵉ m n =
  map-inv-equivᵉ
    ( equiv-lemma-yoneda-representable-Precategoryᵉ
      op-strict-simplex-Precategoryᵉ m n)
```

### Vertices, edges and triangles

```agda
vertex-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
vertex-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 0ᵉ)
    X

edge-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
edge-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 1ᵉ)
    X

triangle-strict-simplicial-set :
  strict-simplicial-set → UUᵉ lzero
triangle-strict-simplicial-set X =
  strict-simplicial-map
    (standard-strict-simplex 2ᵉ)
    X

domain-edge-strict-simplicial-set :
  (X : strict-simplicial-set) →
  edge-strict-simplicial-set X →
  vertex-strict-simplicial-set X
domain-edge-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 0ᵉ)
    ( standard-strict-simplex 1ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
      ⟨0⟩₁-strict-simplex-Precategoryᵉ)

codomain-edge-strict-simplicial-set :
  (X : strict-simplicial-set) →
  edge-strict-simplicial-set X →
  vertex-strict-simplicial-set X
codomain-edge-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 0ᵉ)
    ( standard-strict-simplex 1ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 0ᵉ 1ᵉ
      ⟨1⟩₁-strict-simplex-Precategoryᵉ)

hom-strict-simplicial-set :
  (X : strict-simplicial-set) →
  vertex-strict-simplicial-set X →
  vertex-strict-simplicial-set X →
  UUᵉ lzero
hom-strict-simplicial-set X x y =
  Σᵉ (edge-strict-simplicial-set X)
    ( λ f →
      ( domain-edge-strict-simplicial-set X f ＝ᵉ x) ×ᵉ
      ( codomain-edge-strict-simplicial-set X f ＝ᵉ y))

composition-triangle-strict-simplicial-set :
  (X : strict-simplicial-set) →
  triangle-strict-simplicial-set X →
  edge-strict-simplicial-set X
composition-triangle-strict-simplicial-set X f =
  comp-strict-simplicial-map
    ( standard-strict-simplex 1ᵉ)
    ( standard-strict-simplex 2ᵉ)
    ( X)
    ( f)
    ( strict-simplicial-map-hom-strict-simplex-Precategoryᵉ 1ᵉ 2ᵉ
      ⟨02⟩₂-strict-simplex-Precategoryᵉ)

-- Todo: Show that two edgex x -> y -> z induce a horn Λ¹₂
-- test :
--   (X : strict-simplicial-set) →
--   (x y z : vertex-strict-simplicial-set X) →
--   hom-strict-simplicial-set X y z →
--   hom-strict-simplicial-set X x y →
--   strict-simplicial-map (horn-strict-simplex 1ᵉ 2ᵉ) X
-- pr1ᵉ (test X x y z f g) 0ᵉ (α ,ᵉ pα) = {!case α star =ᵉ 0 !}
-- pr1ᵉ (test X x y z f g) (succ-ℕᵉ 0ᵉ) (α ,ᵉ pα) = {!!}
-- pr1ᵉ (test X x y z f g) (succ-ℕᵉ (succ-ℕᵉ m)) (α ,ᵉ pα) = {!!}
-- pr2ᵉ (test X x y z f g) = {!!}
```

## Properties

### The strict simplex precategory is inverse

```agda
hom-rank-functor-op-strict-simplex-Precategoryᵉ :
  {m n : obj-Precategoryᵉ strict-simplex-Precategoryᵉ}
  (f : hom-strict-simplex-Precategoryᵉ m n) →
  leq-ℕᵉ m n
hom-rank-functor-op-strict-simplex-Precategoryᵉ {m} {n} (f ,ᵉ pf) =
  leq-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) f pf

rank-functor-op-strict-simplex-Precategoryᵉ :
  functor-Precategoryᵉ strict-simplex-Precategoryᵉ ℕ-Precategoryᵉ
pr1ᵉ rank-functor-op-strict-simplex-Precategoryᵉ n = n
pr1ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ) =
  hom-rank-functor-op-strict-simplex-Precategoryᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ)) {m} {n} {o} g f =
  eq-is-propᵉ (is-prop-leq-ℕᵉ m o)
pr2ᵉ (pr2ᵉ (pr2ᵉ rank-functor-op-strict-simplex-Precategoryᵉ)) n =
  eq-is-propᵉ (is-prop-leq-ℕᵉ n n)

reflects-id-rank-functor-op-strict-simplex-Precategoryᵉ :
  reflects-id-functor-Precategoryᵉ
    strict-simplex-Precategoryᵉ
    ℕ-Precategoryᵉ
    rank-functor-op-strict-simplex-Precategoryᵉ
reflects-id-rank-functor-op-strict-simplex-Precategoryᵉ {m} (f ,ᵉ pf) p =
  eq-pair-Σᵉ
    ( eq-htpyᵉ (λ x → lemma m (f ,ᵉ pf) x (f (inrᵉ starᵉ)) reflᵉ))
    ( eq-is-propᵉ (is-prop-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) idᵉ))
  where
    lemma :
      (m : obj-strict-simplex-Precategoryᵉ) →
      ((f ,ᵉ pf) : hom-strict-simplex-Precategoryᵉ m m) →
      (x : Finᵉ (succ-ℕᵉ m)) →
      (y : Finᵉ (succ-ℕᵉ m)) →
      (f (inrᵉ starᵉ) ＝ᵉ y) →
      (f x ＝ᵉ x)
    lemma 0ᵉ (f ,ᵉ pf) (inrᵉ starᵉ) y p with f (inrᵉ starᵉ)
    ... | inrᵉ starᵉ = reflᵉ
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inlᵉ x) y p =
      invᵉ (inl-restriction-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf x) ∙ᵉ
        apᵉ inlᵉ
          ( lemma m
            ( restriction-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf ,ᵉ
              preserves-le-restriction-preserves-le-Finᵉ
                ( succ-ℕᵉ m) (succ-ℕᵉ m) f pf) x
                ( restriction-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf
                  ( inrᵉ starᵉ))
                ( reflᵉ))
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inrᵉ starᵉ) (inlᵉ y) p =
      ex-falsoᵉ
        ( trᵉ (λ - → le-Finᵉ (succ-ℕᵉ (succ-ℕᵉ m)) - (inlᵉ y)) fiis
          ( trᵉ
            ( le-Finᵉ (succ-ℕᵉ (succ-ℕᵉ m)) (f (inlᵉ (inrᵉ starᵉ))))
            ( p)
            ( pf (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) starᵉ)))
      where
        fiis : f (inlᵉ (inrᵉ starᵉ)) ＝ᵉ inlᵉ (inrᵉ starᵉ)
        fiis =
          invᵉ
            ( inl-restriction-preserves-le-Finᵉ
              ( succ-ℕᵉ m) (succ-ℕᵉ m) f pf (inrᵉ starᵉ)) ∙ᵉ
          apᵉ inlᵉ
            ( lemma m
              ( restriction-preserves-le-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ m) f pf ,ᵉ
                preserves-le-restriction-preserves-le-Finᵉ
                  ( succ-ℕᵉ m) (succ-ℕᵉ m) f pf)
              ( inrᵉ starᵉ)
              ( restriction-preserves-le-Finᵉ
                ( succ-ℕᵉ m) (succ-ℕᵉ m) f pf (inrᵉ starᵉ))
              ( reflᵉ))
    lemma (succ-ℕᵉ m) (f ,ᵉ pf) (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

is-inverse-op-strict-simplex-Precategoryᵉ :
  is-inverse-Precategoryᵉ op-strict-simplex-Precategoryᵉ
pr1ᵉ is-inverse-op-strict-simplex-Precategoryᵉ =
  rank-functor-op-strict-simplex-Precategoryᵉ
pr2ᵉ is-inverse-op-strict-simplex-Precategoryᵉ =
  reflects-id-rank-functor-op-strict-simplex-Precategoryᵉ
```
