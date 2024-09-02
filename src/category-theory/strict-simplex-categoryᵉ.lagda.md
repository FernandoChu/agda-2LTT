# Inverse categories

```agda
module category-theory.strict-simplex-categoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-subprecategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.yoneda-lemma-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.representable-functors-precategoriesᵉ

open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coercing-inner-typesᵉ
open import foundation.category-of-setsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.exotypesᵉ


open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

## Definitions

### The strict simplex category

```agda
lt-Finᵉ : (k : ℕᵉ) → Finᵉ k → Finᵉ k → UUᵉ lzero
lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inlᵉ y) = lt-Finᵉ k x y
lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inrᵉ y) = unitᵉ
lt-Finᵉ (succ-ℕᵉ k) (inrᵉ x) (inlᵉ y) = emptyᵉ
lt-Finᵉ (succ-ℕᵉ k) (inrᵉ x) (inrᵉ y) = emptyᵉ

is-prop-lt-Finᵉ :
  (k : ℕᵉ) (x y : Finᵉ k) → is-propᵉ (lt-Finᵉ k x y)
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inlᵉ y) = is-prop-lt-Finᵉ k x y
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inlᵉ x) (inrᵉ star) = is-prop-unitᵉ
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inrᵉ star) (inlᵉ y) = is-prop-emptyᵉ
is-prop-lt-Finᵉ (succ-ℕᵉ k) (inrᵉ star) (inrᵉ star) = is-prop-emptyᵉ

preserves-order-lt-Finᵉ : (n m : ℕᵉ) → (Finᵉ n → Finᵉ m) → UUᵉ lzero
preserves-order-lt-Finᵉ n m f =
  (a b : Finᵉ n) →
  lt-Finᵉ n a b →
  lt-Finᵉ m (f a) (f b)

comp-preserves-order-lt-Finᵉ :
  (m n o : ℕᵉ)
  (g : Finᵉ n → Finᵉ o)
  (f : Finᵉ m → Finᵉ n) →
  preserves-order-lt-Finᵉ m n f →
  preserves-order-lt-Finᵉ n o g →
  preserves-order-lt-Finᵉ m o (g ∘ᵉ f)
comp-preserves-order-lt-Finᵉ m n o g f pf pg a b H =
  pg (f a) (f b) (pf a b H)

obj-strict-simplex-Categoryᵉ : UUᵉ lzero
obj-strict-simplex-Categoryᵉ = ℕᵉ

hom-strict-simplex-Categoryᵉ :
  obj-strict-simplex-Categoryᵉ → obj-strict-simplex-Categoryᵉ → UUᵉ lzero
hom-strict-simplex-Categoryᵉ n m =
  Σᵉ (Finᵉ (succ-ℕᵉ n) → Finᵉ (succ-ℕᵉ m))
    (λ f → preserves-order-lt-Finᵉ (succ-ℕᵉ n) (succ-ℕᵉ m) f)

hom-set-strict-simplex-Categoryᵉ :
  obj-strict-simplex-Categoryᵉ → obj-strict-simplex-Categoryᵉ → Setᵉ lzero
pr1ᵉ (hom-set-strict-simplex-Categoryᵉ n m) = hom-strict-simplex-Categoryᵉ n m
pr2ᵉ (hom-set-strict-simplex-Categoryᵉ n m) = is-setᵉ-exotype _

id-strict-simplex-Categoryᵉ :
  (n : obj-strict-simplex-Categoryᵉ) →
  hom-strict-simplex-Categoryᵉ n n
pr1ᵉ (id-strict-simplex-Categoryᵉ n) = idᵉ
pr2ᵉ (id-strict-simplex-Categoryᵉ n) a b m = m

comp-hom-strict-simplex-Categoryᵉ :
  {m n o : obj-strict-simplex-Categoryᵉ} →
  hom-strict-simplex-Categoryᵉ n o →
  hom-strict-simplex-Categoryᵉ m n →
  hom-strict-simplex-Categoryᵉ m o
pr1ᵉ (comp-hom-strict-simplex-Categoryᵉ (g ,ᵉ pg) (f ,ᵉ pf)) = g ∘ᵉ f
pr2ᵉ (comp-hom-strict-simplex-Categoryᵉ {m} {n} {o} (g ,ᵉ pg) (f ,ᵉ pf)) =
  comp-preserves-order-lt-Finᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) (succ-ℕᵉ o) g f pf pg

strict-simplex-Categoryᵉ : Precategoryᵉ lzero lzero
strict-simplex-Categoryᵉ =
  make-Precategoryᵉ
    obj-strict-simplex-Categoryᵉ 
    hom-set-strict-simplex-Categoryᵉ 
    comp-hom-strict-simplex-Categoryᵉ  
    id-strict-simplex-Categoryᵉ 
    ( λ h g f → reflᵉ)
    ( λ f → reflᵉ)
    ( λ f → reflᵉ)

⟨0⟩₁-strict-simplex-Categoryᵉ :
  hom-strict-simplex-Categoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨0⟩₁-strict-simplex-Categoryᵉ x = zero-Finᵉ 1ᵉ
pr2ᵉ ⟨0⟩₁-strict-simplex-Categoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨1⟩₁-strict-simplex-Categoryᵉ :
  hom-strict-simplex-Categoryᵉ 0ᵉ 1ᵉ
pr1ᵉ ⟨1⟩₁-strict-simplex-Categoryᵉ x = succ-Finᵉ 2ᵉ (zero-Finᵉ 1ᵉ)
pr2ᵉ ⟨1⟩₁-strict-simplex-Categoryᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) p = p

⟨02⟩₂-strict-simplex-Categoryᵉ :
  hom-strict-simplex-Categoryᵉ 1ᵉ 2ᵉ
pr1ᵉ ⟨02⟩₂-strict-simplex-Categoryᵉ (inlᵉ (inrᵉ starᵉ)) = zero-Finᵉ 2ᵉ 
pr1ᵉ ⟨02⟩₂-strict-simplex-Categoryᵉ (inrᵉ starᵉ) = succ-Finᵉ 3ᵉ (succ-Finᵉ 3ᵉ (zero-Finᵉ 2ᵉ))  
pr2ᵉ ⟨02⟩₂-strict-simplex-Categoryᵉ (inlᵉ (inrᵉ x)) (inlᵉ (inrᵉ y)) p = p
pr2ᵉ ⟨02⟩₂-strict-simplex-Categoryᵉ (inlᵉ (inrᵉ x)) (inrᵉ starᵉ) p = x

op-strict-simplex-Categoryᵉ : Precategoryᵉ lzero lzero
op-strict-simplex-Categoryᵉ =
  opposite-Precategoryᵉ strict-simplex-Categoryᵉ
```

### Strict simplicial set

```agda
strict-simplicial-set : UUᵉ (lsuc lzero)
strict-simplicial-set =
  copresheaf-Precategoryᵉ op-strict-simplex-Categoryᵉ lzero

obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → Setᵉ lzero
obj-strict-simplicial-set =
  obj-functor-Precategoryᵉ
    op-strict-simplex-Categoryᵉ
    (Set-Precategoryᵉ lzero)

type-obj-strict-simplicial-set :
  strict-simplicial-set →
  ℕᵉ → UUᵉ lzero
type-obj-strict-simplicial-set X n =
  type-Setᵉ (obj-strict-simplicial-set X n)
```

### The standard strict simplex

```agda
lt-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
lt-ℕᵉ 0ᵉ 0ᵉ = emptyᵉ
lt-ℕᵉ 0ᵉ (succ-ℕᵉ b) = unitᵉ
lt-ℕᵉ (succ-ℕᵉ a) 0ᵉ = emptyᵉ
lt-ℕᵉ (succ-ℕᵉ a) (succ-ℕᵉ b) = lt-ℕᵉ a b

is-prop-lt-ℕᵉ :
  (m n : ℕᵉ) → is-propᵉ (lt-ℕᵉ m n)
is-prop-lt-ℕᵉ 0ᵉ 0ᵉ = is-prop-emptyᵉ
is-prop-lt-ℕᵉ 0ᵉ (succ-ℕᵉ n) = is-prop-unitᵉ
is-prop-lt-ℕᵉ (succ-ℕᵉ m) 0ᵉ = is-prop-emptyᵉ
is-prop-lt-ℕᵉ (succ-ℕᵉ m) (succ-ℕᵉ n) = is-prop-lt-ℕᵉ m n

bounded-strict-simplex-Full-Subcategoryᵉ :
    ℕᵉ → Full-Subprecategoryᵉ (lzero ⊔ lzero) (strict-simplex-Categoryᵉ)
pr1ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = lt-ℕᵉ x n
pr2ᵉ (bounded-strict-simplex-Full-Subcategoryᵉ n x) = is-prop-lt-ℕᵉ x n

bounded-strict-simplex-Categoryᵉ : ℕᵉ → Precategoryᵉ lzero lzero
bounded-strict-simplex-Categoryᵉ n =
  precategory-Full-Subprecategoryᵉ
    ( strict-simplex-Categoryᵉ)
    ( bounded-strict-simplex-Full-Subcategoryᵉ n)

standard-strict-simplex :
  ℕᵉ → strict-simplicial-set
standard-strict-simplex n =
  representable-functor-Precategoryᵉ op-strict-simplex-Categoryᵉ n
```

### The horns

```agda
bounded-succ-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
bounded-succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = skip-zero-Finᵉ kᵉ xᵉ
bounded-succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = inrᵉ starᵉ

-- Maps n to to it's corresponding element in Fin (k + 1), bounding above.
Fin-natᵉ : (kᵉ : ℕᵉ) → ℕᵉ → Finᵉ (succ-ℕᵉ kᵉ)
Fin-natᵉ 0ᵉ 0ᵉ = zero-Finᵉ 0ᵉ
Fin-natᵉ 0ᵉ (succ-ℕᵉ n) = zero-Finᵉ 0ᵉ
Fin-natᵉ (succ-ℕᵉ k) 0ᵉ = zero-Finᵉ (succ-ℕᵉ k) 
Fin-natᵉ (succ-ℕᵉ k) (succ-ℕᵉ n) =
  bounded-succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ k)) (inl-Finᵉ (succ-ℕᵉ k) (Fin-natᵉ k n))

type-obj-horn-strict-simplex :
  ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
type-obj-horn-strict-simplex j n k =
  Σᵉ (hom-strict-simplex-Categoryᵉ k n)
    ( λ (f ,ᵉ p) →
      Σᵉ ( Finᵉ (succ-ℕᵉ n))
        ( λ r →
          ( ¬ᵉ (r ＝ᵉ Fin-natᵉ n j) ×ᵉ ¬ᵉ (fiberᵉ f r))))

hom-horn-strict-simplex :
  (j n k l : ℕᵉ) →
  hom-Precategoryᵉ op-strict-simplex-Categoryᵉ k l →
  type-obj-horn-strict-simplex j n k →
  type-obj-horn-strict-simplex j n l
pr1ᵉ (pr1ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) =
  g ∘ᵉ f 
pr2ᵉ (pr1ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) =
  comp-preserves-order-lt-Finᵉ (succ-ℕᵉ l) (succ-ℕᵉ k) (succ-ℕᵉ n) g f pf pg
pr1ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr))) = r
pr1ᵉ (pr2ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr)))) = pr
pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-horn-strict-simplex j n k l (f ,ᵉ pf) ((g ,ᵉ pg) ,ᵉ r ,ᵉ pr ,ᵉ pgr)))) (s ,ᵉ ps) =
  pgr (f s ,ᵉ ps)

-- The jth horn
horn-strict-simplex :
  ℕᵉ → ℕᵉ →
  strict-simplicial-set
pr1ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = type-obj-horn-strict-simplex j n k
pr2ᵉ (pr1ᵉ (horn-strict-simplex j n) k) = is-setᵉ-exotype _
pr1ᵉ (pr2ᵉ (horn-strict-simplex j n)) {x} {y} f = hom-horn-strict-simplex j n x y f
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
    op-strict-simplex-Categoryᵉ
    (Set-Precategoryᵉ lzero)

comp-strict-simplicial-map :
  (X Y Z : strict-simplicial-set) →
  strict-simplicial-map Y Z →
  strict-simplicial-map X Y →
  strict-simplicial-map X Z
comp-strict-simplicial-map X Y Z g f =
  comp-natural-transformation-Precategoryᵉ
    op-strict-simplex-Categoryᵉ
    (Set-Precategoryᵉ lzero)
    X Y Z g f

horn-inclusion-strict-simplex :
  (j n : ℕᵉ) →
  strict-simplicial-map
    (horn-strict-simplex j n)
    (standard-strict-simplex n)
pr1ᵉ (horn-inclusion-strict-simplex j n) x ((f ,ᵉ pf) ,ᵉ r) = (f ,ᵉ pf)
pr2ᵉ (horn-inclusion-strict-simplex j n) fᵉ = reflᵉ

strict-simplicial-map-hom-strict-simplex-Categoryᵉ :
  (m n : ℕᵉ) →
  hom-strict-simplex-Categoryᵉ m n →
  strict-simplicial-map
    (standard-strict-simplex m)
    (standard-strict-simplex n)
strict-simplicial-map-hom-strict-simplex-Categoryᵉ m n =
  map-inv-equivᵉ
    ( equiv-lemma-yoneda-representable-Precategoryᵉ
      op-strict-simplex-Categoryᵉ m n)
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
    ( strict-simplicial-map-hom-strict-simplex-Categoryᵉ 0ᵉ 1ᵉ
      ⟨0⟩₁-strict-simplex-Categoryᵉ)

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
    ( strict-simplicial-map-hom-strict-simplex-Categoryᵉ 0ᵉ 1ᵉ
      ⟨1⟩₁-strict-simplex-Categoryᵉ)

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
    ( strict-simplicial-map-hom-strict-simplex-Categoryᵉ 1ᵉ 2ᵉ
      ⟨02⟩₂-strict-simplex-Categoryᵉ)

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
