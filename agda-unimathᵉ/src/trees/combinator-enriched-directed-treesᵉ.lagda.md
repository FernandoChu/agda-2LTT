# Combinators of enriched directed trees

```agda
module trees.combinator-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.maybeᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ

open import trees.combinator-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.enriched-directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.equivalences-enriched-directed-treesᵉ
open import trees.fibers-enriched-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
```

</details>

## Idea

Theᵉ **combinatorᵉ operation**ᵉ onᵉ enrichedᵉ directedᵉ treesᵉ combines,ᵉ forᵉ anyᵉ
elementᵉ `aᵉ : A`,ᵉ aᵉ familyᵉ ofᵉ enrichedᵉ directedᵉ treesᵉ
`Tᵉ : B(aᵉ) → Enriched-Directed-Treeᵉ Aᵉ B`ᵉ indexedᵉ byᵉ `Bᵉ a`ᵉ intoᵉ aᵉ singleᵉ treeᵉ
enrichedᵉ directedᵉ treeᵉ with aᵉ newᵉ root.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ}
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  directed-tree-combinator-Enriched-Directed-Treeᵉ :
    Directed-Treeᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  directed-tree-combinator-Enriched-Directed-Treeᵉ =
    combinator-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  node-combinator-Enriched-Directed-Treeᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ)
  node-combinator-Enriched-Directed-Treeᵉ =
    node-combinator-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  node-inclusion-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) → node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) →
    node-combinator-Enriched-Directed-Treeᵉ
  node-inclusion-combinator-Enriched-Directed-Treeᵉ =
    node-inclusion-combinator-Directed-Treeᵉ

  root-combinator-Enriched-Directed-Treeᵉ :
    node-combinator-Enriched-Directed-Treeᵉ
  root-combinator-Enriched-Directed-Treeᵉ = root-combinator-Directed-Treeᵉ

  edge-combinator-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-combinator-Enriched-Directed-Treeᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  edge-combinator-Enriched-Directed-Treeᵉ =
    edge-combinator-Directed-Treeᵉ (directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  graph-combinator-Enriched-Directed-Treeᵉ :
    Directed-Graphᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  graph-combinator-Enriched-Directed-Treeᵉ =
    graph-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  directed-tree-inclusion-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
      ( directed-tree-combinator-Enriched-Directed-Treeᵉ)
  directed-tree-inclusion-combinator-Enriched-Directed-Treeᵉ =
    inclusion-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  walk-combinator-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-combinator-Enriched-Directed-Treeᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  walk-combinator-Enriched-Directed-Treeᵉ =
    walk-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  walk-inclusion-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)) →
    walk-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ yᵉ →
    walk-combinator-Enriched-Directed-Treeᵉ
      ( node-inclusion-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ)
      ( node-inclusion-combinator-Enriched-Directed-Treeᵉ bᵉ yᵉ)
  walk-inclusion-combinator-Enriched-Directed-Treeᵉ =
    walk-inclusion-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  walk-to-root-combinator-Enriched-Directed-Treeᵉ :
    (xᵉ : node-combinator-Enriched-Directed-Treeᵉ) →
    walk-combinator-Enriched-Directed-Treeᵉ xᵉ
      root-combinator-Enriched-Directed-Treeᵉ
  walk-to-root-combinator-Enriched-Directed-Treeᵉ =
    walk-to-root-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-root-combinator-Enriched-Directed-Treeᵉ :
    node-combinator-Enriched-Directed-Treeᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-root-combinator-Enriched-Directed-Treeᵉ =
    is-root-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  unique-direct-successor-combinator-Enriched-Directed-Treeᵉ :
    unique-direct-successor-Directed-Graphᵉ
      ( graph-combinator-Enriched-Directed-Treeᵉ)
      ( root-combinator-Enriched-Directed-Treeᵉ)
  unique-direct-successor-combinator-Enriched-Directed-Treeᵉ =
    unique-direct-successor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-tree-combinator-Enriched-Directed-Treeᵉ :
    is-tree-Directed-Graphᵉ graph-combinator-Enriched-Directed-Treeᵉ
  is-tree-combinator-Enriched-Directed-Treeᵉ =
    is-tree-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  base-combinator-Enriched-Directed-Treeᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  base-combinator-Enriched-Directed-Treeᵉ =
    base-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-proper-node-combinator-Enriched-Directed-Treeᵉ :
    node-combinator-Enriched-Directed-Treeᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-proper-node-combinator-Enriched-Directed-Treeᵉ =
    is-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  proper-node-combinator-Enriched-Directed-Treeᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ)
  proper-node-combinator-Enriched-Directed-Treeᵉ =
    proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-proper-node-inclusion-combinator-Enriched-Directed-Treeᵉ :
    {bᵉ : Bᵉ aᵉ} {xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)} →
    is-proper-node-combinator-Enriched-Directed-Treeᵉ
      ( node-inclusion-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ)
  is-proper-node-inclusion-combinator-Enriched-Directed-Treeᵉ =
    is-proper-node-inclusion-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  shape-combinator-Enriched-Directed-Treeᵉ :
    node-combinator-Enriched-Directed-Treeᵉ → Aᵉ
  shape-combinator-Enriched-Directed-Treeᵉ root-combinator-Directed-Treeᵉ = aᵉ
  shape-combinator-Enriched-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ) =
    shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ

  map-root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    Bᵉ aᵉ →
    Σᵉ ( node-combinator-Enriched-Directed-Treeᵉ)
      ( λ yᵉ →
        edge-combinator-Enriched-Directed-Treeᵉ yᵉ root-combinator-Directed-Treeᵉ)
  pr1ᵉ (map-root-enrichment-combinator-Enriched-Directed-Treeᵉ bᵉ) =
    node-inclusion-combinator-Directed-Treeᵉ bᵉ
      ( root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
  pr2ᵉ (map-root-enrichment-combinator-Enriched-Directed-Treeᵉ bᵉ) =
    edge-to-root-combinator-Directed-Treeᵉ bᵉ

  map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    Σᵉ ( node-combinator-Enriched-Directed-Treeᵉ)
      ( λ yᵉ →
        edge-combinator-Enriched-Directed-Treeᵉ yᵉ
          root-combinator-Directed-Treeᵉ) →
    Bᵉ aᵉ
  map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ
    (.ᵉ_ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ bᵉ) = bᵉ

  is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    ( map-root-enrichment-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ
    ( ._ ,ᵉ edge-to-root-combinator-Directed-Treeᵉ bᵉ) = reflᵉ

  is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    ( map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-root-enrichment-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ bᵉ =
    reflᵉ

  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    is-equivᵉ map-root-enrichment-combinator-Enriched-Directed-Treeᵉ
  is-equiv-map-root-enrichment-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ
      is-section-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ
      is-retraction-map-inv-root-enrichment-combinator-Enriched-Directed-Treeᵉ

  root-enrichment-combinator-Enriched-Directed-Treeᵉ :
    Bᵉ aᵉ ≃ᵉ
    Σᵉ ( node-combinator-Enriched-Directed-Treeᵉ)
      ( λ yᵉ →
        edge-combinator-Enriched-Directed-Treeᵉ yᵉ root-combinator-Directed-Treeᵉ)
  pr1ᵉ root-enrichment-combinator-Enriched-Directed-Treeᵉ =
    map-root-enrichment-combinator-Enriched-Directed-Treeᵉ
  pr2ᵉ root-enrichment-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-map-root-enrichment-combinator-Enriched-Directed-Treeᵉ

  enrichment-combinator-Enriched-Directed-Treeᵉ :
    (xᵉ : node-combinator-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-combinator-Enriched-Directed-Treeᵉ xᵉ) ≃ᵉ
    Σᵉ ( node-combinator-Enriched-Directed-Treeᵉ)
      ( λ yᵉ → edge-combinator-Enriched-Directed-Treeᵉ yᵉ xᵉ)
  enrichment-combinator-Enriched-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    root-enrichment-combinator-Enriched-Directed-Treeᵉ
  enrichment-combinator-Enriched-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ) =
    ( compute-direct-predecessor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ) bᵉ xᵉ) ∘eᵉ
    ( enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ)

  combinator-Enriched-Directed-Treeᵉ :
    Enriched-Directed-Treeᵉ (l2ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) Aᵉ Bᵉ
  pr1ᵉ combinator-Enriched-Directed-Treeᵉ =
    directed-tree-combinator-Enriched-Directed-Treeᵉ
  pr1ᵉ (pr2ᵉ combinator-Enriched-Directed-Treeᵉ) =
    shape-combinator-Enriched-Directed-Treeᵉ
  pr2ᵉ (pr2ᵉ combinator-Enriched-Directed-Treeᵉ) =
    enrichment-combinator-Enriched-Directed-Treeᵉ
```

## Properties

### The type of direct-predecessor of `x : T b` is equivalent to the type of direct-predecessor of the inclusion of `x` in `combinator T`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ} (bᵉ : Bᵉ aᵉ)
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
  where

  direct-predecessor-combinator-Enriched-Directed-Treeᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  direct-predecessor-combinator-Enriched-Directed-Treeᵉ =
    direct-predecessor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
      ( bᵉ)
      ( xᵉ)

  map-compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ :
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ →
    direct-predecessor-combinator-Enriched-Directed-Treeᵉ
  map-compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ =
    map-compute-direct-predecessor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
      ( bᵉ)
      ( xᵉ)

  is-equiv-map-compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ :
    is-equivᵉ map-compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ
  is-equiv-map-compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-map-compute-direct-predecessor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
      ( bᵉ)
      ( xᵉ)

  compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ :
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ ≃ᵉ
    direct-predecessor-combinator-Enriched-Directed-Treeᵉ
  compute-direct-predecessor-combinator-Enriched-Directed-Treeᵉ =
    compute-direct-predecessor-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
      ( bᵉ)
      ( xᵉ)
```

### If `e` is an edge from `node-inclusion i x` to `node-inclusion j y`, then `i ＝ j`

```agda
eq-index-edge-combinator-Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  {bᵉ : Bᵉ aᵉ} (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
  {cᵉ : Bᵉ aᵉ} (yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ cᵉ)) →
  edge-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ bᵉ xᵉ)
    ( node-inclusion-combinator-Directed-Treeᵉ cᵉ yᵉ) →
  bᵉ ＝ᵉ cᵉ
eq-index-edge-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ aᵉ Tᵉ =
  eq-index-edge-combinator-Directed-Treeᵉ
    ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
```

### The base of the combinator tree of a family `T` of enriched directed tree indexed by `B a` is equivalent to `B a`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ}
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  node-base-index-combinator-Enriched-Directed-Treeᵉ :
    Bᵉ aᵉ → node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  node-base-index-combinator-Enriched-Directed-Treeᵉ =
    node-base-index-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  edge-base-index-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    edge-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
      ( node-base-index-combinator-Enriched-Directed-Treeᵉ bᵉ)
      ( root-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
  edge-base-index-combinator-Enriched-Directed-Treeᵉ =
    edge-base-index-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  base-index-combinator-Enriched-Directed-Treeᵉ :
    Bᵉ aᵉ → base-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  base-index-combinator-Enriched-Directed-Treeᵉ =
    base-index-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  index-base-combinator-Enriched-Directed-Treeᵉ :
    base-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ → Bᵉ aᵉ
  index-base-combinator-Enriched-Directed-Treeᵉ =
    index-base-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-section-index-base-combinator-Enriched-Directed-Treeᵉ :
    ( base-index-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      index-base-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-index-base-combinator-Enriched-Directed-Treeᵉ =
    is-section-index-base-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-retraction-index-base-combinator-Enriched-Directed-Treeᵉ :
    ( index-base-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      base-index-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-index-base-combinator-Enriched-Directed-Treeᵉ =
    is-retraction-index-base-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-equiv-base-index-combinator-Enriched-Directed-Treeᵉ :
    is-equivᵉ base-index-combinator-Enriched-Directed-Treeᵉ
  is-equiv-base-index-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-base-index-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  equiv-base-index-combinator-Enriched-Directed-Treeᵉ :
    Bᵉ aᵉ ≃ᵉ base-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  equiv-base-index-combinator-Enriched-Directed-Treeᵉ =
    equiv-base-index-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
```

### The type of nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T b`, plus a root

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ}
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  map-compute-node-combinator-Enriched-Directed-Treeᵉ :
    Maybeᵉ (Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)) →
    node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  map-compute-node-combinator-Enriched-Directed-Treeᵉ =
    map-compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ :
    node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ →
    Maybeᵉ (Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ))
  map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ =
    map-inv-compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-section-map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ :
    ( map-compute-node-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ =
    is-section-map-inv-compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-retraction-map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ :
    ( map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-compute-node-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-node-combinator-Enriched-Directed-Treeᵉ =
    is-retraction-map-inv-compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-equiv-map-compute-node-combinator-Enriched-Directed-Treeᵉ :
    is-equivᵉ map-compute-node-combinator-Enriched-Directed-Treeᵉ
  is-equiv-map-compute-node-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-map-compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  compute-node-combinator-Enriched-Directed-Treeᵉ :
    Maybeᵉ (Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)) ≃ᵉ
    node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  compute-node-combinator-Enriched-Directed-Treeᵉ =
    compute-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
```

### The type of proper nodes of the combinator tree of `T` is equivalent to the dependent sum of the types of nodes of each `T b`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ}
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ) →
    proper-node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    map-compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    proper-node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ →
    Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
  map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    map-inv-compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-section-map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    ( map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    is-section-map-inv-compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-retraction-map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    ( map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ ∘ᵉ
      map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    is-retraction-map-inv-compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  is-equiv-map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    is-equivᵉ map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ
  is-equiv-map-compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-map-compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  compute-proper-node-combinator-Enriched-Directed-Treeᵉ :
    Σᵉ (Bᵉ aᵉ) (node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ) ≃ᵉ
    proper-node-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  compute-proper-node-combinator-Enriched-Directed-Treeᵉ =
    compute-proper-node-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)
```

### The fibers at a base element `b : B a` of the comibinator of a family `T` of trees is equivalent to `T b`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ}
  (Tᵉ : Bᵉ aᵉ → Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  node-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) →
    node-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
  node-compute-fiber-combinator-Enriched-Directed-Treeᵉ =
    node-fiber-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  edge-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)) →
    edge-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ yᵉ →
    edge-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ)
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ yᵉ)
  edge-compute-fiber-combinator-Enriched-Directed-Treeᵉ =
    edge-fiber-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
      ( directed-tree-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
  directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ =
    hom-fiber-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  direct-predecessor-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)) →
    direct-predecessor-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ →
    direct-predecessor-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ)
  direct-predecessor-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ =
    direct-predecessor-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
      ( directed-tree-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
      ( directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ)

  is-equiv-directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    is-equiv-hom-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
      ( directed-tree-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
      ( directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ)
  is-equiv-directed-tree-hom-compute-fiber-combinator-Enriched-Directed-Treeᵉ =
    is-equiv-hom-fiber-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    equiv-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ))
      ( directed-tree-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
  equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Treeᵉ =
    fiber-combinator-Directed-Treeᵉ
      ( directed-tree-Enriched-Directed-Treeᵉ Aᵉ Bᵉ ∘ᵉ Tᵉ)

  shape-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    ( shape-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)) ~ᵉ
    ( ( shape-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)) ∘ᵉ
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ))
  shape-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ = reflᵉ

  enrichment-compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) (xᵉ : node-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ)) →
    ( ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Treeᵉ
        ( bᵉ)
        ( xᵉ)) ∘ᵉ
      ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ)) ~ᵉ
    ( map-enrichment-fiber-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( bᵉ)
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ))
  enrichment-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ yᵉ =
    eq-map-enrichment-fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
      ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ)
      ( node-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ xᵉ)
      ( yᵉ)
      ( pr2ᵉ
        ( pr1ᵉ
          ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Treeᵉ
            ( bᵉ)
            ( xᵉ)
            ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ yᵉ))))
      ( pr2ᵉ
        ( pr2ᵉ
          ( direct-predecessor-compute-fiber-combinator-Enriched-Directed-Treeᵉ
            ( bᵉ)
            ( xᵉ)
            ( map-enrichment-Enriched-Directed-Treeᵉ Aᵉ Bᵉ (Tᵉ bᵉ) xᵉ yᵉ))))

  compute-fiber-combinator-Enriched-Directed-Treeᵉ :
    (bᵉ : Bᵉ aᵉ) →
    equiv-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
      ( Tᵉ bᵉ)
      ( fiber-Enriched-Directed-Treeᵉ Aᵉ Bᵉ
        ( combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ)
        ( node-base-index-combinator-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ bᵉ))
  pr1ᵉ (compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ) =
    equiv-directed-tree-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ
  pr1ᵉ (pr2ᵉ (compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ)) =
    shape-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ
  pr2ᵉ (pr2ᵉ (compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ)) =
    enrichment-compute-fiber-combinator-Enriched-Directed-Treeᵉ bᵉ
```