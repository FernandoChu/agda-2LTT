# Enriched directed trees

```agda
module trees.enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ

open import trees.directed-treesᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ andᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`.ᵉ Anᵉ **`(A,B)`-enrichedᵉ
directedᵉ tree**ᵉ isᵉ aᵉ directedᵉ treeᵉ `T`ᵉ equippedᵉ with aᵉ mapᵉ

```text
  shapeᵉ : node-Directed-Treeᵉ Tᵉ → Aᵉ
```

andᵉ forᵉ eachᵉ nodeᵉ `x`ᵉ anᵉ equivalenceᵉ

```text
  eᵉ : Bᵉ (shapeᵉ xᵉ) ≃ᵉ Σᵉ (node-Directed-Treeᵉ Tᵉ) (λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ xᵉ)
```

Byᵉ thisᵉ equivalence,ᵉ thereᵉ isᵉ aᵉ higherᵉ groupᵉ actionᵉ ofᵉ `Ωᵉ (Aᵉ ,ᵉ fᵉ x)`ᵉ onᵉ theᵉ typeᵉ
ofᵉ childrenᵉ ofᵉ `x`.ᵉ

## Definition

```agda
Enriched-Directed-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ =
  Σᵉ ( Directed-Treeᵉ l3ᵉ l4ᵉ)
    ( λ Tᵉ →
      Σᵉ ( node-Directed-Treeᵉ Tᵉ → Aᵉ)
        ( λ fᵉ →
          (xᵉ : node-Directed-Treeᵉ Tᵉ) →
          Bᵉ (fᵉ xᵉ) ≃ᵉ
          Σᵉ (node-Directed-Treeᵉ Tᵉ) (λ yᵉ → edge-Directed-Treeᵉ Tᵉ yᵉ xᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Tᵉ : Enriched-Directed-Treeᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  where

  directed-tree-Enriched-Directed-Treeᵉ : Directed-Treeᵉ l3ᵉ l4ᵉ
  directed-tree-Enriched-Directed-Treeᵉ = pr1ᵉ Tᵉ

  graph-Enriched-Directed-Treeᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ
  graph-Enriched-Directed-Treeᵉ =
    graph-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  node-Enriched-Directed-Treeᵉ : UUᵉ l3ᵉ
  node-Enriched-Directed-Treeᵉ =
    node-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  edge-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ) → UUᵉ l4ᵉ
  edge-Enriched-Directed-Treeᵉ =
    edge-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  direct-predecessor-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  direct-predecessor-Enriched-Directed-Treeᵉ =
    direct-predecessor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  node-direct-predecessor-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    direct-predecessor-Enriched-Directed-Treeᵉ xᵉ → node-Enriched-Directed-Treeᵉ
  node-direct-predecessor-Enriched-Directed-Treeᵉ =
    node-direct-predecessor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  edge-direct-predecessor-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ)
    (yᵉ : direct-predecessor-Enriched-Directed-Treeᵉ xᵉ) →
    edge-Enriched-Directed-Treeᵉ
      ( node-direct-predecessor-Enriched-Directed-Treeᵉ xᵉ yᵉ)
      ( xᵉ)
  edge-direct-predecessor-Enriched-Directed-Treeᵉ =
    edge-direct-predecessor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  walk-Enriched-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Enriched-Directed-Treeᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  walk-Enriched-Directed-Treeᵉ =
    walk-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  refl-walk-Enriched-Directed-Treeᵉ :
    {xᵉ : node-Enriched-Directed-Treeᵉ} → walk-Enriched-Directed-Treeᵉ xᵉ xᵉ
  refl-walk-Enriched-Directed-Treeᵉ =
    refl-walk-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  cons-walk-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ zᵉ : node-Enriched-Directed-Treeᵉ} → edge-Enriched-Directed-Treeᵉ xᵉ yᵉ →
    walk-Enriched-Directed-Treeᵉ yᵉ zᵉ → walk-Enriched-Directed-Treeᵉ xᵉ zᵉ
  cons-walk-Enriched-Directed-Treeᵉ =
    cons-walk-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  unit-walk-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ} →
    edge-Enriched-Directed-Treeᵉ xᵉ yᵉ → walk-Enriched-Directed-Treeᵉ xᵉ yᵉ
  unit-walk-Enriched-Directed-Treeᵉ =
    unit-walk-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  length-walk-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ} →
    walk-Enriched-Directed-Treeᵉ xᵉ yᵉ → ℕᵉ
  length-walk-Enriched-Directed-Treeᵉ =
    length-walk-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  root-Enriched-Directed-Treeᵉ : node-Enriched-Directed-Treeᵉ
  root-Enriched-Directed-Treeᵉ =
    root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-root-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ → UUᵉ l3ᵉ
  is-root-Enriched-Directed-Treeᵉ =
    is-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-isolated-root-Enriched-Directed-Treeᵉ :
    is-isolatedᵉ root-Enriched-Directed-Treeᵉ
  is-isolated-root-Enriched-Directed-Treeᵉ =
    is-isolated-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-prop-is-root-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-propᵉ (is-root-Enriched-Directed-Treeᵉ xᵉ)
  is-prop-is-root-Enriched-Directed-Treeᵉ =
    is-prop-is-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-root-enriched-directed-tree-Propᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) → Propᵉ l3ᵉ
  is-root-enriched-directed-tree-Propᵉ =
    is-root-directed-tree-Propᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-contr-loop-space-root-Enriched-Directed-Treeᵉ :
    is-contrᵉ (root-Enriched-Directed-Treeᵉ ＝ᵉ root-Enriched-Directed-Treeᵉ)
  is-contr-loop-space-root-Enriched-Directed-Treeᵉ =
    is-contr-loop-space-root-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  is-proper-node-Enriched-Directed-Treeᵉ :
    node-Enriched-Directed-Treeᵉ → UUᵉ l3ᵉ
  is-proper-node-Enriched-Directed-Treeᵉ =
    is-proper-node-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  eq-refl-root-Enriched-Directed-Treeᵉ :
    (pᵉ : root-Enriched-Directed-Treeᵉ ＝ᵉ root-Enriched-Directed-Treeᵉ) → pᵉ ＝ᵉ reflᵉ
  eq-refl-root-Enriched-Directed-Treeᵉ =
    eq-refl-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  eq-refl-root-Enriched-Directed-Tree'ᵉ :
    (pᵉ : root-Enriched-Directed-Treeᵉ ＝ᵉ root-Enriched-Directed-Treeᵉ) → reflᵉ ＝ᵉ pᵉ
  eq-refl-root-Enriched-Directed-Tree'ᵉ =
    eq-refl-root-Directed-Tree'ᵉ directed-tree-Enriched-Directed-Treeᵉ

  no-direct-successor-root-Enriched-Directed-Treeᵉ :
    ¬ᵉ ( Σᵉ ( node-Enriched-Directed-Treeᵉ)
          ( edge-Enriched-Directed-Treeᵉ root-Enriched-Directed-Treeᵉ))
  no-direct-successor-root-Enriched-Directed-Treeᵉ =
    no-direct-successor-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-proper-node-direct-successor-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ} (eᵉ : edge-Enriched-Directed-Treeᵉ xᵉ yᵉ) →
    ¬ᵉ (is-root-Enriched-Directed-Treeᵉ xᵉ)
  is-proper-node-direct-successor-Enriched-Directed-Treeᵉ =
    is-proper-node-direct-successor-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  is-proof-irrelevant-edge-to-root-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-proof-irrelevantᵉ
      ( edge-Enriched-Directed-Treeᵉ xᵉ root-Enriched-Directed-Treeᵉ)
  is-proof-irrelevant-edge-to-root-Enriched-Directed-Treeᵉ =
    is-proof-irrelevant-edge-to-root-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  is-prop-edge-to-root-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-propᵉ (edge-Enriched-Directed-Treeᵉ xᵉ root-Enriched-Directed-Treeᵉ)
  is-prop-edge-to-root-Enriched-Directed-Treeᵉ =
    is-prop-edge-to-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  is-tree-Enriched-Directed-Treeᵉ :
    is-tree-Directed-Graphᵉ graph-Enriched-Directed-Treeᵉ
  is-tree-Enriched-Directed-Treeᵉ =
    is-tree-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  unique-walk-to-root-Enriched-Directed-Treeᵉ :
    is-tree-Directed-Graph'ᵉ
      graph-Enriched-Directed-Treeᵉ
      root-Enriched-Directed-Treeᵉ
  unique-walk-to-root-Enriched-Directed-Treeᵉ =
    unique-walk-to-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  uniqueness-root-Enriched-Directed-Treeᵉ :
    (Hᵉ : is-tree-Directed-Graphᵉ graph-Enriched-Directed-Treeᵉ) →
    is-root-Enriched-Directed-Treeᵉ (pr1ᵉ Hᵉ)
  uniqueness-root-Enriched-Directed-Treeᵉ =
    uniqueness-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  walk-to-root-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    walk-Enriched-Directed-Treeᵉ xᵉ root-Enriched-Directed-Treeᵉ
  walk-to-root-Enriched-Directed-Treeᵉ =
    walk-to-root-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  unique-direct-successor-Enriched-Directed-Treeᵉ :
    unique-direct-successor-Directed-Graphᵉ
      graph-Enriched-Directed-Treeᵉ
      root-Enriched-Directed-Treeᵉ
  unique-direct-successor-Enriched-Directed-Treeᵉ =
    unique-direct-successor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  unique-direct-successor-is-proper-node-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-proper-node-Enriched-Directed-Treeᵉ xᵉ →
    is-contrᵉ ( Σᵉ node-Enriched-Directed-Treeᵉ (edge-Enriched-Directed-Treeᵉ xᵉ))
  unique-direct-successor-is-proper-node-Enriched-Directed-Treeᵉ =
    unique-direct-successor-is-proper-node-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  is-proof-irrelevant-direct-successor-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-proof-irrelevantᵉ
      ( Σᵉ (node-Enriched-Directed-Treeᵉ) (edge-Enriched-Directed-Treeᵉ xᵉ))
  is-proof-irrelevant-direct-successor-Enriched-Directed-Treeᵉ =
    is-proof-irrelevant-direct-successor-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  is-prop-direct-successor-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    is-propᵉ
      ( Σᵉ (node-Enriched-Directed-Treeᵉ) (edge-Enriched-Directed-Treeᵉ xᵉ))
  is-prop-direct-successor-Enriched-Directed-Treeᵉ =
    is-prop-direct-successor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  eq-direct-successor-Enriched-Directed-Treeᵉ :
    {xᵉ : node-Enriched-Directed-Treeᵉ}
    ( uᵉ vᵉ : Σᵉ (node-Enriched-Directed-Treeᵉ) (edge-Enriched-Directed-Treeᵉ xᵉ)) →
    uᵉ ＝ᵉ vᵉ
  eq-direct-successor-Enriched-Directed-Treeᵉ =
    eq-direct-successor-Directed-Treeᵉ directed-tree-Enriched-Directed-Treeᵉ

  direct-successor-is-proper-node-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    ¬ᵉ (is-root-Enriched-Directed-Treeᵉ xᵉ) →
    Σᵉ (node-Enriched-Directed-Treeᵉ) (edge-Enriched-Directed-Treeᵉ xᵉ)
  direct-successor-is-proper-node-Enriched-Directed-Treeᵉ =
    direct-successor-is-proper-node-Directed-Treeᵉ
      directed-tree-Enriched-Directed-Treeᵉ

  shape-Enriched-Directed-Treeᵉ : node-Enriched-Directed-Treeᵉ → Aᵉ
  shape-Enriched-Directed-Treeᵉ = pr1ᵉ (pr2ᵉ Tᵉ)

  shape-root-Enriched-Directed-Treeᵉ : Aᵉ
  shape-root-Enriched-Directed-Treeᵉ =
    shape-Enriched-Directed-Treeᵉ root-Enriched-Directed-Treeᵉ

  enrichment-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-Enriched-Directed-Treeᵉ xᵉ) ≃ᵉ
    Σᵉ (node-Enriched-Directed-Treeᵉ) (λ yᵉ → edge-Enriched-Directed-Treeᵉ yᵉ xᵉ)
  enrichment-Enriched-Directed-Treeᵉ = pr2ᵉ (pr2ᵉ Tᵉ)

  map-enrichment-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) →
    Bᵉ (shape-Enriched-Directed-Treeᵉ xᵉ) →
    direct-predecessor-Enriched-Directed-Treeᵉ xᵉ
  map-enrichment-Enriched-Directed-Treeᵉ xᵉ =
    map-equivᵉ (enrichment-Enriched-Directed-Treeᵉ xᵉ)

  node-enrichment-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) (bᵉ : Bᵉ (shape-Enriched-Directed-Treeᵉ xᵉ)) →
    node-Enriched-Directed-Treeᵉ
  node-enrichment-Enriched-Directed-Treeᵉ xᵉ bᵉ =
    pr1ᵉ (map-enrichment-Enriched-Directed-Treeᵉ xᵉ bᵉ)

  edge-enrichment-Enriched-Directed-Treeᵉ :
    (xᵉ : node-Enriched-Directed-Treeᵉ) (bᵉ : Bᵉ (shape-Enriched-Directed-Treeᵉ xᵉ)) →
    edge-Enriched-Directed-Treeᵉ (node-enrichment-Enriched-Directed-Treeᵉ xᵉ bᵉ) xᵉ
  edge-enrichment-Enriched-Directed-Treeᵉ xᵉ bᵉ =
    pr2ᵉ (map-enrichment-Enriched-Directed-Treeᵉ xᵉ bᵉ)

  coherence-square-map-enrichment-Enriched-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Enriched-Directed-Treeᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-square-mapsᵉ
      ( trᵉ Bᵉ (apᵉ shape-Enriched-Directed-Treeᵉ pᵉ))
      ( map-enrichment-Enriched-Directed-Treeᵉ xᵉ)
      ( map-enrichment-Enriched-Directed-Treeᵉ yᵉ)
      ( totᵉ ( λ yᵉ → trᵉ (edge-Enriched-Directed-Treeᵉ yᵉ) pᵉ))
  coherence-square-map-enrichment-Enriched-Directed-Treeᵉ reflᵉ = refl-htpyᵉ
```