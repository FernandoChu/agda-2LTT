# Undirected trees

```agda
module trees.undirected-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.paths-undirected-graphsᵉ
open import graph-theory.trails-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
open import graph-theory.walks-undirected-graphsᵉ
```

</details>

## Idea

Anᵉ **undirectedᵉ tree**ᵉ isᵉ anᵉ undirectedᵉ graphᵉ suchᵉ thatᵉ theᵉ typeᵉ ofᵉ trailsᵉ fromᵉ
xᵉ to yᵉ isᵉ contractibleᵉ forᵉ anyᵉ twoᵉ verticesᵉ xᵉ andᵉ y.ᵉ

## Definition

```agda
is-tree-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
is-tree-Undirected-Graphᵉ Gᵉ =
  (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) → is-contrᵉ (trail-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)

Undirected-Treeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Undirected-Treeᵉ l1ᵉ l2ᵉ = Σᵉ (Undirected-Graphᵉ l1ᵉ l2ᵉ) is-tree-Undirected-Graphᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Undirected-Treeᵉ l1ᵉ l2ᵉ)
  where

  undirected-graph-Undirected-Treeᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ
  undirected-graph-Undirected-Treeᵉ = pr1ᵉ Tᵉ

  is-tree-undirected-graph-Undirected-Treeᵉ :
    is-tree-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ
  is-tree-undirected-graph-Undirected-Treeᵉ = pr2ᵉ Tᵉ

  node-Undirected-Treeᵉ : UUᵉ l1ᵉ
  node-Undirected-Treeᵉ =
    vertex-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  unordered-pair-nodes-Undirected-Treeᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ)
  unordered-pair-nodes-Undirected-Treeᵉ =
    unordered-pair-vertices-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  edge-Undirected-Treeᵉ : unordered-pair-nodes-Undirected-Treeᵉ → UUᵉ l2ᵉ
  edge-Undirected-Treeᵉ = edge-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  walk-Undirected-Treeᵉ :
    node-Undirected-Treeᵉ → node-Undirected-Treeᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  walk-Undirected-Treeᵉ = walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-node-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : walk-Undirected-Treeᵉ xᵉ yᵉ) →
    node-Undirected-Treeᵉ → UUᵉ l1ᵉ
  is-node-on-walk-Undirected-Treeᵉ =
    is-vertex-on-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  node-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → walk-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ l1ᵉ
  node-on-walk-Undirected-Treeᵉ =
    vertex-on-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  node-node-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : walk-Undirected-Treeᵉ xᵉ yᵉ) →
    node-on-walk-Undirected-Treeᵉ wᵉ → node-Undirected-Treeᵉ
  node-node-on-walk-Undirected-Treeᵉ wᵉ = pr1ᵉ

  is-edge-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : walk-Undirected-Treeᵉ xᵉ yᵉ)
    (pᵉ : unordered-pair-nodes-Undirected-Treeᵉ) →
    edge-Undirected-Treeᵉ pᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-walk-Undirected-Treeᵉ =
    is-edge-on-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  edge-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} →
    walk-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  edge-on-walk-Undirected-Treeᵉ =
    edge-on-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  edge-edge-on-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : walk-Undirected-Treeᵉ xᵉ yᵉ) →
    edge-on-walk-Undirected-Treeᵉ wᵉ →
    Σᵉ unordered-pair-nodes-Undirected-Treeᵉ edge-Undirected-Treeᵉ
  edge-edge-on-walk-Undirected-Treeᵉ =
    edge-edge-on-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-trail-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} →
    walk-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-trail-walk-Undirected-Treeᵉ =
    is-trail-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  trail-Undirected-Treeᵉ :
    node-Undirected-Treeᵉ → node-Undirected-Treeᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  trail-Undirected-Treeᵉ =
    trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  walk-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} →
    trail-Undirected-Treeᵉ xᵉ yᵉ → walk-Undirected-Treeᵉ xᵉ yᵉ
  walk-trail-Undirected-Treeᵉ =
    walk-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-trail-walk-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (tᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ) →
    is-trail-walk-Undirected-Treeᵉ (walk-trail-Undirected-Treeᵉ tᵉ)
  is-trail-walk-trail-Undirected-Treeᵉ =
    is-trail-walk-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-node-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (tᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ) →
    node-Undirected-Treeᵉ → UUᵉ l1ᵉ
  is-node-on-trail-Undirected-Treeᵉ =
    is-vertex-on-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  node-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → trail-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ l1ᵉ
  node-on-trail-Undirected-Treeᵉ =
    vertex-on-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  node-node-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ) →
    node-on-trail-Undirected-Treeᵉ wᵉ → node-Undirected-Treeᵉ
  node-node-on-trail-Undirected-Treeᵉ wᵉ = pr1ᵉ

  is-edge-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ)
    (pᵉ : unordered-pair-nodes-Undirected-Treeᵉ) →
    edge-Undirected-Treeᵉ pᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-trail-Undirected-Treeᵉ =
    is-edge-on-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  edge-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} →
    trail-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  edge-on-trail-Undirected-Treeᵉ =
    edge-on-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  edge-edge-on-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ) →
    edge-on-trail-Undirected-Treeᵉ wᵉ →
    Σᵉ unordered-pair-nodes-Undirected-Treeᵉ edge-Undirected-Treeᵉ
  edge-edge-on-trail-Undirected-Treeᵉ =
    edge-edge-on-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-path-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → walk-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ l1ᵉ
  is-path-walk-Undirected-Treeᵉ =
    is-path-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  path-Undirected-Treeᵉ :
    node-Undirected-Treeᵉ → node-Undirected-Treeᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  path-Undirected-Treeᵉ = path-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  walk-path-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → path-Undirected-Treeᵉ xᵉ yᵉ →
    walk-Undirected-Treeᵉ xᵉ yᵉ
  walk-path-Undirected-Treeᵉ =
    walk-path-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  standard-trail-Undirected-Treeᵉ :
    (xᵉ yᵉ : node-Undirected-Treeᵉ) → trail-Undirected-Treeᵉ xᵉ yᵉ
  standard-trail-Undirected-Treeᵉ xᵉ yᵉ = centerᵉ (pr2ᵉ Tᵉ xᵉ yᵉ)

  standard-walk-Undirected-Treeᵉ :
    (xᵉ yᵉ : node-Undirected-Treeᵉ) → walk-Undirected-Treeᵉ xᵉ yᵉ
  standard-walk-Undirected-Treeᵉ xᵉ yᵉ =
    walk-trail-Undirected-Treeᵉ (standard-trail-Undirected-Treeᵉ xᵉ yᵉ)

  is-trail-standard-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} →
    is-trail-walk-Undirected-Treeᵉ (standard-walk-Undirected-Treeᵉ xᵉ yᵉ)
  is-trail-standard-walk-Undirected-Treeᵉ {xᵉ} {yᵉ} =
    is-trail-walk-trail-Undirected-Treeᵉ (standard-trail-Undirected-Treeᵉ xᵉ yᵉ)

  length-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → walk-Undirected-Treeᵉ xᵉ yᵉ → ℕᵉ
  length-walk-Undirected-Treeᵉ =
    length-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  length-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → trail-Undirected-Treeᵉ xᵉ yᵉ → ℕᵉ
  length-trail-Undirected-Treeᵉ =
    length-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-constant-walk-Undirected-Tree-Propᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → walk-Undirected-Treeᵉ xᵉ yᵉ → Propᵉ lzero
  is-constant-walk-Undirected-Tree-Propᵉ =
    is-constant-walk-Undirected-Graph-Propᵉ undirected-graph-Undirected-Treeᵉ

  is-constant-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → walk-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ lzero
  is-constant-walk-Undirected-Treeᵉ =
    is-constant-walk-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-decidable-is-constant-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (wᵉ : walk-Undirected-Treeᵉ xᵉ yᵉ) →
    is-decidableᵉ (is-constant-walk-Undirected-Treeᵉ wᵉ)
  is-decidable-is-constant-walk-Undirected-Treeᵉ =
    is-decidable-is-constant-walk-Undirected-Graphᵉ
      undirected-graph-Undirected-Treeᵉ

  is-constant-trail-Undirected-Tree-Propᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → trail-Undirected-Treeᵉ xᵉ yᵉ → Propᵉ lzero
  is-constant-trail-Undirected-Tree-Propᵉ =
    is-constant-trail-Undirected-Graph-Propᵉ undirected-graph-Undirected-Treeᵉ

  is-constant-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} → trail-Undirected-Treeᵉ xᵉ yᵉ → UUᵉ lzero
  is-constant-trail-Undirected-Treeᵉ =
    is-constant-trail-Undirected-Graphᵉ undirected-graph-Undirected-Treeᵉ

  is-decidable-is-constant-trail-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ} (tᵉ : trail-Undirected-Treeᵉ xᵉ yᵉ) →
    is-decidableᵉ (is-constant-trail-Undirected-Treeᵉ tᵉ)
  is-decidable-is-constant-trail-Undirected-Treeᵉ =
    is-decidable-is-constant-trail-Undirected-Graphᵉ
      undirected-graph-Undirected-Treeᵉ
```

### Distance between nodes of a tree

```agda
  dist-Undirected-Treeᵉ : node-Undirected-Treeᵉ → node-Undirected-Treeᵉ → ℕᵉ
  dist-Undirected-Treeᵉ xᵉ yᵉ =
    length-trail-Undirected-Treeᵉ (standard-trail-Undirected-Treeᵉ xᵉ yᵉ)
```

## Properties

### Trees are acyclic graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Undirected-Treeᵉ l1ᵉ l2ᵉ)
  where

  is-refl-is-circuit-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ Tᵉ} (tᵉ : trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ)
    (pᵉ : xᵉ ＝ᵉ yᵉ) →
    trᵉ (walk-Undirected-Treeᵉ Tᵉ xᵉ) pᵉ refl-walk-Undirected-Graphᵉ ＝ᵉ
    walk-trail-Undirected-Treeᵉ Tᵉ tᵉ
  is-refl-is-circuit-walk-Undirected-Treeᵉ {xᵉ} tᵉ reflᵉ =
    apᵉ
      ( walk-trail-Undirected-Treeᵉ Tᵉ)
      ( eq-is-contrᵉ
        ( is-tree-undirected-graph-Undirected-Treeᵉ Tᵉ xᵉ xᵉ)
        { pairᵉ
          ( refl-walk-Undirected-Graphᵉ)
          ( is-trail-refl-walk-Undirected-Graphᵉ
            ( undirected-graph-Undirected-Treeᵉ Tᵉ) {xᵉ})}
        { tᵉ})

  is-empty-edge-on-walk-is-circuit-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ Tᵉ} (tᵉ : trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ) →
    (pᵉ : xᵉ ＝ᵉ yᵉ) → is-emptyᵉ (edge-on-trail-Undirected-Treeᵉ Tᵉ tᵉ)
  is-empty-edge-on-walk-is-circuit-walk-Undirected-Treeᵉ {xᵉ} tᵉ reflᵉ eᵉ =
    is-empty-edge-on-walk-refl-walk-Undirected-Graphᵉ
      ( undirected-graph-Undirected-Treeᵉ Tᵉ)
      ( xᵉ)
      ( trᵉ
        ( edge-on-walk-Undirected-Treeᵉ Tᵉ)
        ( invᵉ (is-refl-is-circuit-walk-Undirected-Treeᵉ tᵉ reflᵉ))
        ( eᵉ))
```

### If `x` and `y` are merely equal vertices, then the standard trail between them is constant

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Undirected-Treeᵉ l1ᵉ l2ᵉ) {xᵉ : node-Undirected-Treeᵉ Tᵉ}
  where

  is-constant-standard-trail-eq-Undirected-Treeᵉ :
    {yᵉ : node-Undirected-Treeᵉ Tᵉ} → (xᵉ ＝ᵉ yᵉ) →
    is-constant-trail-Undirected-Treeᵉ Tᵉ (standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ)
  is-constant-standard-trail-eq-Undirected-Treeᵉ {yᵉ} reflᵉ =
    invᵉ
      ( apᵉ
        ( length-walk-Undirected-Treeᵉ Tᵉ)
        ( is-refl-is-circuit-walk-Undirected-Treeᵉ Tᵉ
        ( standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ)
        ( reflᵉ)))

  is-constant-standard-trail-mere-eq-Undirected-Treeᵉ :
    {yᵉ : node-Undirected-Treeᵉ Tᵉ} →
    mere-eqᵉ xᵉ yᵉ →
    is-constant-trail-Undirected-Treeᵉ Tᵉ (standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ)
  is-constant-standard-trail-mere-eq-Undirected-Treeᵉ {yᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-constant-trail-Undirected-Tree-Propᵉ Tᵉ
        ( standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ))
      ( is-constant-standard-trail-eq-Undirected-Treeᵉ)

  eq-is-constant-standard-trail-Undirected-Treeᵉ :
    {yᵉ : node-Undirected-Treeᵉ Tᵉ} →
    is-constant-trail-Undirected-Treeᵉ Tᵉ (standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ) →
    xᵉ ＝ᵉ yᵉ
  eq-is-constant-standard-trail-Undirected-Treeᵉ {yᵉ} Hᵉ =
    eq-constant-walk-Undirected-Graphᵉ
      ( undirected-graph-Undirected-Treeᵉ Tᵉ)
      ( pairᵉ (standard-walk-Undirected-Treeᵉ Tᵉ xᵉ yᵉ) Hᵉ)
```

### The type of nodes of a tree is a set

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Undirected-Treeᵉ l1ᵉ l2ᵉ) {xᵉ : node-Undirected-Treeᵉ Tᵉ}
  where

  is-set-node-Undirected-Treeᵉ : is-setᵉ (node-Undirected-Treeᵉ Tᵉ)
  is-set-node-Undirected-Treeᵉ =
    is-set-mere-eq-in-idᵉ
      ( λ xᵉ yᵉ Hᵉ →
        eq-constant-walk-Undirected-Graphᵉ
          ( undirected-graph-Undirected-Treeᵉ Tᵉ)
          ( pairᵉ
            ( standard-walk-Undirected-Treeᵉ Tᵉ xᵉ yᵉ)
            ( is-constant-standard-trail-mere-eq-Undirected-Treeᵉ Tᵉ Hᵉ)))

  node-Undirected-Tree-Setᵉ : Setᵉ l1ᵉ
  pr1ᵉ node-Undirected-Tree-Setᵉ = node-Undirected-Treeᵉ Tᵉ
  pr2ᵉ node-Undirected-Tree-Setᵉ = is-set-node-Undirected-Treeᵉ
```

### The type of nodes of a tree has decidable equality

```agda
has-decidable-equality-node-Undirected-Treeᵉ :
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Undirected-Treeᵉ l2ᵉ l1ᵉ) →
  has-decidable-equalityᵉ (node-Undirected-Treeᵉ Tᵉ)
has-decidable-equality-node-Undirected-Treeᵉ Tᵉ xᵉ yᵉ =
  is-decidable-iffᵉ
    ( eq-is-constant-standard-trail-Undirected-Treeᵉ Tᵉ)
    ( is-constant-standard-trail-eq-Undirected-Treeᵉ Tᵉ)
    ( is-decidable-is-constant-trail-Undirected-Treeᵉ Tᵉ
      ( standard-trail-Undirected-Treeᵉ Tᵉ xᵉ yᵉ))
```

### Any trail in a tree is a path

```text
module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Treeᵉ l1ᵉ l2ᵉ)
  where

  is-path-is-trail-walk-Undirected-Treeᵉ :
    {xᵉ yᵉ : node-Undirected-Treeᵉ Tᵉ} (wᵉ : walk-Undirected-Treeᵉ Tᵉ xᵉ yᵉ) →
    is-trail-walk-Undirected-Treeᵉ Tᵉ wᵉ → is-path-walk-Undirected-Treeᵉ Tᵉ wᵉ
  is-path-is-trail-walk-Undirected-Treeᵉ {xᵉ} {yᵉ} wᵉ Hᵉ {pairᵉ uᵉ KUᵉ} {pairᵉ vᵉ Kᵉ} pᵉ with
    is-vertex-on-first-or-second-segment-walk-Undirected-Graphᵉ
      (undirected-graph-Undirected-Treeᵉ Tᵉ) wᵉ (pairᵉ uᵉ KUᵉ) (pairᵉ vᵉ Kᵉ)
  ... | inlᵉ Lᵉ = {!!ᵉ}
    where
    w1'ᵉ : walk-Undirected-Treeᵉ Tᵉ xᵉ uᵉ
    w1'ᵉ =
      first-segment-walk-Undirected-Graphᵉ (undirected-graph-Undirected-Treeᵉ Tᵉ) wᵉ (pairᵉ uᵉ KUᵉ)
    w1ᵉ : walk-Undirected-Treeᵉ Tᵉ xᵉ vᵉ
    w1ᵉ =
      first-segment-walk-Undirected-Graphᵉ
        ( undirected-graph-Undirected-Treeᵉ Tᵉ)
        ( w1'ᵉ)
        ( pairᵉ vᵉ Lᵉ)
    w'ᵉ : walk-Undirected-Treeᵉ Tᵉ vᵉ uᵉ
    w'ᵉ = {!!ᵉ}
  ... | inrᵉ Lᵉ = {!!ᵉ}
    where
    w1ᵉ : walk-Undirected-Treeᵉ Tᵉ xᵉ uᵉ
    w1ᵉ =
      first-segment-walk-Undirected-Graphᵉ (undirected-graph-Undirected-Treeᵉ Tᵉ) wᵉ (pairᵉ uᵉ KUᵉ)

{-ᵉ
    where
    w1ᵉ : walk-Undirected-Treeᵉ Tᵉ xᵉ (node-node-on-walk-Undirected-Treeᵉ Tᵉ wᵉ uᵉ)
    w1ᵉ =
      first-segment-walk-Undirected-Graphᵉ (undirected-graph-Undirected-Treeᵉ Tᵉ) wᵉ uᵉ
    w2'ᵉ : walk-Undirected-Treeᵉ Tᵉ (node-node-on-walk-Undirected-Treeᵉ Tᵉ wᵉ uᵉ) yᵉ
    w2'ᵉ =
      second-segment-walk-Undirected-Graphᵉ (undirected-graph-Undirected-Treeᵉ Tᵉ) wᵉ uᵉ
    w2ᵉ : walk-Undirected-Treeᵉ Tᵉ (node-node-on-walk-Undirected-Treeᵉ Tᵉ wᵉ uᵉ) (node-node-on-walk-Undirected-Treeᵉ Tᵉ wᵉ vᵉ)
    w2ᵉ = {!first-segment-walk-Undirected-Graphᵉ (undirected-graph-Undirected-Treeᵉ Tᵉ) w2'ᵉ !ᵉ}
  -ᵉ}
```

## See also

Thereᵉ areᵉ manyᵉ variationsᵉ ofᵉ theᵉ notionᵉ ofᵉ trees,ᵉ allᵉ ofᵉ whichᵉ areᵉ subtlyᵉ
differentᵉ:

-ᵉ Directedᵉ treesᵉ canᵉ beᵉ foundᵉ in
  [`trees.directed-trees`](trees.directed-trees.md).ᵉ
-ᵉ Acyclicᵉ undirectedᵉ graphsᵉ canᵉ beᵉ foundᵉ in
  [`graph-theory.acyclic-undirected-graphs`](graph-theory.acyclic-undirected-graphs.md).ᵉ