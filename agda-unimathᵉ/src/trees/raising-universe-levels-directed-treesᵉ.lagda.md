# Raising universe levels of directed trees

```agda
module trees.raising-universe-levels-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.raising-universe-levels-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ

open import trees.directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ operationᵉ thatᵉ raisesᵉ theᵉ universeᵉ levelᵉ ofᵉ aᵉ directedᵉ tree.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Tᵉ : Directed-Treeᵉ l1ᵉ l2ᵉ)
  where

  graph-raise-Directed-Treeᵉ : Directed-Graphᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  graph-raise-Directed-Treeᵉ = raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  node-raise-Directed-Treeᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  node-raise-Directed-Treeᵉ = vertex-Directed-Graphᵉ graph-raise-Directed-Treeᵉ

  equiv-node-compute-raise-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ ≃ᵉ node-raise-Directed-Treeᵉ
  equiv-node-compute-raise-Directed-Treeᵉ =
    equiv-vertex-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  node-compute-raise-Directed-Treeᵉ :
    node-Directed-Treeᵉ Tᵉ → node-raise-Directed-Treeᵉ
  node-compute-raise-Directed-Treeᵉ =
    vertex-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  edge-raise-Directed-Treeᵉ :
    (xᵉ yᵉ : node-raise-Directed-Treeᵉ) → UUᵉ (l2ᵉ ⊔ l4ᵉ)
  edge-raise-Directed-Treeᵉ = edge-Directed-Graphᵉ graph-raise-Directed-Treeᵉ

  equiv-edge-compute-raise-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ) →
    edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ ≃ᵉ
    edge-raise-Directed-Treeᵉ
      ( node-compute-raise-Directed-Treeᵉ xᵉ)
      ( node-compute-raise-Directed-Treeᵉ yᵉ)
  equiv-edge-compute-raise-Directed-Treeᵉ =
    equiv-edge-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  edge-compute-raise-Directed-Treeᵉ :
    (xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ) →
    edge-Directed-Treeᵉ Tᵉ xᵉ yᵉ →
    edge-raise-Directed-Treeᵉ
      ( node-compute-raise-Directed-Treeᵉ xᵉ)
      ( node-compute-raise-Directed-Treeᵉ yᵉ)
  edge-compute-raise-Directed-Treeᵉ =
    edge-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  walk-raise-Directed-Treeᵉ :
    (xᵉ yᵉ : node-raise-Directed-Treeᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  walk-raise-Directed-Treeᵉ = walk-Directed-Graphᵉ graph-raise-Directed-Treeᵉ

  equiv-walk-compute-raise-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ} →
    walk-Directed-Treeᵉ Tᵉ xᵉ yᵉ ≃ᵉ
    walk-raise-Directed-Treeᵉ
      ( node-compute-raise-Directed-Treeᵉ xᵉ)
      ( node-compute-raise-Directed-Treeᵉ yᵉ)
  equiv-walk-compute-raise-Directed-Treeᵉ =
    equiv-walk-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  walk-compute-raise-Directed-Treeᵉ :
    {xᵉ yᵉ : node-Directed-Treeᵉ Tᵉ} →
    walk-Directed-Treeᵉ Tᵉ xᵉ yᵉ →
    walk-raise-Directed-Treeᵉ
      ( node-compute-raise-Directed-Treeᵉ xᵉ)
      ( node-compute-raise-Directed-Treeᵉ yᵉ)
  walk-compute-raise-Directed-Treeᵉ =
    walk-compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)

  root-raise-Directed-Treeᵉ : node-raise-Directed-Treeᵉ
  root-raise-Directed-Treeᵉ =
    node-compute-raise-Directed-Treeᵉ (root-Directed-Treeᵉ Tᵉ)

  unique-walk-to-root-raise-Directed-Treeᵉ :
    (xᵉ : node-raise-Directed-Treeᵉ) →
    is-contrᵉ (walk-raise-Directed-Treeᵉ xᵉ root-raise-Directed-Treeᵉ)
  unique-walk-to-root-raise-Directed-Treeᵉ (map-raiseᵉ xᵉ) =
    is-contr-equiv'ᵉ
      ( walk-Directed-Treeᵉ Tᵉ xᵉ (root-Directed-Treeᵉ Tᵉ))
      ( equiv-walk-compute-raise-Directed-Treeᵉ)
      ( unique-walk-to-root-Directed-Treeᵉ Tᵉ xᵉ)

  is-tree-raise-Directed-Treeᵉ :
    is-tree-Directed-Graphᵉ graph-raise-Directed-Treeᵉ
  pr1ᵉ is-tree-raise-Directed-Treeᵉ = root-raise-Directed-Treeᵉ
  pr2ᵉ is-tree-raise-Directed-Treeᵉ = unique-walk-to-root-raise-Directed-Treeᵉ

  raise-Directed-Treeᵉ : Directed-Treeᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ raise-Directed-Treeᵉ = graph-raise-Directed-Treeᵉ
  pr2ᵉ raise-Directed-Treeᵉ = is-tree-raise-Directed-Treeᵉ

  compute-raise-Directed-Treeᵉ :
    equiv-Directed-Treeᵉ Tᵉ raise-Directed-Treeᵉ
  compute-raise-Directed-Treeᵉ =
    compute-raise-Directed-Graphᵉ l3ᵉ l4ᵉ (graph-Directed-Treeᵉ Tᵉ)
```