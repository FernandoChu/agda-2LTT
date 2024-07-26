# Rooted undirected trees

```agda
module trees.rooted-undirected-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.trails-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ

open import trees.undirected-treesᵉ
```

</details>

## Idea

Aᵉ **rootedᵉ undirectedᵉ tree**ᵉ isᵉ aᵉ treeᵉ equippedᵉ with aᵉ markedᵉ node.ᵉ Theᵉ markedᵉ
nodeᵉ isᵉ calledᵉ theᵉ **root**ᵉ ofᵉ theᵉ undirectedᵉ tree.ᵉ

## Definition

```agda
Rooted-Undirected-Treeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Rooted-Undirected-Treeᵉ l1ᵉ l2ᵉ = Σᵉ (Undirected-Treeᵉ l1ᵉ l2ᵉ) node-Undirected-Treeᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Tᵉ : Rooted-Undirected-Treeᵉ l1ᵉ l2ᵉ)
  where

  tree-Rooted-Undirected-Treeᵉ : Undirected-Treeᵉ l1ᵉ l2ᵉ
  tree-Rooted-Undirected-Treeᵉ = pr1ᵉ Tᵉ

  undirected-graph-Rooted-Undirected-Treeᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ
  undirected-graph-Rooted-Undirected-Treeᵉ =
    undirected-graph-Undirected-Treeᵉ tree-Rooted-Undirected-Treeᵉ

  node-Rooted-Undirected-Treeᵉ : UUᵉ l1ᵉ
  node-Rooted-Undirected-Treeᵉ = node-Undirected-Treeᵉ tree-Rooted-Undirected-Treeᵉ

  root-Rooted-Undirected-Treeᵉ : node-Rooted-Undirected-Treeᵉ
  root-Rooted-Undirected-Treeᵉ = pr2ᵉ Tᵉ

  trail-to-root-Rooted-Undirected-Treeᵉ :
    (xᵉ : node-Rooted-Undirected-Treeᵉ) →
    trail-Undirected-Graphᵉ undirected-graph-Rooted-Undirected-Treeᵉ xᵉ
      root-Rooted-Undirected-Treeᵉ
  trail-to-root-Rooted-Undirected-Treeᵉ xᵉ =
    standard-trail-Undirected-Treeᵉ
      ( tree-Rooted-Undirected-Treeᵉ)
      ( xᵉ)
      ( root-Rooted-Undirected-Treeᵉ)

  height-node-Rooted-Undirected-Treeᵉ : node-Rooted-Undirected-Treeᵉ → ℕᵉ
  height-node-Rooted-Undirected-Treeᵉ xᵉ =
    length-trail-Undirected-Graphᵉ
      ( undirected-graph-Rooted-Undirected-Treeᵉ)
      ( trail-to-root-Rooted-Undirected-Treeᵉ xᵉ)

  node-of-height-one-Rooted-Undirected-Treeᵉ : UUᵉ l1ᵉ
  node-of-height-one-Rooted-Undirected-Treeᵉ =
    Σᵉ ( node-Rooted-Undirected-Treeᵉ)
      ( λ xᵉ → is-one-ℕᵉ (height-node-Rooted-Undirected-Treeᵉ xᵉ))
```

## Properties

### The type of rooted trees is equivalent to the type of forests of rooted trees

```agda
Forest-Rooted-Undirected-Treesᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Forest-Rooted-Undirected-Treesᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ (UUᵉ l1ᵉ) (λ Xᵉ → Xᵉ → Rooted-Undirected-Treeᵉ l2ᵉ l3ᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Fᵉ : Forest-Rooted-Undirected-Treesᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  indexing-type-Forest-Rooted-Undirected-Treesᵉ : UUᵉ l1ᵉ
  indexing-type-Forest-Rooted-Undirected-Treesᵉ = pr1ᵉ Fᵉ

  family-of-rooted-trees-Forest-Rooted-Undirected-Treesᵉ :
    indexing-type-Forest-Rooted-Undirected-Treesᵉ → Rooted-Undirected-Treeᵉ l2ᵉ l3ᵉ
  family-of-rooted-trees-Forest-Rooted-Undirected-Treesᵉ = pr2ᵉ Fᵉ

  node-rooted-tree-Forest-Rooted-Undirected-Treesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  node-rooted-tree-Forest-Rooted-Undirected-Treesᵉ =
    ( Σᵉ indexing-type-Forest-Rooted-Undirected-Treesᵉ
      ( λ xᵉ →
        node-Rooted-Undirected-Treeᵉ
          ( family-of-rooted-trees-Forest-Rooted-Undirected-Treesᵉ xᵉ))) +ᵉ
    ( unitᵉ)

  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Undirected-Treesᵉ :
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  unordered-pair-of-nodes-rooted-tree-Forest-Rooted-Undirected-Treesᵉ =
    unordered-pairᵉ node-rooted-tree-Forest-Rooted-Undirected-Treesᵉ
```