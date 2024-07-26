# Raising universe levels of directed graphs

```agda
module graph-theory.raising-universe-levels-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.equivalences-directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ
```

</details>

## Idea

Weᵉ **raiseᵉ theᵉ universeᵉ levels**ᵉ ofᵉ
[directedᵉ graphs](graph-theory.directed-graphs.mdᵉ) byᵉ
[raisingᵉ theᵉ universeᵉ levels](foundation.raising-universe-levels.mdᵉ) ofᵉ theᵉ
verticesᵉ andᵉ theᵉ edges.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level) (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  vertex-raise-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  vertex-raise-Directed-Graphᵉ = raiseᵉ l3ᵉ (vertex-Directed-Graphᵉ Gᵉ)

  equiv-vertex-compute-raise-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ ≃ᵉ vertex-raise-Directed-Graphᵉ
  equiv-vertex-compute-raise-Directed-Graphᵉ =
    compute-raiseᵉ l3ᵉ (vertex-Directed-Graphᵉ Gᵉ)

  vertex-compute-raise-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ → vertex-raise-Directed-Graphᵉ
  vertex-compute-raise-Directed-Graphᵉ =
    map-equivᵉ equiv-vertex-compute-raise-Directed-Graphᵉ

  edge-raise-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-raise-Directed-Graphᵉ) → UUᵉ (l2ᵉ ⊔ l4ᵉ)
  edge-raise-Directed-Graphᵉ (map-raiseᵉ xᵉ) (map-raiseᵉ yᵉ) =
    raiseᵉ l4ᵉ (edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)

  equiv-edge-compute-raise-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
    edge-raise-Directed-Graphᵉ
      ( vertex-compute-raise-Directed-Graphᵉ xᵉ)
      ( vertex-compute-raise-Directed-Graphᵉ yᵉ)
  equiv-edge-compute-raise-Directed-Graphᵉ xᵉ yᵉ =
    compute-raiseᵉ l4ᵉ (edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)

  edge-compute-raise-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    edge-raise-Directed-Graphᵉ
      ( vertex-compute-raise-Directed-Graphᵉ xᵉ)
      ( vertex-compute-raise-Directed-Graphᵉ yᵉ)
  edge-compute-raise-Directed-Graphᵉ xᵉ yᵉ =
    map-equivᵉ (equiv-edge-compute-raise-Directed-Graphᵉ xᵉ yᵉ)

  raise-Directed-Graphᵉ : Directed-Graphᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ raise-Directed-Graphᵉ = vertex-raise-Directed-Graphᵉ
  pr2ᵉ raise-Directed-Graphᵉ = edge-raise-Directed-Graphᵉ

  compute-raise-Directed-Graphᵉ :
    equiv-Directed-Graphᵉ Gᵉ raise-Directed-Graphᵉ
  pr1ᵉ compute-raise-Directed-Graphᵉ = equiv-vertex-compute-raise-Directed-Graphᵉ
  pr2ᵉ compute-raise-Directed-Graphᵉ = equiv-edge-compute-raise-Directed-Graphᵉ

  walk-raise-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-raise-Directed-Graphᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  walk-raise-Directed-Graphᵉ = walk-Directed-Graphᵉ raise-Directed-Graphᵉ

  equiv-walk-compute-raise-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
    walk-raise-Directed-Graphᵉ
      ( vertex-compute-raise-Directed-Graphᵉ xᵉ)
      ( vertex-compute-raise-Directed-Graphᵉ yᵉ)
  equiv-walk-compute-raise-Directed-Graphᵉ =
    equiv-walk-equiv-Directed-Graphᵉ Gᵉ
      raise-Directed-Graphᵉ
      compute-raise-Directed-Graphᵉ

  walk-compute-raise-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    walk-raise-Directed-Graphᵉ
      ( vertex-compute-raise-Directed-Graphᵉ xᵉ)
      ( vertex-compute-raise-Directed-Graphᵉ yᵉ)
  walk-compute-raise-Directed-Graphᵉ =
    map-equivᵉ equiv-walk-compute-raise-Directed-Graphᵉ
```