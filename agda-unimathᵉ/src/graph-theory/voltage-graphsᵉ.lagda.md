# Voltage graphs

```agda
module graph-theory.voltage-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ

open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ **voltageᵉ graph**ᵉ isᵉ aᵉ [directedᵉ graph](graph-theory.directed-graphs.mdᵉ) `G`ᵉ
equippedᵉ with aᵉ [group](group-theory.groups.mdᵉ) `Π`,ᵉ whichᵉ weᵉ callᵉ theᵉ **voltageᵉ
group**,ᵉ andᵉ aᵉ labellingᵉ ofᵉ theᵉ edgesᵉ ofᵉ `G`ᵉ byᵉ elementsᵉ ofᵉ `Π`.ᵉ

## Definition

```agda
Voltage-Graphᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Πᵉ : Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Voltage-Graphᵉ l2ᵉ l3ᵉ Πᵉ =
  Σᵉ ( Directed-Graphᵉ l2ᵉ l3ᵉ)
    ( λ Gᵉ →
      {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
      edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ → type-Groupᵉ Πᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Πᵉ : Groupᵉ l1ᵉ) (Gᵉ : Voltage-Graphᵉ l2ᵉ l3ᵉ Πᵉ)
  where

  graph-Voltage-Graphᵉ : Directed-Graphᵉ l2ᵉ l3ᵉ
  graph-Voltage-Graphᵉ = pr1ᵉ Gᵉ

  vertex-Voltage-Graphᵉ : UUᵉ l2ᵉ
  vertex-Voltage-Graphᵉ = vertex-Directed-Graphᵉ graph-Voltage-Graphᵉ

  edge-Voltage-Graphᵉ : (xᵉ yᵉ : vertex-Voltage-Graphᵉ) → UUᵉ l3ᵉ
  edge-Voltage-Graphᵉ = edge-Directed-Graphᵉ graph-Voltage-Graphᵉ

  voltage-Voltage-Graphᵉ :
    {xᵉ yᵉ : vertex-Voltage-Graphᵉ} → edge-Voltage-Graphᵉ xᵉ yᵉ → type-Groupᵉ Πᵉ
  voltage-Voltage-Graphᵉ = pr2ᵉ Gᵉ
```

## External links

-ᵉ [Voltageᵉ graph](https://en.wikipedia.org/wiki/Voltage_graphᵉ) atᵉ Wikipediaᵉ