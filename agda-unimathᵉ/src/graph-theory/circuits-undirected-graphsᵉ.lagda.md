# Circuits in undirected graphs

```agda
module graph-theory.circuits-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.polygonsᵉ
open import graph-theory.totally-faithful-morphisms-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "circuit"ᵉ Agda=circuit-Undirected-Graphᵉ WD="cycle"ᵉ WDID=Q245595ᵉ}}
in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `G`ᵉ consistsᵉ ofᵉ aᵉ
[`k`-gon](graph-theory.polygons.mdᵉ) `H`ᵉ equippedᵉ with aᵉ
[totallyᵉ faithful](graph-theory.totally-faithful-morphisms-undirected-graphs.mdᵉ)
[morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) ofᵉ undirectedᵉ graphsᵉ
fromᵉ `H`ᵉ to `G`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ circuitᵉ isᵉ aᵉ closedᵉ walkᵉ with noᵉ repeatedᵉ
edges.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  circuit-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  circuit-Undirected-Graphᵉ =
    Σᵉ ( Polygonᵉ kᵉ)
      ( λ Hᵉ →
        totally-faithful-hom-Undirected-Graphᵉ (undirected-graph-Polygonᵉ kᵉ Hᵉ) Gᵉ)
```

## External links

-ᵉ [Cycleᵉ (Graphᵉ Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graphᵉ Cycle](https://mathworld.wolfram.com/GraphCycle.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ