# Closed walks in undirected graphs

```agda
module graph-theory.closed-walks-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.morphisms-undirected-graphsᵉ
open import graph-theory.polygonsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "closedᵉ walk"ᵉ Agda=closed-walk-Undirected-Graphᵉ Disambiguation="undirectedᵉ graph"ᵉ WDID=Q245595ᵉ WD="cycle"ᵉ}}
ofᵉ lengthᵉ `kᵉ : ℕ`ᵉ in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ)
`G`ᵉ isᵉ aᵉ [morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) ofᵉ graphsᵉ fromᵉ
aᵉ [`k`-gon](graph-theory.polygons.mdᵉ) intoᵉ `G`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  closed-walk-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  closed-walk-Undirected-Graphᵉ =
    Σᵉ (Polygonᵉ kᵉ) (λ Hᵉ → hom-Undirected-Graphᵉ (undirected-graph-Polygonᵉ kᵉ Hᵉ) Gᵉ)
```

## External links

-ᵉ [Cycle](https://www.wikidata.org/entity/Q245595ᵉ) atᵉ Wikidataᵉ
-ᵉ [Cycleᵉ (Graphᵉ Theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graphᵉ Cycle](https://mathworld.wolfram.com/GraphCycle.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ