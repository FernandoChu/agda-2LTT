# Cycles in undirected graphs

```agda
module graph-theory.cycles-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.embeddings-undirected-graphsᵉ
open import graph-theory.polygonsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "cycle"ᵉ Agda=cycle-Undirected-Graphᵉ Disambiguation="undirectedᵉ graph"ᵉ WD="cycle"ᵉ WDID=Q245595ᵉ}}
in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `G`ᵉ consistsᵉ ofᵉ aᵉ
[`k`-gon](graph-theory.polygons.mdᵉ) `H`ᵉ equippedᵉ with anᵉ
[embeddingᵉ ofᵉ graphs](graph-theory.embeddings-undirected-graphs.mdᵉ) fromᵉ `H`ᵉ
intoᵉ `G`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : ℕᵉ) (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  cycle-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  cycle-Undirected-Graphᵉ =
    Σᵉ (Polygonᵉ kᵉ) (λ Hᵉ → emb-Undirected-Graphᵉ (undirected-graph-Polygonᵉ kᵉ Hᵉ) Gᵉ)
```

## External links

-ᵉ [Cycle](https://www.wikidata.org/entity/Q245595ᵉ) onᵉ Wikidataᵉ
-ᵉ [Cycleᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Cycle_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graphᵉ cycle](https://mathworld.wolfram.com/GraphCycle.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ