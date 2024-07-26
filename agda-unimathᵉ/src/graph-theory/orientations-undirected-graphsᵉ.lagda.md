# Orientations of undirected graphs

```agda
module graph-theory.orientations-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ orientationᵉ ofᵉ anᵉ undirectedᵉ graphᵉ isᵉ aᵉ functionᵉ thatᵉ picksᵉ aᵉ directionᵉ forᵉ
everyᵉ edge.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  orientation-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  orientation-Undirected-Graphᵉ =
    ( pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ → type-UU-Finᵉ 2 (pr1ᵉ pᵉ)

  source-edge-orientation-Undirected-Graphᵉ :
    orientation-Undirected-Graphᵉ →
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ → vertex-Undirected-Graphᵉ Gᵉ
  source-edge-orientation-Undirected-Graphᵉ dᵉ (pairᵉ Xᵉ pᵉ) eᵉ =
    pᵉ (dᵉ (pairᵉ Xᵉ pᵉ) eᵉ)
```

## External links

-ᵉ [Orientation](https://www.wikidata.org/entity/Q7102401ᵉ) onᵉ Wikidataᵉ
-ᵉ [Orientationᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Orientation_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graphᵉ orientation](https://mathworld.wolfram.com/GraphOrientation.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ