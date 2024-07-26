# Edge-coloured undirected graphs

```agda
module graph-theory.edge-coloured-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.neighbors-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Anᵉ **edge-colouredᵉ undirectedᵉ graph**ᵉ isᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) equippedᵉ with aᵉ familyᵉ ofᵉ
mapsᵉ `Eᵉ pᵉ → X`ᵉ fromᵉ theᵉ edgesᵉ atᵉ
[unorderedᵉ pairs](foundation.unordered-pairs.mdᵉ) `p`ᵉ intoᵉ aᵉ typeᵉ `C`ᵉ ofᵉ colours,ᵉ
suchᵉ thatᵉ theᵉ inducedᵉ mapᵉ `incident-Undirected-Graphᵉ Gᵉ xᵉ → C`ᵉ isᵉ
[injective](foundation.injective-maps.mdᵉ) forᵉ eachᵉ vertexᵉ `x`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Cᵉ : UUᵉ l1ᵉ) (Gᵉ : Undirected-Graphᵉ l2ᵉ l3ᵉ)
  where

  neighbor-edge-colouring-Undirected-Graphᵉ :
    ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
      edge-Undirected-Graphᵉ Gᵉ pᵉ → Cᵉ) →
    (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) → neighbor-Undirected-Graphᵉ Gᵉ xᵉ → Cᵉ
  neighbor-edge-colouring-Undirected-Graphᵉ fᵉ xᵉ (pairᵉ yᵉ eᵉ) =
    fᵉ (standard-unordered-pairᵉ xᵉ yᵉ) eᵉ

  edge-colouring-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  edge-colouring-Undirected-Graphᵉ =
    Σᵉ ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        edge-Undirected-Graphᵉ Gᵉ pᵉ → Cᵉ)
      ( λ fᵉ →
        (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
        is-embᵉ (neighbor-edge-colouring-Undirected-Graphᵉ fᵉ xᵉ))

Edge-Coloured-Undirected-Graphᵉ :
  {lᵉ : Level} (l1ᵉ l2ᵉ : Level) (Cᵉ : UUᵉ lᵉ) → UUᵉ (lᵉ ⊔ lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Edge-Coloured-Undirected-Graphᵉ l1ᵉ l2ᵉ Cᵉ =
  Σᵉ ( Undirected-Graphᵉ l1ᵉ l2ᵉ)
    ( edge-colouring-Undirected-Graphᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Cᵉ : UUᵉ l1ᵉ} (Gᵉ : Edge-Coloured-Undirected-Graphᵉ l2ᵉ l3ᵉ Cᵉ)
  where

  undirected-graph-Edge-Coloured-Undirected-Graphᵉ : Undirected-Graphᵉ l2ᵉ l3ᵉ
  undirected-graph-Edge-Coloured-Undirected-Graphᵉ = pr1ᵉ Gᵉ

  vertex-Edge-Coloured-Undirected-Graphᵉ : UUᵉ l2ᵉ
  vertex-Edge-Coloured-Undirected-Graphᵉ =
    vertex-Undirected-Graphᵉ undirected-graph-Edge-Coloured-Undirected-Graphᵉ

  unordered-pair-vertices-Edge-Coloured-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l2ᵉ)
  unordered-pair-vertices-Edge-Coloured-Undirected-Graphᵉ =
    unordered-pair-vertices-Undirected-Graphᵉ
      undirected-graph-Edge-Coloured-Undirected-Graphᵉ

  edge-Edge-Coloured-Undirected-Graphᵉ :
    unordered-pair-vertices-Edge-Coloured-Undirected-Graphᵉ → UUᵉ l3ᵉ
  edge-Edge-Coloured-Undirected-Graphᵉ =
    edge-Undirected-Graphᵉ undirected-graph-Edge-Coloured-Undirected-Graphᵉ

  neighbor-Edge-Coloured-Undirected-Graphᵉ :
    vertex-Edge-Coloured-Undirected-Graphᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  neighbor-Edge-Coloured-Undirected-Graphᵉ =
    neighbor-Undirected-Graphᵉ undirected-graph-Edge-Coloured-Undirected-Graphᵉ

  colouring-Edge-Coloured-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Edge-Coloured-Undirected-Graphᵉ) →
    edge-Edge-Coloured-Undirected-Graphᵉ pᵉ → Cᵉ
  colouring-Edge-Coloured-Undirected-Graphᵉ =
    pr1ᵉ (pr2ᵉ Gᵉ)

  neighbor-colouring-Edge-Coloured-Undirected-Graphᵉ :
    (xᵉ : vertex-Edge-Coloured-Undirected-Graphᵉ) →
    neighbor-Edge-Coloured-Undirected-Graphᵉ xᵉ → Cᵉ
  neighbor-colouring-Edge-Coloured-Undirected-Graphᵉ =
    neighbor-edge-colouring-Undirected-Graphᵉ Cᵉ
      undirected-graph-Edge-Coloured-Undirected-Graphᵉ
      colouring-Edge-Coloured-Undirected-Graphᵉ

  is-emb-colouring-Edge-Coloured-Undirected-Graphᵉ :
    (xᵉ : vertex-Edge-Coloured-Undirected-Graphᵉ) →
    is-embᵉ (neighbor-colouring-Edge-Coloured-Undirected-Graphᵉ xᵉ)
  is-emb-colouring-Edge-Coloured-Undirected-Graphᵉ =
    pr2ᵉ (pr2ᵉ Gᵉ)
```

## External links

-ᵉ [Edgeᵉ coloring](https://en.wikipedia.org/wiki/Edge_coloringᵉ) atᵉ Wikipediaᵉ
-ᵉ [Edgeᵉ coloring](https://mathworld.wolfram.com/EdgeColoring.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ
-ᵉ [Graphᵉ coloring](https://www.wikidata.org/entity/Q504843ᵉ) onᵉ Wikidataᵉ