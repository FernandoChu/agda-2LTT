# Matchings

```agda
module graph-theory.matchingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **matching**ᵉ in aᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) isᵉ aᵉ
typeᵉ ofᵉ edgesᵉ withoutᵉ commonᵉ vertices.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  selected-edges-vertex-Undirected-Graphᵉ :
    ( Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) →
    ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
      edge-Undirected-Graphᵉ Gᵉ pᵉ → Finᵉ 2ᵉ) →
    vertex-Undirected-Graphᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  selected-edges-vertex-Undirected-Graphᵉ Gᵉ cᵉ xᵉ =
    Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ)
      ( λ yᵉ →
        Σᵉ ( edge-Undirected-Graphᵉ Gᵉ (standard-unordered-pairᵉ xᵉ yᵉ))
          ( λ eᵉ → Idᵉ (cᵉ (standard-unordered-pairᵉ xᵉ yᵉ) eᵉ) (inrᵉ starᵉ)))

  matchingᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  matchingᵉ Gᵉ =
    Σᵉ ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        edge-Undirected-Graphᵉ Gᵉ pᵉ → Finᵉ 2ᵉ)
      ( λ cᵉ →
        ( xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
        is-propᵉ (selected-edges-vertex-Undirected-Graphᵉ Gᵉ cᵉ xᵉ))

  perfect-matchingᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  perfect-matchingᵉ Gᵉ =
    Σᵉ ( (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
        edge-Undirected-Graphᵉ Gᵉ pᵉ → Finᵉ 2ᵉ)
      ( λ cᵉ →
        ( xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
          is-contrᵉ (selected-edges-vertex-Undirected-Graphᵉ Gᵉ cᵉ xᵉ))
```

## External links

-ᵉ [Matching](https://www.wikidata.org/entity/Q1065144ᵉ) onᵉ Wikidataᵉ
-ᵉ [Matchingᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Matching_(graph_theory)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Matching](https://mathworld.wolfram.com/Matching.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ