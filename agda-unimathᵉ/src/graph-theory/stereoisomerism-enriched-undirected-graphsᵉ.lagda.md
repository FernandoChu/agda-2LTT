# Stereoisomerism for enriched undirected graphs

```agda
module graph-theory.stereoisomerism-enriched-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.enriched-undirected-graphsᵉ
open import graph-theory.equivalences-undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **stereoisomerism**ᵉ betweenᵉ twoᵉ
[`(A,B)`-enrichedᵉ undirectedᵉ graphs](graph-theory.enriched-undirected-graphs.mdᵉ)
isᵉ anᵉ [equivalence](graph-theory.equivalences-undirected-graphs.mdᵉ) betweenᵉ
theirᵉ underlyingᵉ [undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ)
preservingᵉ theᵉ shapeᵉ ofᵉ theᵉ vertices.ᵉ Thisᵉ conceptᵉ isᵉ derivedᵉ fromᵉ theᵉ conceptᵉ
ofᵉ stereoisomerismᵉ ofᵉ chemicalᵉ compounds.ᵉ

**Note:**ᵉ Itᵉ couldᵉ beᵉ thatᵉ weᵉ onlyᵉ wantᵉ theᵉ shapesᵉ to beᵉ merelyᵉ preserved.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  (Gᵉ : Enriched-Undirected-Graphᵉ l3ᵉ l4ᵉ Aᵉ Bᵉ)
  (Hᵉ : Enriched-Undirected-Graphᵉ l5ᵉ l6ᵉ Aᵉ Bᵉ)
  where

  stereoisomerism-Enriched-Undirected-Graphᵉ :
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  stereoisomerism-Enriched-Undirected-Graphᵉ =
    Σᵉ ( equiv-Undirected-Graphᵉ
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
        ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ))
      ( λ eᵉ →
        ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ) ~ᵉ
        ( ( shape-vertex-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ) ∘ᵉ
          ( vertex-equiv-Undirected-Graphᵉ
            ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Gᵉ)
            ( undirected-graph-Enriched-Undirected-Graphᵉ Aᵉ Bᵉ Hᵉ)
            ( eᵉ))))
```

## External links

-ᵉ [Stereoisomerism](https://www.wikidata.org/entity/Q47455153ᵉ) onᵉ Wikidataᵉ
-ᵉ [Stereoisomerism](https://en.wikipedia.org/wiki/Stereoisomerismᵉ) atᵉ Wikipediaᵉ