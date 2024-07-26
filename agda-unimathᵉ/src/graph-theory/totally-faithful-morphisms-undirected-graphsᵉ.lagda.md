# Totally faithful morphisms of undirected graphs

```agda
module graph-theory.totally-faithful-morphisms-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.morphisms-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **totallyᵉ faithfulᵉ morphismᵉ ofᵉ undirectedᵉ graphs**ᵉ isᵉ aᵉ
[morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) `fᵉ : Gᵉ → H`ᵉ ofᵉ
[undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ) suchᵉ thatᵉ forᵉ edgeᵉ `e`ᵉ in
`H`ᵉ thereᵉ isᵉ atᵉ mostᵉ oneᵉ edgeᵉ in `G`ᵉ thatᵉ `f`ᵉ mapsᵉ to `e`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  is-totally-faithful-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ Gᵉ Hᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-totally-faithful-hom-Undirected-Graphᵉ fᵉ =
    is-embᵉ (totᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ))

  totally-faithful-hom-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  totally-faithful-hom-Undirected-Graphᵉ =
    Σᵉ (hom-Undirected-Graphᵉ Gᵉ Hᵉ) is-totally-faithful-hom-Undirected-Graphᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : totally-faithful-hom-Undirected-Graphᵉ Gᵉ Hᵉ)
  where

  hom-totally-faithful-hom-Undirected-Graphᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ
  hom-totally-faithful-hom-Undirected-Graphᵉ = pr1ᵉ fᵉ

  vertex-totally-faithful-hom-Undirected-Graphᵉ :
    vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ
  vertex-totally-faithful-hom-Undirected-Graphᵉ =
    vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-totally-faithful-hom-Undirected-Graphᵉ

  unordered-pair-vertices-totally-faithful-hom-Undirected-Graphᵉ :
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  unordered-pair-vertices-totally-faithful-hom-Undirected-Graphᵉ =
    unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ
      hom-totally-faithful-hom-Undirected-Graphᵉ

  edge-totally-faithful-hom-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-totally-faithful-hom-Undirected-Graphᵉ pᵉ)
  edge-totally-faithful-hom-Undirected-Graphᵉ =
    edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-totally-faithful-hom-Undirected-Graphᵉ

  is-totally-faithful-totally-faithful-hom-Undirected-Graphᵉ :
    is-totally-faithful-hom-Undirected-Graphᵉ Gᵉ Hᵉ
      hom-totally-faithful-hom-Undirected-Graphᵉ
  is-totally-faithful-totally-faithful-hom-Undirected-Graphᵉ = pr2ᵉ fᵉ
```

## See also

-ᵉ [Embeddingsᵉ ofᵉ undirectedᵉ graphs](graph-theory.embeddings-undirected-graphs.mdᵉ)
-ᵉ [Faithfulᵉ morphismsᵉ ofᵉ undirectedᵉ graphs](graph-theory.faithful-morphisms-undirected-graphs.mdᵉ)

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) atᵉ
  Wikipediaᵉ