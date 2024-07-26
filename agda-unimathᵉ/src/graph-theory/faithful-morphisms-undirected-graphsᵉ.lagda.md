# Faithful morphisms of undirected graphs

```agda
module graph-theory.faithful-morphisms-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.morphisms-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **faithfulᵉ morphismᵉ ofᵉ undirectedᵉ graphs**ᵉ isᵉ aᵉ
[morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) `fᵉ : Gᵉ → H`ᵉ ofᵉ
[undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ) suchᵉ thatᵉ forᵉ eachᵉ
[unorderedᵉ pair](foundation.unordered-pairs.mdᵉ) `p`ᵉ ofᵉ verticesᵉ in `G`ᵉ theᵉ mapᵉ

```text
  edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ :
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ)
```

isᵉ anᵉ [embedding](foundation.embeddings.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  is-faithful-hom-undirected-graph-Propᵉ :
    hom-Undirected-Graphᵉ Gᵉ Hᵉ → Propᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-faithful-hom-undirected-graph-Propᵉ fᵉ =
    Π-Propᵉ
      ( unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
      ( λ pᵉ → is-emb-Propᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ))

  is-faithful-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ Gᵉ Hᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-faithful-hom-Undirected-Graphᵉ fᵉ =
    type-Propᵉ (is-faithful-hom-undirected-graph-Propᵉ fᵉ)

  is-prop-is-faithful-hom-Undirected-Graphᵉ :
    (fᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) →
    is-propᵉ (is-faithful-hom-Undirected-Graphᵉ fᵉ)
  is-prop-is-faithful-hom-Undirected-Graphᵉ fᵉ =
    is-prop-type-Propᵉ (is-faithful-hom-undirected-graph-Propᵉ fᵉ)

  faithful-hom-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  faithful-hom-Undirected-Graphᵉ =
    Σᵉ (hom-Undirected-Graphᵉ Gᵉ Hᵉ) is-faithful-hom-Undirected-Graphᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : faithful-hom-Undirected-Graphᵉ Gᵉ Hᵉ)
  where

  hom-faithful-hom-Undirected-Graphᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ
  hom-faithful-hom-Undirected-Graphᵉ = pr1ᵉ fᵉ

  is-faithful-faithful-hom-Undirected-Graphᵉ :
    is-faithful-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-faithful-hom-Undirected-Graphᵉ
  is-faithful-faithful-hom-Undirected-Graphᵉ = pr2ᵉ fᵉ

  vertex-faithful-hom-Undirected-Graphᵉ :
    vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ
  vertex-faithful-hom-Undirected-Graphᵉ =
    vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-faithful-hom-Undirected-Graphᵉ

  unordered-pair-vertices-faithful-hom-Undirected-Graphᵉ :
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  unordered-pair-vertices-faithful-hom-Undirected-Graphᵉ =
    unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ
      hom-faithful-hom-Undirected-Graphᵉ

  edge-faithful-hom-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-faithful-hom-Undirected-Graphᵉ pᵉ)
  edge-faithful-hom-Undirected-Graphᵉ =
    edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-faithful-hom-Undirected-Graphᵉ

  is-emb-edge-faithful-hom-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    is-embᵉ (edge-faithful-hom-Undirected-Graphᵉ pᵉ)
  is-emb-edge-faithful-hom-Undirected-Graphᵉ =
    is-faithful-faithful-hom-Undirected-Graphᵉ

  emb-edge-faithful-hom-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ ↪ᵉ
    edge-Undirected-Graphᵉ Hᵉ
      ( unordered-pair-vertices-faithful-hom-Undirected-Graphᵉ pᵉ)
  pr1ᵉ (emb-edge-faithful-hom-Undirected-Graphᵉ pᵉ) =
    edge-faithful-hom-Undirected-Graphᵉ pᵉ
  pr2ᵉ (emb-edge-faithful-hom-Undirected-Graphᵉ pᵉ) =
    is-emb-edge-faithful-hom-Undirected-Graphᵉ pᵉ
```

## See also

-ᵉ [Embeddingsᵉ ofᵉ undirectedᵉ graphs](graph-theory.embeddings-undirected-graphs.mdᵉ)
-ᵉ [Totallyᵉ faithfulᵉ morphismsᵉ ofᵉ undirectedᵉ graphs](graph-theory.totally-faithful-morphisms-undirected-graphs.mdᵉ)

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) atᵉ
  Wikipediaᵉ