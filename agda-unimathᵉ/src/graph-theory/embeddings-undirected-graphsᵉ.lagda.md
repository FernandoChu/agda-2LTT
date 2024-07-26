# Embeddings of undirected graphs

```agda
module graph-theory.embeddings-undirected-graphsᵉ where
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

Anᵉ **embeddingᵉ ofᵉ undirectedᵉ graphs**ᵉ isᵉ aᵉ
[morphism](graph-theory.morphisms-undirected-graphs.mdᵉ) `fᵉ : Gᵉ → H`ᵉ ofᵉ
[undirectedᵉ graphs](graph-theory.undirected-graphs.mdᵉ) whichᵉ isᵉ anᵉ
[embedding](foundation.embeddings.mdᵉ) onᵉ verticesᵉ suchᵉ thatᵉ forᵉ eachᵉ
[unorderedᵉ pair](foundation.unordered-pairs.mdᵉ) `p`ᵉ ofᵉ verticesᵉ in `G`ᵉ theᵉ mapᵉ

```text
  edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ :
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ (unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ)
```

isᵉ alsoᵉ anᵉ embedding.ᵉ Embeddingsᵉ ofᵉ undirectedᵉ graphsᵉ correspondᵉ to undirectedᵉ
subgraphs.ᵉ

**Note:**ᵉ Ourᵉ notionᵉ ofᵉ embeddingsᵉ ofᵉ directedᵉ graphsᵉ differsᵉ quiteᵉ
substantiallyᵉ fromᵉ theᵉ graphᵉ theoreticᵉ notionᵉ ofᵉ _graphᵉ embedding_,ᵉ whichᵉ
usuallyᵉ refersᵉ to anᵉ embeddingᵉ ofᵉ aᵉ graphᵉ intoᵉ theᵉ plane.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  where

  is-emb-hom-undirected-graph-Propᵉ :
    hom-Undirected-Graphᵉ Gᵉ Hᵉ → Propᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-emb-hom-undirected-graph-Propᵉ fᵉ =
    product-Propᵉ
      ( is-emb-Propᵉ (vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ))
      ( Π-Propᵉ
        ( unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
        ( λ pᵉ →
          is-emb-Propᵉ (edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ fᵉ pᵉ)))

  is-emb-hom-Undirected-Graphᵉ :
    hom-Undirected-Graphᵉ Gᵉ Hᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-emb-hom-Undirected-Graphᵉ fᵉ = type-Propᵉ (is-emb-hom-undirected-graph-Propᵉ fᵉ)

  is-prop-is-emb-hom-Undirected-Graphᵉ :
    (fᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ) → is-propᵉ (is-emb-hom-Undirected-Graphᵉ fᵉ)
  is-prop-is-emb-hom-Undirected-Graphᵉ fᵉ =
    is-prop-type-Propᵉ (is-emb-hom-undirected-graph-Propᵉ fᵉ)

  emb-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  emb-Undirected-Graphᵉ =
    Σᵉ (hom-Undirected-Graphᵉ Gᵉ Hᵉ) is-emb-hom-Undirected-Graphᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Undirected-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : emb-Undirected-Graphᵉ Gᵉ Hᵉ)
  where

  hom-emb-Undirected-Graphᵉ : hom-Undirected-Graphᵉ Gᵉ Hᵉ
  hom-emb-Undirected-Graphᵉ = pr1ᵉ fᵉ

  is-emb-emb-Undirected-Graphᵉ :
    is-emb-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-emb-Undirected-Graphᵉ
  is-emb-emb-Undirected-Graphᵉ = pr2ᵉ fᵉ

  vertex-emb-Undirected-Graphᵉ :
    vertex-Undirected-Graphᵉ Gᵉ → vertex-Undirected-Graphᵉ Hᵉ
  vertex-emb-Undirected-Graphᵉ =
    vertex-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-emb-Undirected-Graphᵉ

  is-emb-vertex-emb-Undirected-Graphᵉ :
    is-embᵉ vertex-emb-Undirected-Graphᵉ
  is-emb-vertex-emb-Undirected-Graphᵉ = pr1ᵉ is-emb-emb-Undirected-Graphᵉ

  emb-vertex-emb-Undirected-Graphᵉ :
    vertex-Undirected-Graphᵉ Gᵉ ↪ᵉ vertex-Undirected-Graphᵉ Hᵉ
  pr1ᵉ emb-vertex-emb-Undirected-Graphᵉ = vertex-emb-Undirected-Graphᵉ
  pr2ᵉ emb-vertex-emb-Undirected-Graphᵉ = is-emb-vertex-emb-Undirected-Graphᵉ

  unordered-pair-vertices-emb-Undirected-Graphᵉ :
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ →
    unordered-pair-vertices-Undirected-Graphᵉ Hᵉ
  unordered-pair-vertices-emb-Undirected-Graphᵉ =
    unordered-pair-vertices-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-emb-Undirected-Graphᵉ

  edge-emb-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ →
    edge-Undirected-Graphᵉ Hᵉ (unordered-pair-vertices-emb-Undirected-Graphᵉ pᵉ)
  edge-emb-Undirected-Graphᵉ =
    edge-hom-Undirected-Graphᵉ Gᵉ Hᵉ hom-emb-Undirected-Graphᵉ

  is-emb-edge-emb-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    is-embᵉ (edge-emb-Undirected-Graphᵉ pᵉ)
  is-emb-edge-emb-Undirected-Graphᵉ = pr2ᵉ is-emb-emb-Undirected-Graphᵉ

  emb-edge-emb-Undirected-Graphᵉ :
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ pᵉ ↪ᵉ
    edge-Undirected-Graphᵉ Hᵉ (unordered-pair-vertices-emb-Undirected-Graphᵉ pᵉ)
  pr1ᵉ (emb-edge-emb-Undirected-Graphᵉ pᵉ) = edge-emb-Undirected-Graphᵉ pᵉ
  pr2ᵉ (emb-edge-emb-Undirected-Graphᵉ pᵉ) = is-emb-edge-emb-Undirected-Graphᵉ pᵉ
```

## See also

-ᵉ [Faithfulᵉ morphismsᵉ ofᵉ undirectedᵉ graphs](graph-theory.faithful-morphisms-undirected-graphs.mdᵉ)
-ᵉ [Totallyᵉ faithfulᵉ morphismsᵉ ofᵉ undirectedᵉ graphs](graph-theory.totally-faithful-morphisms-undirected-graphs.mdᵉ)

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) onᵉ
  Wikipediaᵉ