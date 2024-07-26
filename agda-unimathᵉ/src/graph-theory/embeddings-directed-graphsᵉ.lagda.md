# Embeddings of directed graphs

```agda
module graph-theory.embeddings-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
```

</details>

## Idea

Anᵉ **embeddingᵉ ofᵉ directedᵉ graphs**ᵉ isᵉ aᵉ
[morphism](graph-theory.morphisms-directed-graphs.mdᵉ) `fᵉ : Gᵉ → H`ᵉ ofᵉ
[directedᵉ graphs](graph-theory.directed-graphs.mdᵉ) whichᵉ isᵉ anᵉ
[embedding](foundation.embeddings.mdᵉ) onᵉ verticesᵉ suchᵉ thatᵉ forᵉ eachᵉ pairᵉ
`(xᵉ ,ᵉ y)`ᵉ ofᵉ verticesᵉ in `G`ᵉ theᵉ mapᵉ

```text
  edge-hom-Graphᵉ Gᵉ Hᵉ : edge-Graphᵉ Gᵉ pᵉ → edge-Graphᵉ Hᵉ xᵉ yᵉ
```

isᵉ alsoᵉ anᵉ embedding.ᵉ Embeddingsᵉ ofᵉ directedᵉ graphsᵉ correspondᵉ to directedᵉ
subgraphs.ᵉ

**Note:**ᵉ Ourᵉ notionᵉ ofᵉ embeddingsᵉ ofᵉ directedᵉ graphsᵉ differsᵉ quiteᵉ
substantiallyᵉ fromᵉ theᵉ graphᵉ theoreticᵉ notionᵉ ofᵉ _graphᵉ embedding_,ᵉ whichᵉ
usuallyᵉ refersᵉ to anᵉ embeddingᵉ ofᵉ aᵉ graphᵉ intoᵉ theᵉ plane.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  where

  is-emb-hom-Directed-Graph-Propᵉ :
    hom-Directed-Graphᵉ Gᵉ Hᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-emb-hom-Directed-Graph-Propᵉ fᵉ =
    product-Propᵉ
      ( is-emb-Propᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ))
      ( Π-Propᵉ
        ( vertex-Directed-Graphᵉ Gᵉ)
        ( λ xᵉ →
          Π-Propᵉ
            ( vertex-Directed-Graphᵉ Gᵉ)
            ( λ yᵉ → is-emb-Propᵉ (edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ {xᵉ} {yᵉ}))))

  is-emb-hom-Directed-Graphᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-emb-hom-Directed-Graphᵉ fᵉ = type-Propᵉ (is-emb-hom-Directed-Graph-Propᵉ fᵉ)

  emb-Directed-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  emb-Directed-Graphᵉ = Σᵉ (hom-Directed-Graphᵉ Gᵉ Hᵉ) is-emb-hom-Directed-Graphᵉ

  hom-emb-Directed-Graphᵉ : emb-Directed-Graphᵉ → hom-Directed-Graphᵉ Gᵉ Hᵉ
  hom-emb-Directed-Graphᵉ = pr1ᵉ

  is-emb-emb-Directed-Graphᵉ :
    (fᵉ : emb-Directed-Graphᵉ) →
    is-emb-hom-Directed-Graphᵉ (hom-emb-Directed-Graphᵉ fᵉ)
  is-emb-emb-Directed-Graphᵉ = pr2ᵉ
```

## External links

-ᵉ [Graphᵉ homomorphism](https://www.wikidata.org/entity/Q3385162ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ homomorphism](https://en.wikipedia.org/wiki/Graph_homomorphismᵉ) onᵉ
  Wikipediaᵉ