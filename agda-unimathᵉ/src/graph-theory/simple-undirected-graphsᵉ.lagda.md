# Simple undirected graphs

```agda
module graph-theory.simple-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) isᵉ saidᵉ to beᵉ
**simple**ᵉ ifᵉ itᵉ onlyᵉ containsᵉ edgesᵉ betweenᵉ
[distinctᵉ points](foundation.pairs-of-distinct-elements.md),ᵉ andᵉ thereᵉ isᵉ atᵉ
mostᵉ oneᵉ edgeᵉ betweenᵉ anyᵉ twoᵉ vertices.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-simple-Undirected-Graph-Propᵉ : Propᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-simple-Undirected-Graph-Propᵉ =
    product-Propᵉ
      ( Π-Propᵉ
        ( unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
        ( λ pᵉ →
          function-Propᵉ
            ( edge-Undirected-Graphᵉ Gᵉ pᵉ)
            ( is-emb-Propᵉ
              ( element-unordered-pair-vertices-Undirected-Graphᵉ Gᵉ pᵉ))))
      ( Π-Propᵉ
        ( unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
        ( λ pᵉ → is-prop-Propᵉ (edge-Undirected-Graphᵉ Gᵉ pᵉ)))

  is-simple-Undirected-Graphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-simple-Undirected-Graphᵉ = type-Propᵉ is-simple-Undirected-Graph-Propᵉ

  is-prop-is-simple-Undirected-Graphᵉ : is-propᵉ is-simple-Undirected-Graphᵉ
  is-prop-is-simple-Undirected-Graphᵉ =
    is-prop-type-Propᵉ is-simple-Undirected-Graph-Propᵉ

Simple-Undirected-Graphᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Simple-Undirected-Graphᵉ l1ᵉ l2ᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Vᵉ →
      Σᵉ ( unordered-pairᵉ Vᵉ → Propᵉ l2ᵉ)
        ( λ Eᵉ →
          (xᵉ : Vᵉ) → ¬ᵉ (type-Propᵉ (Eᵉ (pairᵉ (Fin-UU-Fin'ᵉ 2ᵉ) (λ yᵉ → xᵉ))))))
```

## External links

-ᵉ [Graph](https://ncatlab.org/nlab/show/graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graphᵉ (discreteᵉ mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Simpleᵉ graph](https://www.wikidata.org/entity/Q15838309ᵉ) onᵉ Wikidataᵉ
-ᵉ [Simpleᵉ graph](https://mathworld.wolfram.com/SimpleGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ