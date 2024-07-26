# Hypergraphs

```agda
module graph-theory.hypergraphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-tuplesᵉ
```

</details>

## Idea

Aᵉ **`k`-hypergraph**ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `V`ᵉ ofᵉ verticesᵉ andᵉ aᵉ familyᵉ `E`ᵉ ofᵉ
typesᵉ indexedᵉ byᵉ theᵉ [unorderedᵉ `k`-tuples](foundation.unordered-tuples.mdᵉ) ofᵉ
vertices.ᵉ

## Definition

```agda
Hypergraphᵉ : (l1ᵉ l2ᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Hypergraphᵉ l1ᵉ l2ᵉ kᵉ = Σᵉ (UUᵉ l1ᵉ) (λ Vᵉ → unordered-tupleᵉ kᵉ Vᵉ → UUᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : ℕᵉ} (Gᵉ : Hypergraphᵉ l1ᵉ l2ᵉ kᵉ)
  where

  vertex-Hypergraphᵉ : UUᵉ l1ᵉ
  vertex-Hypergraphᵉ = pr1ᵉ Gᵉ

  unordered-tuple-vertices-Hypergraphᵉ : UUᵉ (lsuc lzero ⊔ l1ᵉ)
  unordered-tuple-vertices-Hypergraphᵉ = unordered-tupleᵉ kᵉ vertex-Hypergraphᵉ

  simplex-Hypergraphᵉ : unordered-tuple-vertices-Hypergraphᵉ → UUᵉ l2ᵉ
  simplex-Hypergraphᵉ = pr2ᵉ Gᵉ
```

## External links

-ᵉ [Hypergraph](https://ncatlab.org/nlab/show/hypergraphᵉ) atᵉ $n$Labᵉ
-ᵉ [Hypergraph](https://www.wikidata.org/entity/Q840247ᵉ) onᵉ Wikidataᵉ
-ᵉ [Hypergraph](https://en.wikipedia.org/wiki/Hypergraphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Hypergraph](https://mathworld.wolfram.com/Hypergraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ