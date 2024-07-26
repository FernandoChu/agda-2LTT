# Connected graphs

```agda
module graph-theory.connected-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.undirected-graphsᵉ
open import graph-theory.walks-undirected-graphsᵉ
```

</details>

## Idea

Anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) isᵉ saidᵉ to beᵉ
**connected**ᵉ ifᵉ anyᵉ pointᵉ canᵉ beᵉ reachedᵉ fromᵉ anyᵉ pointᵉ byᵉ aᵉ
[walk](graph-theory.walks-undirected-graphs.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-connected-Undirected-Graphᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lzero)
  is-connected-Undirected-Graphᵉ =
    (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
    type-trunc-Propᵉ (walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
```

## Properties

### The property of being connected for an undirected graph is a proposition

```agda
  is-prop-is-connected-Undirected-Graphᵉ
    : is-propᵉ is-connected-Undirected-Graphᵉ
  is-prop-is-connected-Undirected-Graphᵉ =
    is-prop-Πᵉ (λ _ → is-prop-Πᵉ (λ _ → is-prop-type-trunc-Propᵉ))
```

## External links

-ᵉ [Connectedᵉ graph](https://ncatlab.org/nlab/show/connected+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Connectedᵉ graph](https://www.wikidata.org/entity/Q230655ᵉ) onᵉ Wikidataᵉ
-ᵉ [Connectivityᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Connectivity_(graph_theory)>ᵉ)
  onᵉ Wikipediaᵉ
-ᵉ [Connectedᵉ graph](https://mathworld.wolfram.com/ConnectedGraph.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ