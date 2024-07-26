# Regular undirected graph

```agda
module graph-theory.regular-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.mere-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.neighbors-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **regularᵉ undirectedᵉ graph**ᵉ isᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) ofᵉ whichᵉ eachᵉ vertexᵉ hasᵉ
theᵉ sameᵉ numberᵉ ofᵉ
[incidentᵉ edges](graph-theory.neighbors-undirected-graphs.md).ᵉ

## Definition

```agda
is-regular-undirected-graph-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ)
  (Gᵉ : Undirected-Graphᵉ l2ᵉ l3ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-regular-undirected-graph-Propᵉ Xᵉ Gᵉ =
  Π-Propᵉ
    ( vertex-Undirected-Graphᵉ Gᵉ)
    ( λ xᵉ → mere-equiv-Propᵉ Xᵉ (neighbor-Undirected-Graphᵉ Gᵉ xᵉ))

is-regular-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Gᵉ : Undirected-Graphᵉ l2ᵉ l3ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-regular-Undirected-Graphᵉ Xᵉ Gᵉ =
  type-Propᵉ (is-regular-undirected-graph-Propᵉ Xᵉ Gᵉ)

is-prop-is-regular-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Gᵉ : Undirected-Graphᵉ l2ᵉ l3ᵉ) →
  is-propᵉ (is-regular-Undirected-Graphᵉ Xᵉ Gᵉ)
is-prop-is-regular-Undirected-Graphᵉ Xᵉ Gᵉ =
  is-prop-type-Propᵉ (is-regular-undirected-graph-Propᵉ Xᵉ Gᵉ)
```

## External links

-ᵉ [Regularᵉ graph](https://d3gt.com/unit.html?regular-graphᵉ) atᵉ D3ᵉ Graphᵉ Theoryᵉ
-ᵉ [Regularᵉ graph](https://www.wikidata.org/entity/Q826467ᵉ) onᵉ Wikidataᵉ
-ᵉ [Regularᵉ graph](https://en.wikipedia.org/wiki/Regular_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Regularᵉ graph](https://mathworld.wolfram.com/RegularGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ