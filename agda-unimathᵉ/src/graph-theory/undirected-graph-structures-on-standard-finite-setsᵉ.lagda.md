# Undirected graph structures on standard finite sets

```agda
module graph-theory.undirected-graph-structures-on-standard-finite-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

```agda
Undirected-Graph-Finᵉ : UUᵉ (lsuc lzero)
Undirected-Graph-Finᵉ = Σᵉ ℕᵉ (λ Vᵉ → unordered-pairᵉ (Finᵉ Vᵉ) → ℕᵉ)
```

## External links

-ᵉ [Graph](https://ncatlab.org/nlab/show/graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graph](https://www.wikidata.org/entity/Q141488ᵉ) onᵉ Wikidataᵉ
-ᵉ [Graphᵉ (discreteᵉ mathematics)](<https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)>ᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Graph](https://mathworld.wolfram.com/Graph.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ