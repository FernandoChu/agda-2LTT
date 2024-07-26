# Directed graph structures on standard finite sets

```agda
module graph-theory.directed-graph-structures-on-standard-finite-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "directedᵉ graphᵉ structure"ᵉ WD="directedᵉ graph"ᵉ WDID=Q1137726ᵉ Agda=structure-directed-graph-Finᵉ}}
onᵉ aᵉ [standardᵉ finiteᵉ set](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ n`ᵉ isᵉ aᵉ [binaryᵉ type-valuedᵉ relation](foundation.binary-relations.mdᵉ)

```text
  Finᵉ nᵉ → Finᵉ nᵉ → 𝒰.ᵉ
```

## Definitions

### Directed graph structures on standard finite sets

```agda
structure-directed-graph-Finᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
structure-directed-graph-Finᵉ lᵉ nᵉ = Finᵉ nᵉ → Finᵉ nᵉ → UUᵉ lᵉ
```

### Directed graphs on standard finite sets

```agda
Directed-Graph-Finᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Directed-Graph-Finᵉ lᵉ = Σᵉ ℕᵉ (structure-directed-graph-Finᵉ lᵉ)
```

### Labeled finite directed graphs on standard finite sets

Aᵉ
{{#conceptᵉ "labeledᵉ finiteᵉ directedᵉ graph"ᵉ Agda=Labeled-Finite-Directed-Graphᵉ}}
consistsᵉ ofᵉ aᵉ [naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`ᵉ
andᵉ aᵉ mapᵉ `Finᵉ nᵉ → Finᵉ nᵉ → ℕ`.ᵉ

```agda
Labeled-Finite-Directed-Graphᵉ : UUᵉ lzero
Labeled-Finite-Directed-Graphᵉ = Σᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ → Finᵉ nᵉ → ℕᵉ)
```

## External links

-ᵉ [Digraph](https://ncatlab.org/nlab/show/digraphᵉ) atᵉ $n$Labᵉ
-ᵉ [Directedᵉ graph](https://ncatlab.org/nlab/show/directed+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Directedᵉ graph](https://www.wikidata.org/entity/Q1137726ᵉ) onᵉ Wikdiataᵉ
-ᵉ [Directedᵉ graph](https://en.wikipedia.org/wiki/Directed_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Directedᵉ graph](https://mathworld.wolfram.com/DirectedGraph.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ