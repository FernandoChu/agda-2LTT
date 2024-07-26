# Reflexive graphs

```agda
module graph-theory.reflexive-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "reflexiveᵉ graph"ᵉ Agda=Reflexive-Graphᵉ}} isᵉ aᵉ
[directedᵉ graph](graph-theory.directed-graphs.mdᵉ)
[equipped](foundation.structure.mdᵉ) with aᵉ loopᵉ edgeᵉ atᵉ everyᵉ vertex.ᵉ

## Definition

```agda
Reflexive-Graphᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Reflexive-Graphᵉ l1ᵉ l2ᵉ =
  Σᵉ (UUᵉ l1ᵉ) (λ Vᵉ → Σᵉ (Vᵉ → Vᵉ → UUᵉ l2ᵉ) (λ Eᵉ → (vᵉ : Vᵉ) → Eᵉ vᵉ vᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Reflexive-Graphᵉ l1ᵉ l2ᵉ)
  where

  vertex-Reflexive-Graphᵉ : UUᵉ l1ᵉ
  vertex-Reflexive-Graphᵉ = pr1ᵉ Gᵉ

  edge-Reflexive-Graphᵉ : vertex-Reflexive-Graphᵉ → vertex-Reflexive-Graphᵉ → UUᵉ l2ᵉ
  edge-Reflexive-Graphᵉ = pr1ᵉ (pr2ᵉ Gᵉ)

  refl-Reflexive-Graphᵉ : (xᵉ : vertex-Reflexive-Graphᵉ) → edge-Reflexive-Graphᵉ xᵉ xᵉ
  refl-Reflexive-Graphᵉ = pr2ᵉ (pr2ᵉ Gᵉ)

  graph-Reflexive-Graphᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ
  graph-Reflexive-Graphᵉ = vertex-Reflexive-Graphᵉ ,ᵉ edge-Reflexive-Graphᵉ
```

## See also

-ᵉ [Largeᵉ reflexiveᵉ graphs](graph-theory.large-reflexive-graphs.mdᵉ)

## External links

-ᵉ [Reflexiveᵉ graph](https://ncatlab.org/nlab/show/reflexive+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graph](https://www.wikidata.org/entity/Q141488ᵉ) onᵉ Wikidataᵉ
-ᵉ [Directedᵉ graph](https://en.wikipedia.org/wiki/Directed_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Reflexiveᵉ graph](https://mathworld.wolfram.com/ReflexiveGraph.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ