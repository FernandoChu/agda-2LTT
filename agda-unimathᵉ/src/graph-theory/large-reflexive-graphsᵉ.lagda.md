# Large reflexive graphs

```agda
module graph-theory.large-reflexive-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "largeᵉ reflexiveᵉ graph"ᵉ Agda=Large-Reflexive-Graphᵉ}} isᵉ aᵉ largeᵉ
directedᵉ graphᵉ [equipped](foundation.structure.mdᵉ) with aᵉ loopᵉ edgeᵉ atᵉ everyᵉ
vertex.ᵉ

## Definition

```agda
record
  Large-Reflexive-Graphᵉ
  (αᵉ : Level → Level) (βᵉ : Level → Level → Level) : UUωᵉ
  where

  field
    vertex-Large-Reflexive-Graphᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)

    edge-Large-Reflexive-Graphᵉ :
      {l1ᵉ l2ᵉ : Level} →
      vertex-Large-Reflexive-Graphᵉ l1ᵉ →
      vertex-Large-Reflexive-Graphᵉ l2ᵉ → UUᵉ (βᵉ l1ᵉ l2ᵉ)

    refl-Large-Reflexive-Graphᵉ :
      {lᵉ : Level} (xᵉ : vertex-Large-Reflexive-Graphᵉ lᵉ) →
      edge-Large-Reflexive-Graphᵉ xᵉ xᵉ

open Large-Reflexive-Graphᵉ public
```

## See also

-ᵉ [Reflexiveᵉ graphs](graph-theory.reflexive-graphs.mdᵉ)

## External links

-ᵉ [Reflexiveᵉ graph](https://ncatlab.org/nlab/show/reflexive+graphᵉ) atᵉ $n$Labᵉ
-ᵉ [Graph](https://www.wikidata.org/entity/Q141488ᵉ) onᵉ Wikidataᵉ
-ᵉ [Directedᵉ graph](https://en.wikipedia.org/wiki/Directed_graphᵉ) atᵉ Wikipediaᵉ
-ᵉ [Reflexiveᵉ graph](https://mathworld.wolfram.com/ReflexiveGraph.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ