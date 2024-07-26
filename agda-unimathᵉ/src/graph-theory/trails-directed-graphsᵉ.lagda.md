# Trails in directed graphs

```agda
module graph-theory.trails-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.walks-directed-graphsᵉ
```

</details>

## Idea

Aᵉ **trail**ᵉ in aᵉ [directedᵉ graph](graph-theory.directed-graphs.mdᵉ) isᵉ aᵉ
[walk](graph-theory.walks-directed-graphs.mdᵉ) thatᵉ goesᵉ throughᵉ eachᵉ edgeᵉ atᵉ
mostᵉ once.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-trail-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} → walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-trail-walk-Directed-Graphᵉ wᵉ =
    is-injectiveᵉ (total-edge-edge-on-walk-Directed-Graphᵉ Gᵉ wᵉ)

  trail-Directed-Graphᵉ : (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  trail-Directed-Graphᵉ xᵉ yᵉ =
    Σᵉ (walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (is-trail-walk-Directed-Graphᵉ)

  walk-trail-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    trail-Directed-Graphᵉ xᵉ yᵉ → walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ
  walk-trail-Directed-Graphᵉ = pr1ᵉ

  is-trail-trail-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (tᵉ : trail-Directed-Graphᵉ xᵉ yᵉ) →
    is-trail-walk-Directed-Graphᵉ (walk-trail-Directed-Graphᵉ tᵉ)
  is-trail-trail-Directed-Graphᵉ = pr2ᵉ
```

## External links

-ᵉ [Pathᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Trail](https://www.wikidata.org/entity/Q17455228ᵉ) onᵉ Wikidataᵉ
-ᵉ [Trail](https://mathworld.wolfram.com/Trail.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ