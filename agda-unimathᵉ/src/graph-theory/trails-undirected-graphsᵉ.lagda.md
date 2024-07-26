# Trails in undirected graphs

```agda
module graph-theory.trails-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.undirected-graphsᵉ
open import graph-theory.walks-undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **trail**ᵉ in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) isᵉ aᵉ
[walk](graph-theory.walks-undirected-graphs.mdᵉ) thatᵉ passesᵉ throughᵉ eachᵉ edgeᵉ atᵉ
mostᵉ once.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-trail-walk-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ →
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-trail-walk-Undirected-Graphᵉ wᵉ =
    is-injectiveᵉ (edge-edge-on-walk-Undirected-Graphᵉ Gᵉ wᵉ)

  trail-Undirected-Graphᵉ :
    (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  trail-Undirected-Graphᵉ xᵉ yᵉ =
    Σᵉ (walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) is-trail-walk-Undirected-Graphᵉ

  walk-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    trail-Undirected-Graphᵉ xᵉ yᵉ → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ
  walk-trail-Undirected-Graphᵉ = pr1ᵉ

  is-trail-walk-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ) →
    is-trail-walk-Undirected-Graphᵉ (walk-trail-Undirected-Graphᵉ tᵉ)
  is-trail-walk-trail-Undirected-Graphᵉ = pr2ᵉ

  is-vertex-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    trail-Undirected-Graphᵉ xᵉ yᵉ → vertex-Undirected-Graphᵉ Gᵉ → UUᵉ l1ᵉ
  is-vertex-on-trail-Undirected-Graphᵉ tᵉ =
    is-vertex-on-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  vertex-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → trail-Undirected-Graphᵉ xᵉ yᵉ → UUᵉ l1ᵉ
  vertex-on-trail-Undirected-Graphᵉ tᵉ =
    vertex-on-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  vertex-vertex-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ) →
    vertex-on-trail-Undirected-Graphᵉ tᵉ → vertex-Undirected-Graphᵉ Gᵉ
  vertex-vertex-on-trail-Undirected-Graphᵉ tᵉ =
    vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ
      ( walk-trail-Undirected-Graphᵉ tᵉ)

  is-edge-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ)
    (pᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ)
    (eᵉ : edge-Undirected-Graphᵉ Gᵉ pᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  is-edge-on-trail-Undirected-Graphᵉ tᵉ =
    is-edge-on-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  edge-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ) →
    UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  edge-on-trail-Undirected-Graphᵉ tᵉ =
    edge-on-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  edge-edge-on-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ) →
    edge-on-trail-Undirected-Graphᵉ tᵉ → total-edge-Undirected-Graphᵉ Gᵉ
  edge-edge-on-trail-Undirected-Graphᵉ tᵉ =
    edge-edge-on-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  length-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → trail-Undirected-Graphᵉ xᵉ yᵉ → ℕᵉ
  length-trail-Undirected-Graphᵉ tᵉ =
    length-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  is-constant-trail-Undirected-Graph-Propᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    trail-Undirected-Graphᵉ xᵉ yᵉ → Propᵉ lzero
  is-constant-trail-Undirected-Graph-Propᵉ tᵉ =
    is-constant-walk-Undirected-Graph-Propᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  is-constant-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → trail-Undirected-Graphᵉ xᵉ yᵉ → UUᵉ lzero
  is-constant-trail-Undirected-Graphᵉ tᵉ =
    is-constant-walk-Undirected-Graphᵉ Gᵉ (walk-trail-Undirected-Graphᵉ tᵉ)

  is-decidable-is-constant-trail-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ xᵉ yᵉ) →
    is-decidableᵉ (is-constant-trail-Undirected-Graphᵉ tᵉ)
  is-decidable-is-constant-trail-Undirected-Graphᵉ tᵉ =
    is-decidable-is-constant-walk-Undirected-Graphᵉ Gᵉ
      ( walk-trail-Undirected-Graphᵉ tᵉ)
```

## Properties

### Any constant walk is a trail

```agda
is-trail-refl-walk-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
  is-trail-walk-Undirected-Graphᵉ Gᵉ (refl-walk-Undirected-Graphᵉ {xᵉ = xᵉ})
is-trail-refl-walk-Undirected-Graphᵉ Gᵉ {xᵉ} =
  is-injective-is-emptyᵉ
    ( edge-edge-on-walk-Undirected-Graphᵉ Gᵉ (refl-walk-Undirected-Graphᵉ {xᵉ = xᵉ}))
    ( is-empty-edge-on-walk-refl-walk-Undirected-Graphᵉ Gᵉ xᵉ)
```

### Both walks in the decomposition of a trail are trails

Noteᵉ thatᵉ in general,ᵉ theᵉ concatenationᵉ ofᵉ twoᵉ trailsᵉ doesᵉ notᵉ needᵉ to beᵉ aᵉ
trail.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {xᵉ : vertex-Undirected-Graphᵉ Gᵉ}
  where

  first-segment-trail-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
    (vᵉ : vertex-on-trail-Undirected-Graphᵉ Gᵉ tᵉ) →
    walk-Undirected-Graphᵉ Gᵉ xᵉ
      ( vertex-vertex-on-trail-Undirected-Graphᵉ Gᵉ tᵉ vᵉ)
  first-segment-trail-Undirected-Graphᵉ tᵉ =
    first-segment-walk-Undirected-Graphᵉ Gᵉ
      ( walk-trail-Undirected-Graphᵉ Gᵉ tᵉ)

  second-segment-trail-Undirected-Graphᵉ :
    {yᵉ : vertex-Undirected-Graphᵉ Gᵉ} (tᵉ : trail-Undirected-Graphᵉ Gᵉ xᵉ yᵉ)
    (vᵉ : vertex-on-trail-Undirected-Graphᵉ Gᵉ tᵉ) →
    walk-Undirected-Graphᵉ Gᵉ
      ( vertex-vertex-on-trail-Undirected-Graphᵉ Gᵉ tᵉ vᵉ)
      ( yᵉ)
  second-segment-trail-Undirected-Graphᵉ tᵉ =
    second-segment-walk-Undirected-Graphᵉ Gᵉ
      ( walk-trail-Undirected-Graphᵉ Gᵉ tᵉ)
```

## External links

-ᵉ [Pathᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Trail](https://www.wikidata.org/entity/Q17455228ᵉ) onᵉ Wikidataᵉ
-ᵉ [Trail](https://mathworld.wolfram.com/Trail.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ