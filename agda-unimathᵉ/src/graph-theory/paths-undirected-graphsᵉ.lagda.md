# Paths in undirected graphs

```agda
module graph-theory.paths-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.undirected-graphsᵉ
open import graph-theory.walks-undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **path**ᵉ in anᵉ [undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `G`ᵉ isᵉ aᵉ
[walk](graph-theory.walks-undirected-graphs.mdᵉ) `w`ᵉ in Gᵉ suchᵉ thatᵉ theᵉ inclusionᵉ
ofᵉ theᵉ typeᵉ ofᵉ verticesᵉ onᵉ `w`ᵉ intoᵉ theᵉ verticesᵉ ofᵉ `G`ᵉ isᵉ anᵉ
[injective](foundation.injective-maps.mdᵉ) function.ᵉ

**Note:**ᵉ Itᵉ isᵉ tooᵉ muchᵉ to askᵉ forᵉ forᵉ thisᵉ functionᵉ to beᵉ anᵉ
[embedding](foundation-core.embeddings.md),ᵉ sinceᵉ theᵉ typeᵉ ofᵉ verticesᵉ onᵉ `w`ᵉ isᵉ
equivalentᵉ to theᵉ
[standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ (nᵉ +ᵉ 1)`ᵉ where `n`ᵉ isᵉ theᵉ lengthᵉ ofᵉ theᵉ walk,ᵉ whereasᵉ theᵉ typeᵉ ofᵉ verticesᵉ
ofᵉ `G`ᵉ doesᵉ notᵉ needᵉ to beᵉ aᵉ [set](foundation-core.sets.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-path-walk-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ → UUᵉ l1ᵉ
  is-path-walk-Undirected-Graphᵉ wᵉ =
    is-injectiveᵉ (vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ wᵉ)

  path-Undirected-Graphᵉ :
    (xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
  path-Undirected-Graphᵉ xᵉ yᵉ =
    Σᵉ (walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ) is-path-walk-Undirected-Graphᵉ

  walk-path-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    path-Undirected-Graphᵉ xᵉ yᵉ → walk-Undirected-Graphᵉ Gᵉ xᵉ yᵉ
  walk-path-Undirected-Graphᵉ pᵉ = pr1ᵉ pᵉ

  length-path-Undirected-Graphᵉ :
    {xᵉ yᵉ : vertex-Undirected-Graphᵉ Gᵉ} →
    path-Undirected-Graphᵉ xᵉ yᵉ → ℕᵉ
  length-path-Undirected-Graphᵉ pᵉ =
    length-walk-Undirected-Graphᵉ Gᵉ (walk-path-Undirected-Graphᵉ pᵉ)
```

## Properties

### The constant walk is a path

```agda
is-path-refl-walk-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Undirected-Graphᵉ Gᵉ) →
  is-path-walk-Undirected-Graphᵉ Gᵉ (refl-walk-Undirected-Graphᵉ {xᵉ = xᵉ})
is-path-refl-walk-Undirected-Graphᵉ Gᵉ xᵉ =
  is-injective-is-contrᵉ
    ( vertex-vertex-on-walk-Undirected-Graphᵉ Gᵉ refl-walk-Undirected-Graphᵉ)
    ( is-contr-vertex-on-walk-refl-walk-Undirected-Graphᵉ Gᵉ xᵉ)
```

## External links

-ᵉ [Path](https://www.wikidata.org/entity/Q1415372ᵉ) onᵉ Wikidataᵉ
-ᵉ [Pathᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Graphᵉ path](https://mathworld.wolfram.com/GraphPath.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ