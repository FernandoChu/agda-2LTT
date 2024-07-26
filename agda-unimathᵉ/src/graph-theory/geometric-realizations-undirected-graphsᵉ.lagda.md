# Geometric realizations of undirected graphs

```agda
module graph-theory.geometric-realizations-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.symmetric-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.reflecting-maps-undirected-graphsᵉ
open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Theᵉ **geometricᵉ realization**ᵉ ofᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `G`ᵉ isᵉ theᵉ initialᵉ typeᵉ
`X`ᵉ equippedᵉ with aᵉ
[reflectingᵉ map](graph-theory.reflecting-maps-undirected-graphs.mdᵉ) fromᵉ `G`ᵉ
intoᵉ `X`.ᵉ

## Definition

```agda
precomp-reflecting-map-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ} (Yᵉ : UUᵉ l4ᵉ) →
  reflecting-map-Undirected-Graphᵉ Gᵉ Xᵉ →
  (Xᵉ → Yᵉ) → reflecting-map-Undirected-Graphᵉ Gᵉ Yᵉ
pr1ᵉ (precomp-reflecting-map-Undirected-Graphᵉ Gᵉ Yᵉ fᵉ hᵉ) =
  hᵉ ∘ᵉ vertex-reflecting-map-Undirected-Graphᵉ Gᵉ fᵉ
pr2ᵉ (precomp-reflecting-map-Undirected-Graphᵉ Gᵉ Yᵉ fᵉ hᵉ) vᵉ eᵉ =
  map-symmetric-Idᵉ hᵉ
    ( unordered-pair-vertices-reflecting-map-Undirected-Graphᵉ Gᵉ fᵉ vᵉ)
    ( edge-reflecting-map-Undirected-Graphᵉ Gᵉ fᵉ vᵉ eᵉ)

is-geometric-realization-reflecting-map-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (lᵉ : Level) (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : reflecting-map-Undirected-Graphᵉ Gᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc lᵉ)
is-geometric-realization-reflecting-map-Undirected-Graphᵉ lᵉ Gᵉ fᵉ =
  (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (precomp-reflecting-map-Undirected-Graphᵉ Gᵉ Yᵉ fᵉ)
```

## External links

-ᵉ [Geometricᵉ realization](https://ncatlab.org/nlab/show/geometric+realizationᵉ)
  atᵉ $n$Labᵉ