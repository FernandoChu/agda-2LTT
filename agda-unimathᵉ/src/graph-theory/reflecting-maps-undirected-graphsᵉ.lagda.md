# Reflecting maps of undirected graphs

```agda
module graph-theory.reflecting-maps-undirected-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.symmetric-identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import graph-theory.undirected-graphsᵉ
```

</details>

## Idea

Aᵉ **reflectingᵉ map**ᵉ fromᵉ anᵉ
[undirectedᵉ graph](graph-theory.undirected-graphs.mdᵉ) `(Vᵉ ,ᵉ E)`ᵉ intoᵉ aᵉ typeᵉ `X`ᵉ
consistsᵉ ofᵉ aᵉ mapᵉ `fVᵉ : Vᵉ → X`ᵉ andᵉ aᵉ mapᵉ

```text
  fEᵉ : (vᵉ : unordered-pairᵉ Vᵉ) → Eᵉ vᵉ → symmetric-Idᵉ (map-unordered-pairᵉ fVᵉ v).ᵉ
```

Inᵉ otherᵉ words,ᵉ itᵉ mapsᵉ edgesᵉ intoᵉ theᵉ
[symmetricᵉ identityᵉ type](foundation.symmetric-identity-types.md).ᵉ

## Definitions

### Reflecting maps of undirected graphs

```agda
reflecting-map-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) (Xᵉ : UUᵉ l3ᵉ) →
  UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
reflecting-map-Undirected-Graphᵉ Gᵉ Xᵉ =
  Σᵉ ( vertex-Undirected-Graphᵉ Gᵉ → Xᵉ)
    ( λ fᵉ →
      (vᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
      edge-Undirected-Graphᵉ Gᵉ vᵉ → symmetric-Idᵉ (map-unordered-pairᵉ fᵉ vᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : reflecting-map-Undirected-Graphᵉ Gᵉ Xᵉ)
  where

  vertex-reflecting-map-Undirected-Graphᵉ : vertex-Undirected-Graphᵉ Gᵉ → Xᵉ
  vertex-reflecting-map-Undirected-Graphᵉ = pr1ᵉ fᵉ

  unordered-pair-vertices-reflecting-map-Undirected-Graphᵉ :
    unordered-pair-vertices-Undirected-Graphᵉ Gᵉ → unordered-pairᵉ Xᵉ
  unordered-pair-vertices-reflecting-map-Undirected-Graphᵉ =
    map-unordered-pairᵉ vertex-reflecting-map-Undirected-Graphᵉ

  edge-reflecting-map-Undirected-Graphᵉ :
    (vᵉ : unordered-pair-vertices-Undirected-Graphᵉ Gᵉ) →
    edge-Undirected-Graphᵉ Gᵉ vᵉ →
    symmetric-Idᵉ (unordered-pair-vertices-reflecting-map-Undirected-Graphᵉ vᵉ)
  edge-reflecting-map-Undirected-Graphᵉ = pr2ᵉ fᵉ
```

### Terminal reflecting maps

```agda
terminal-reflecting-map-Undirected-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Undirected-Graphᵉ l1ᵉ l2ᵉ) →
  reflecting-map-Undirected-Graphᵉ Gᵉ unitᵉ
pr1ᵉ (terminal-reflecting-map-Undirected-Graphᵉ Gᵉ) xᵉ = starᵉ
pr1ᵉ (pr2ᵉ (terminal-reflecting-map-Undirected-Graphᵉ Gᵉ) pᵉ eᵉ) = starᵉ
pr2ᵉ (pr2ᵉ (terminal-reflecting-map-Undirected-Graphᵉ Gᵉ) pᵉ eᵉ) xᵉ =
  eq-is-contrᵉ is-contr-unitᵉ
```

## External links

-ᵉ [Geometricᵉ realization](https://ncatlab.org/nlab/show/geometric+realizationᵉ)
  atᵉ $n$Labᵉ