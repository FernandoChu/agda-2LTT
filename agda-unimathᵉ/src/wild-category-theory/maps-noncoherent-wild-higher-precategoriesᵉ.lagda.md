# Maps between noncoherent wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.maps-noncoherent-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.maps-globular-typesᵉ

open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "map"ᵉ Disambiguation="betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategories"ᵉ Agda=map-Noncoherent-Wild-Higher-Precategoryᵉ}}
`f`ᵉ betweenᵉ
[noncoherentᵉ wildᵉ higherᵉ precategories](wild-category-theory.noncoherent-wild-higher-precategories.mdᵉ)
`𝒜`ᵉ andᵉ `ℬ`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ onᵉ objectsᵉ `F₀ᵉ : objᵉ 𝒜ᵉ → objᵉ ℬ`,ᵉ andᵉ forᵉ everyᵉ
pairᵉ ofᵉ $n$-morphismsᵉ `f`ᵉ andᵉ `g`,ᵉ aᵉ mapᵉ ofᵉ $(n+1)$-morphismsᵉ

```text
  Fₙ₊₁ᵉ : (𝑛+1)-homᵉ 𝒞ᵉ fᵉ gᵉ → (𝑛+1)-homᵉ 𝒟ᵉ (Fₙᵉ fᵉ) (Fₙᵉ g).ᵉ
```

Aᵉ mapᵉ betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategoriesᵉ doesᵉ notᵉ haveᵉ to preserveᵉ
theᵉ identitiesᵉ orᵉ compositionᵉ in anyᵉ shapeᵉ orᵉ form,ᵉ andᵉ isᵉ theᵉ leastᵉ structuredᵉ
notionᵉ ofᵉ aᵉ "morphism"ᵉ betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategories.ᵉ Forᵉ aᵉ
notionᵉ ofᵉ "morphism"ᵉ betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategoriesᵉ thatᵉ in oneᵉ
senseᵉ preservesᵉ thisᵉ additionalᵉ structure,ᵉ seeᵉ
[colaxᵉ functorsᵉ betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategories](wild-category-theory.colax-functors-noncoherent-wild-higher-precategories.md).ᵉ

## Definitions

### Maps between noncoherent wild higher precategories

```agda
record
  map-Noncoherent-Wild-Higher-Precategoryᵉ
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ)
  (ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  where
  field
    obj-map-Noncoherent-Wild-Higher-Precategoryᵉ :
      obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ →
      obj-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ

    hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ :
      {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ} →
      map-Globular-Typeᵉ
        ( hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ)
        ( hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
          ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ)
          ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ))

open map-Noncoherent-Wild-Higher-Precategoryᵉ public

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  (Fᵉ : map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
  where

  hom-map-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ} →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
      ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ yᵉ)
  hom-map-Noncoherent-Wild-Higher-Precategoryᵉ =
    0-cell-map-Globular-Typeᵉ
      ( hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ)

  2-hom-map-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ)
      ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ gᵉ)
  2-hom-map-Noncoherent-Wild-Higher-Precategoryᵉ =
    1-cell-map-Globular-Typeᵉ
      ( hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ)

  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
    map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( 𝒜ᵉ)
        ( xᵉ)
        ( yᵉ))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( ℬᵉ)
        ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
        ( obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ yᵉ))
  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    λ where
    .obj-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      hom-map-Noncoherent-Wild-Higher-Precategoryᵉ
    .hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      globular-type-1-cell-map-Globular-Typeᵉ
        ( hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ)
```

### The identity map on a noncoherent wild higher precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ)
  where

  id-map-Noncoherent-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ 𝒜ᵉ
  id-map-Noncoherent-Wild-Higher-Precategoryᵉ =
    λ where
    .obj-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      idᵉ
    .hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      id-map-Globular-Typeᵉ _
```

### Composition of maps between noncoherent wild higher precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  {𝒞ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l5ᵉ l6ᵉ}
  (Gᵉ : map-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
  where

  comp-map-Noncoherent-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ 𝒞ᵉ
  comp-map-Noncoherent-Wild-Higher-Precategoryᵉ =
    λ where
    .obj-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ ∘ᵉ
      obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ
    .hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      comp-map-Globular-Typeᵉ
        ( hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ)
        ( hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ)
```