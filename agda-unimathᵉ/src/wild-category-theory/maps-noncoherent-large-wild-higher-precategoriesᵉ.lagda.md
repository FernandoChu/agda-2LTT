# Maps between noncoherent large wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.maps-noncoherent-large-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.large-globular-typesᵉ
open import structured-types.maps-globular-typesᵉ
open import structured-types.maps-large-globular-typesᵉ

open import wild-category-theory.maps-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-large-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "map"ᵉ Disambiguation="betweenᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories"ᵉ Agda=map-Noncoherent-Large-Wild-Higher-Precategoryᵉ}}
`f`ᵉ betweenᵉ
[noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories](wild-category-theory.noncoherent-large-wild-higher-precategories.mdᵉ)
`𝒜`ᵉ andᵉ `ℬ`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ onᵉ objectsᵉ `F₀ᵉ : objᵉ 𝒜ᵉ → objᵉ ℬ`,ᵉ andᵉ forᵉ everyᵉ
pairᵉ ofᵉ $n$-morphismsᵉ `f`ᵉ andᵉ `g`,ᵉ aᵉ mapᵉ ofᵉ $(n+1)$-morphismsᵉ

```text
  Fₙ₊₁ᵉ : (𝑛+1)-homᵉ 𝒞ᵉ fᵉ gᵉ → (𝑛+1)-homᵉ 𝒟ᵉ (Fₙᵉ fᵉ) (Fₙᵉ g).ᵉ
```

Aᵉ mapᵉ betweenᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategoriesᵉ doesᵉ notᵉ haveᵉ to
preserveᵉ theᵉ identitiesᵉ orᵉ compositionᵉ in anyᵉ shapeᵉ orᵉ form,ᵉ andᵉ isᵉ theᵉ leastᵉ
structuredᵉ notionᵉ ofᵉ aᵉ "morphism"ᵉ betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategories.ᵉ
Forᵉ aᵉ notionᵉ ofᵉ "morphism"ᵉ betweenᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategoriesᵉ
thatᵉ in oneᵉ senseᵉ preservesᵉ thisᵉ additionalᵉ structure,ᵉ seeᵉ
[colaxᵉ functorsᵉ betweenᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories](wild-category-theory.colax-functors-noncoherent-large-wild-higher-precategories.md).ᵉ

## Definitions

### Maps between noncoherent large wild higher precategories

```agda
record
  map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} (δᵉ : Level → Level)
  (𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ)
  (ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ) : UUωᵉ
  where
  field
    obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      {lᵉ : Level} →
      obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ lᵉ →
      obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ (δᵉ lᵉ)

    hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      {l1ᵉ l2ᵉ : Level}
      {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
      {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ} →
      map-Globular-Typeᵉ
        ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ)
        ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
          ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ)
          ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ))

open map-Noncoherent-Large-Wild-Higher-Precategoryᵉ public

module _
  {α1ᵉ α2ᵉ : Level → Level} {β1ᵉ β2ᵉ : Level → Level → Level} {δᵉ : Level → Level}
  {𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ}
  {ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ}
  (Fᵉ : map-Noncoherent-Large-Wild-Higher-Precategoryᵉ δᵉ 𝒜ᵉ ℬᵉ)
  where

  hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ} →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
      ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ yᵉ)
  hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    0-cell-map-Globular-Typeᵉ
      ( hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ)

  2-hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ)
      ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ gᵉ)
  2-hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    1-cell-map-Globular-Typeᵉ
      ( hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ)

  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ)
    (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ) →
    map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒜ᵉ)
        ( xᵉ)
        ( yᵉ))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( ℬᵉ)
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
        ( obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ yᵉ))
  hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    λ where
    .obj-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    .hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ →
      globular-type-1-cell-map-Globular-Typeᵉ
        ( hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ)
```

### The identity map on a noncoherent large wild higher precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ αᵉ βᵉ)
  where

  id-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Large-Wild-Higher-Precategoryᵉ (λ lᵉ → lᵉ) 𝒜ᵉ 𝒜ᵉ
  id-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      idᵉ
    .hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      id-map-Globular-Typeᵉ _
```

### Composition of maps of noncoherent large wild higher precategories

```agda
module _
  {α1ᵉ α2ᵉ α3ᵉ : Level → Level}
  {β1ᵉ β2ᵉ β3ᵉ : Level → Level → Level}
  {δ1ᵉ δ2ᵉ : Level → Level}
  {𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ}
  {ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ}
  {𝒞ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α3ᵉ β3ᵉ}
  (Gᵉ : map-Noncoherent-Large-Wild-Higher-Precategoryᵉ δ2ᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : map-Noncoherent-Large-Wild-Higher-Precategoryᵉ δ1ᵉ 𝒜ᵉ ℬᵉ)
  where

  comp-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Large-Wild-Higher-Precategoryᵉ (λ lᵉ → δ2ᵉ (δ1ᵉ lᵉ)) 𝒜ᵉ 𝒞ᵉ
  comp-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Gᵉ ∘ᵉ
      obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ
    .hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      comp-map-Globular-Typeᵉ
        ( hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Gᵉ)
        ( hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ)
```