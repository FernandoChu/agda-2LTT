# Colax functors between large noncoherent wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.colax-functors-noncoherent-large-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.maps-globular-typesᵉ

open import wild-category-theory.colax-functors-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.maps-noncoherent-large-wild-higher-precategoriesᵉ
open import wild-category-theory.maps-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-large-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "colaxᵉ functor"ᵉ Disambiguation="betweenᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories"ᵉ Agda=colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ}}
`f`ᵉ betweenᵉ
[noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories](wild-category-theory.noncoherent-large-wild-higher-precategories.mdᵉ)
`𝒜`ᵉ andᵉ `ℬ`ᵉ isᵉ aᵉ
[mapᵉ ofᵉ noncoherentᵉ largeᵉ wildᵉ higherᵉ precategories](wild-category-theory.maps-noncoherent-large-wild-higher-precategories.mdᵉ)
thatᵉ preservesᵉ identityᵉ morphismsᵉ andᵉ compositionᵉ _colaxly_.ᵉ Thisᵉ meansᵉ thatᵉ forᵉ
everyᵉ $n$-morphismᵉ `f`ᵉ in `𝒜`,ᵉ where weᵉ takeᵉ $0$-morphismsᵉ to beᵉ objects,ᵉ thereᵉ
isᵉ anᵉ $(n+1)$-morphismᵉ

```text
  Fₙ₊₁ᵉ (id-homᵉ 𝒜ᵉ fᵉ) ⇒ᵉ id-homᵉ ℬᵉ (Fₙᵉ fᵉ)
```

in `ℬ`,ᵉ andᵉ forᵉ everyᵉ pairᵉ ofᵉ composableᵉ $(n+1)$-morphismsᵉ `g`ᵉ afterᵉ `f`ᵉ in `𝒜`,ᵉ
thereᵉ isᵉ anᵉ $(n+2)$-morphismᵉ

```text
  Fₙ₊₁ᵉ (gᵉ ∘ᵉ fᵉ) ⇒ᵉ (Fₙ₊₁ᵉ gᵉ) ∘ᵉ (Fₙ₊₁ᵉ fᵉ)
```

in `ℬ`.ᵉ

## Definitions

### The predicate of being a colax functor between noncoherent wild higher precategories

```agda
record
  is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  {α1ᵉ α2ᵉ : Level → Level}
  {β1ᵉ β2ᵉ : Level → Level → Level}
  {δᵉ : Level → Level}
  {𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ}
  {ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ}
  (Fᵉ : map-Noncoherent-Large-Wild-Higher-Precategoryᵉ δᵉ 𝒜ᵉ ℬᵉ) : UUωᵉ
  where
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      {lᵉ : Level}
      (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ lᵉ) →
      2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ
          ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ {xᵉ = xᵉ}))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
          { xᵉ = obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ xᵉ})

    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level}
      {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
      {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ}
      {zᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l3ᵉ}
      (gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ yᵉ zᵉ)
      (fᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ) →
      2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ
          ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ gᵉ fᵉ))
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
          ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ gᵉ)
          ( hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ fᵉ))

    is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ)
      (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ) →
      is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( Fᵉ)
          ( xᵉ)
          ( yᵉ))

open is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ public
```

### The type of colax functors between noncoherent wild higher precategories

```agda
record
  colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
  {α1ᵉ α2ᵉ : Level → Level}
  {β1ᵉ β2ᵉ : Level → Level → Level}
  (δᵉ : Level → Level)
  (𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ)
  (ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ) : UUωᵉ
  where

  field
    map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      map-Noncoherent-Large-Wild-Higher-Precategoryᵉ δᵉ 𝒜ᵉ ℬᵉ

    is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
      is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
```

```agda
  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {lᵉ : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ lᵉ →
    obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ (δᵉ lᵉ)
  obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    obj-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ} →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ →
    hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ)
      ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ)
  hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ

  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {lᵉ : Level}
    (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ lᵉ) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ {xᵉ = xᵉ}))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
        { xᵉ = obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ})
  preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ}
    {zᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l3ᵉ}
    (gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ yᵉ zᵉ)
    (fᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ gᵉ fᵉ))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ gᵉ)
        ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ))
  preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ fᵉ)
      ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ gᵉ)
  2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    2-hom-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ

  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ}
    {yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ} →
    map-Globular-Typeᵉ
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ)
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategoryᵉ ℬᵉ
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ))
  hom-globular-type-map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    hom-globular-type-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
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
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ))
  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    hom-noncoherent-wild-higher-precategory-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)

  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l1ᵉ)
    (yᵉ : obj-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ l2ᵉ) →
    colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( 𝒜ᵉ)
        ( xᵉ)
        ( yᵉ))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( ℬᵉ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ yᵉ))
  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    ( map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( xᵉ)
        ( yᵉ) ,ᵉ
      is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        ( is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))

open colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ public
```

### The identity colax functor on a noncoherent large wild higher precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ αᵉ βᵉ)
  where

  is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( id-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ)
  is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
      .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        xᵉ →
        id-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ
      .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
        gᵉ fᵉ →
        id-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ
      .is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
        is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
          ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategoryᵉ
            ( 𝒜ᵉ)
            ( xᵉ)
            ( yᵉ))

  id-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ (λ lᵉ → lᵉ) 𝒜ᵉ 𝒜ᵉ
  id-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      id-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒜ᵉ
    .is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      is-colax-functor-id-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
```

### Composition of colax functors between noncoherent wild higher precategories

```agda
module _
  {α1ᵉ α2ᵉ α3ᵉ : Level → Level}
  {β1ᵉ β2ᵉ β3ᵉ : Level → Level → Level}
  {δ1ᵉ δ2ᵉ : Level → Level}
  {𝒜ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α1ᵉ β1ᵉ}
  {ℬᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α2ᵉ β2ᵉ}
  {𝒞ᵉ : Noncoherent-Large-Wild-Higher-Precategoryᵉ α3ᵉ β3ᵉ}
  (Gᵉ : colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ δ2ᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ δ1ᵉ 𝒜ᵉ ℬᵉ)
  where

  map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Large-Wild-Higher-Precategoryᵉ (λ lᵉ → δ2ᵉ (δ1ᵉ lᵉ)) 𝒜ᵉ 𝒞ᵉ
  map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    comp-map-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Gᵉ)
      ( map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ)

  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ)
  is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      xᵉ →
      comp-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( Gᵉ)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ xᵉ))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Gᵉ
          ( preserves-id-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
            ( Fᵉ)
            ( xᵉ)))
    .preserves-comp-hom-is-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      gᵉ fᵉ →
      comp-2-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ 𝒞ᵉ
        ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( Gᵉ)
          ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ gᵉ)
          ( hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ fᵉ))
        ( 2-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Gᵉ
          ( preserves-comp-hom-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
            ( Fᵉ)
            ( gᵉ)
            ( fᵉ)))
    .is-colax-functor-map-hom-Noncoherent-Large-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
      is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( Gᵉ)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
          ( obj-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ Fᵉ yᵉ))
        ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
          ( Fᵉ)
          ( xᵉ)
          ( yᵉ))

  comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ :
    colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
      ( λ lᵉ → δ2ᵉ (δ1ᵉ lᵉ))
      ( 𝒜ᵉ)
      ( 𝒞ᵉ)
  comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ =
    λ where
    .map-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      map-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
    .is-colax-functor-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ →
      is-colax-functor-comp-colax-functor-Noncoherent-Large-Wild-Higher-Precategoryᵉ
```