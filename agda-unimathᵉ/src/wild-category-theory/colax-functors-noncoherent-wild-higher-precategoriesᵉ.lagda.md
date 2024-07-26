# Colax functors between noncoherent wild higher precategories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module wild-category-theory.colax-functors-noncoherent-wild-higher-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.globular-typesᵉ
open import structured-types.maps-globular-typesᵉ

open import wild-category-theory.maps-noncoherent-wild-higher-precategoriesᵉ
open import wild-category-theory.noncoherent-wild-higher-precategoriesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "colaxᵉ functor"ᵉ Disambiguation="betweenᵉ noncoherentᵉ wildᵉ higherᵉ precategories"ᵉ Agda=colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ}}
`F`ᵉ betweenᵉ
[noncoherentᵉ wildᵉ higherᵉ precategories](wild-category-theory.noncoherent-wild-higher-precategories.mdᵉ)
`𝒜`ᵉ andᵉ `ℬ`ᵉ isᵉ aᵉ
[mapᵉ ofᵉ noncoherentᵉ wildᵉ higherᵉ precategories](wild-category-theory.maps-noncoherent-wild-higher-precategories.mdᵉ)
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
  is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  (Fᵉ : map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  where
  coinductiveᵉ
  field
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
      (xᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
      2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ
          ( id-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ {xᵉ}))
        ( id-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
          { obj-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ xᵉ})

    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
      {xᵉ yᵉ zᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ}
      (gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ yᵉ zᵉ)
      (fᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ) →
      2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ
          ( comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ gᵉ fᵉ))
        ( comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
          ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ gᵉ)
          ( hom-map-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ fᵉ))

    is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategoryᵉ :
      (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
      is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategoryᵉ
          ( Fᵉ)
          ( xᵉ)
          ( yᵉ))

open is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ public
```

### The type of colax functors between noncoherent wild higher precategories

```agda
colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ)
  (ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ =
  Σᵉ ( map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
    ( is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  (Fᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
  where

  map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ
  map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ = pr1ᵉ Fᵉ

  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)
  is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ = pr2ᵉ Fᵉ

  obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ →
    obj-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
  obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    obj-map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

  hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ} →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ →
    hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ)
      ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ)
  hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    hom-map-Noncoherent-Wild-Higher-Precategoryᵉ
      map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ

  preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( id-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ {xᵉ}))
      ( id-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
        { obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ})
  preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

  preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ}
    (gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ yᵉ zᵉ)
    (fᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ) →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ gᵉ fᵉ))
      ( comp-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ gᵉ)
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ))
  preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ}
    {fᵉ gᵉ : hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ} →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ fᵉ gᵉ →
    2-hom-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ fᵉ)
      ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ gᵉ)
  2-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    2-hom-map-Noncoherent-Wild-Higher-Precategoryᵉ
      map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ

  hom-globular-type-map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    {xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ} →
    map-Globular-Typeᵉ
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ xᵉ yᵉ)
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ))
  hom-globular-type-map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    hom-globular-type-map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
    map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( 𝒜ᵉ)
        ( xᵉ)
        ( yᵉ))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( ℬᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ))
  map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    hom-noncoherent-wild-higher-precategory-map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)

  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    (xᵉ yᵉ : obj-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ) →
    colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( 𝒜ᵉ)
        ( xᵉ)
        ( yᵉ))
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
        ( ℬᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ yᵉ))
  hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
    xᵉ yᵉ =
    ( map-hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( xᵉ)
        ( yᵉ) ,ᵉ
      is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategoryᵉ
        ( is-colax-functor-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ)
        ( xᵉ)
        ( yᵉ))
```

### The identity colax functor on a noncoherent wild higher precategory

```agda
is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ) →
  is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
    ( id-map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ)
is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ =
  λ where
    .preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      xᵉ →
      id-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ
    .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      gᵉ fᵉ →
      id-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ
    .is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
      is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategoryᵉ
          ( 𝒜ᵉ)
          ( xᵉ)
          ( yᵉ))

id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ) →
  colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ 𝒜ᵉ
id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ =
  ( id-map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ,ᵉ
    is-colax-functor-id-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ)
```

### Composition of colax functors between noncoherent wild higher precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  {𝒞ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l5ᵉ l6ᵉ}
  (Gᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
  where

  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    map-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ 𝒞ᵉ
  map-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    comp-map-Noncoherent-Wild-Higher-Precategoryᵉ
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ)
      ( map-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ)

is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  {𝒞ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l5ᵉ l6ᵉ}
  (Gᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ) →
  is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
    ( map-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ Fᵉ)
is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
  {𝒞ᵉ = 𝒞ᵉ} Gᵉ Fᵉ =
  λ where
  .preserves-id-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ →
    comp-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒞ᵉ
      ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ xᵉ))
      ( 2-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ
        ( preserves-id-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ
          ( xᵉ)))
  .preserves-comp-hom-is-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ gᵉ fᵉ →
    comp-2-hom-Noncoherent-Wild-Higher-Precategoryᵉ 𝒞ᵉ
      ( preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ gᵉ)
        ( hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ fᵉ))
      ( 2-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ
        ( preserves-comp-hom-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ
          ( gᵉ)
          ( fᵉ)))
  .is-colax-functor-map-hom-Noncoherent-Wild-Higher-Precategoryᵉ xᵉ yᵉ →
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
      ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( Gᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ xᵉ)
        ( obj-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Fᵉ yᵉ))
      ( hom-noncoherent-wild-higher-precategory-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ
        ( Fᵉ)
        ( xᵉ)
        ( yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {𝒜ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l1ᵉ l2ᵉ}
  {ℬᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l3ᵉ l4ᵉ}
  {𝒞ᵉ : Noncoherent-Wild-Higher-Precategoryᵉ l5ᵉ l6ᵉ}
  (Gᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ ℬᵉ 𝒞ᵉ)
  (Fᵉ : colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ ℬᵉ)
  where

  comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ :
    colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ 𝒜ᵉ 𝒞ᵉ
  pr1ᵉ comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    map-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ Fᵉ
  pr2ᵉ comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ =
    is-colax-functor-comp-colax-functor-Noncoherent-Wild-Higher-Precategoryᵉ Gᵉ Fᵉ
```