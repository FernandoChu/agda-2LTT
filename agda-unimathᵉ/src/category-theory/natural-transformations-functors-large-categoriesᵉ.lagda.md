# Natural transformations between functors between large categories

```agda
module category-theory.natural-transformations-functors-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ [largeᵉ categories](category-theory.large-categories.mdᵉ) `C`ᵉ andᵉ `D`,ᵉ aᵉ
**naturalᵉ transformation**ᵉ fromᵉ aᵉ
[functor](category-theory.functors-large-categories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to
`Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `γᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  **naturalityᵉ condition**ᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (γᵉ xᵉ) = (γᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Categoryᵉ γGᵉ Cᵉ Dᵉ)
  where

  family-of-morphisms-functor-Large-Categoryᵉ : UUωᵉ
  family-of-morphisms-functor-Large-Categoryᵉ =
    family-of-morphisms-functor-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  naturality-family-of-morphisms-functor-Large-Categoryᵉ :
    family-of-morphisms-functor-Large-Categoryᵉ → UUωᵉ
  naturality-family-of-morphisms-functor-Large-Categoryᵉ =
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-transformation-Large-Categoryᵉ : UUωᵉ
  natural-transformation-Large-Categoryᵉ =
    natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  hom-natural-transformation-Large-Categoryᵉ :
    natural-transformation-Large-Categoryᵉ →
    family-of-morphisms-functor-Large-Categoryᵉ
  hom-natural-transformation-Large-Categoryᵉ =
    hom-natural-transformation-Large-Precategoryᵉ

  naturality-natural-transformation-Large-Categoryᵉ :
    (τᵉ : natural-transformation-Large-Categoryᵉ) →
    naturality-family-of-morphisms-functor-Large-Categoryᵉ
      (hom-natural-transformation-Large-Categoryᵉ τᵉ)
  naturality-natural-transformation-Large-Categoryᵉ =
    naturality-natural-transformation-Large-Precategoryᵉ
```

## Properties

### The identity natural transformation

Everyᵉ functorᵉ comesᵉ equippedᵉ with anᵉ identityᵉ naturalᵉ transformation.ᵉ

```agda
module _
  { αCᵉ αDᵉ γFᵉ : Level → Level}
  { βCᵉ βDᵉ : Level → Level → Level}
  ( Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  ( Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  ( Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  where

  hom-id-natural-transformation-Large-Categoryᵉ :
    family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  hom-id-natural-transformation-Large-Categoryᵉ =
    hom-id-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  naturality-id-natural-transformation-Large-Categoryᵉ :
    naturality-family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
      hom-id-natural-transformation-Large-Categoryᵉ
  naturality-id-natural-transformation-Large-Categoryᵉ =
    naturality-id-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  id-natural-transformation-Large-Categoryᵉ :
    natural-transformation-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-Large-Categoryᵉ =
    id-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### Composition of natural transformations

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ γHᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Categoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Categoryᵉ γGᵉ Cᵉ Dᵉ)
  (Hᵉ : functor-Large-Categoryᵉ γHᵉ Cᵉ Dᵉ)
  (τᵉ : natural-transformation-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (σᵉ : natural-transformation-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-comp-natural-transformation-Large-Categoryᵉ :
    family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-comp-natural-transformation-Large-Categoryᵉ =
    hom-comp-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( Hᵉ)
      ( τᵉ)
      ( σᵉ)

  naturality-comp-natural-transformation-Large-Categoryᵉ :
    naturality-family-of-morphisms-functor-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      hom-comp-natural-transformation-Large-Categoryᵉ
  naturality-comp-natural-transformation-Large-Categoryᵉ =
    naturality-comp-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( Hᵉ)
      ( τᵉ)
      ( σᵉ)

  comp-natural-transformation-Large-Categoryᵉ :
    natural-transformation-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-Large-Categoryᵉ =
    comp-natural-transformation-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( Hᵉ)
      ( τᵉ)
      ( σᵉ)
```