# Natural transformations between functors between large precategories

```agda
module category-theory.natural-transformations-functors-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategoriesᵉ
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ [largeᵉ precategories](category-theory.large-precategories.mdᵉ) `C`ᵉ andᵉ `D`,ᵉ
aᵉ **naturalᵉ transformation**ᵉ fromᵉ aᵉ
[functor](category-theory.functors-large-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to
`Gᵉ : Cᵉ → D`ᵉ consistsᵉ ofᵉ :

-ᵉ aᵉ familyᵉ ofᵉ morphismsᵉ `γᵉ : (xᵉ : Cᵉ) → homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identityᵉ holdsᵉ:
-ᵉ `(Gᵉ fᵉ) ∘ᵉ (γᵉ xᵉ) = (γᵉ yᵉ) ∘ᵉ (Fᵉ f)`,ᵉ forᵉ allᵉ `fᵉ : homᵉ xᵉ y`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ)
  where

  family-of-morphisms-functor-Large-Precategoryᵉ : UUωᵉ
  family-of-morphisms-functor-Large-Precategoryᵉ =
    {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ)
      ( obj-functor-Large-Precategoryᵉ Gᵉ Xᵉ)

  naturality-family-of-morphisms-functor-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ → UUωᵉ
  naturality-family-of-morphisms-functor-Large-Precategoryᵉ τᵉ =
    {l1ᵉ l2ᵉ : Level} {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
    {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
    (fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
    coherence-square-hom-Large-Precategoryᵉ Dᵉ
      ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ)
      ( τᵉ Xᵉ)
      ( τᵉ Yᵉ)
      ( hom-functor-Large-Precategoryᵉ Gᵉ fᵉ)

  record natural-transformation-Large-Precategoryᵉ : UUωᵉ
    where
    constructor make-natural-transformationᵉ
    field
      hom-natural-transformation-Large-Precategoryᵉ :
        family-of-morphisms-functor-Large-Precategoryᵉ
      naturality-natural-transformation-Large-Precategoryᵉ :
        naturality-family-of-morphisms-functor-Large-Precategoryᵉ
          hom-natural-transformation-Large-Precategoryᵉ

  open natural-transformation-Large-Precategoryᵉ public
```

## Properties

### The identity natural transformation

Everyᵉ functorᵉ comesᵉ equippedᵉ with anᵉ identityᵉ naturalᵉ transformation.ᵉ

```agda
module _
  { αCᵉ αDᵉ γFᵉ : Level → Level}
  { βCᵉ βDᵉ : Level → Level → Level}
  ( Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  ( Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  ( Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  where

  hom-id-natural-transformation-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  hom-id-natural-transformation-Large-Precategoryᵉ Xᵉ =
    id-hom-Large-Precategoryᵉ Dᵉ

  naturality-id-natural-transformation-Large-Precategoryᵉ :
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
      hom-id-natural-transformation-Large-Precategoryᵉ
  naturality-id-natural-transformation-Large-Precategoryᵉ fᵉ =
    ( right-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ)))

  id-natural-transformation-Large-Precategoryᵉ :
    natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  hom-natural-transformation-Large-Precategoryᵉ
    id-natural-transformation-Large-Precategoryᵉ =
    hom-id-natural-transformation-Large-Precategoryᵉ
  naturality-natural-transformation-Large-Precategoryᵉ
    id-natural-transformation-Large-Precategoryᵉ =
    naturality-id-natural-transformation-Large-Precategoryᵉ
```

### Composition of natural transformations

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ γHᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ)
  (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ)
  (Hᵉ : functor-Large-Precategoryᵉ γHᵉ Cᵉ Dᵉ)
  (τᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (σᵉ : natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-comp-natural-transformation-Large-Precategoryᵉ :
    family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-comp-natural-transformation-Large-Precategoryᵉ Xᵉ =
    comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Xᵉ)
      ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Xᵉ)

  naturality-comp-natural-transformation-Large-Precategoryᵉ :
    naturality-family-of-morphisms-functor-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      hom-comp-natural-transformation-Large-Precategoryᵉ
  naturality-comp-natural-transformation-Large-Precategoryᵉ {Xᵉ = Xᵉ} {Yᵉ} fᵉ =
    invᵉ
      ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-functor-Large-Precategoryᵉ Hᵉ fᵉ)
        ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Xᵉ)
        ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Xᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategory'ᵉ Dᵉ
        ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Xᵉ))
      ( naturality-natural-transformation-Large-Precategoryᵉ τᵉ fᵉ)) ∙ᵉ
    ( associative-comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Yᵉ)
      ( hom-functor-Large-Precategoryᵉ Gᵉ fᵉ)
      ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Xᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Yᵉ))
      ( naturality-natural-transformation-Large-Precategoryᵉ σᵉ fᵉ)) ∙ᵉ
    ( invᵉ
      (associative-comp-hom-Large-Precategoryᵉ Dᵉ
        ( hom-natural-transformation-Large-Precategoryᵉ τᵉ Yᵉ)
        ( hom-natural-transformation-Large-Precategoryᵉ σᵉ Yᵉ)
        ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ)))

  comp-natural-transformation-Large-Precategoryᵉ :
    natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-natural-transformation-Large-Precategoryᵉ
    comp-natural-transformation-Large-Precategoryᵉ =
    hom-comp-natural-transformation-Large-Precategoryᵉ
  naturality-natural-transformation-Large-Precategoryᵉ
    comp-natural-transformation-Large-Precategoryᵉ =
    naturality-comp-natural-transformation-Large-Precategoryᵉ
```

## See also

-ᵉ [Homotopiesᵉ ofᵉ naturalᵉ transformationsᵉ in largeᵉ precategories](category-theory.homotopies-natural-transformations-large-precategories.mdᵉ)