# Natural isomorphisms between functors between large precategories

```agda
module category-theory.natural-isomorphisms-functors-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-large-precategoriesᵉ
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.natural-transformations-functors-large-precategoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **naturalᵉ isomorphism**ᵉ `γ`ᵉ fromᵉ
[functor](category-theory.functors-large-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to
`Gᵉ : Cᵉ → D`ᵉ isᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-large-precategories.mdᵉ)
fromᵉ `F`ᵉ to `G`ᵉ suchᵉ thatᵉ theᵉ morphismᵉ `γᵉ xᵉ : homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ isᵉ anᵉ
[isomorphism](category-theory.isomorphisms-in-precategories.md),ᵉ forᵉ everyᵉ
objectᵉ `x`ᵉ in `C`.ᵉ

## Definition

```agda
module _
  {αCᵉ αDᵉ γFᵉ γGᵉ : Level → Level}
  {βCᵉ βDᵉ : Level → Level → Level}
  {Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ}
  {Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ}
  (Fᵉ : functor-Large-Precategoryᵉ γFᵉ Cᵉ Dᵉ)
  (Gᵉ : functor-Large-Precategoryᵉ γGᵉ Cᵉ Dᵉ)
  where

  iso-family-functor-Large-Precategoryᵉ : UUωᵉ
  iso-family-functor-Large-Precategoryᵉ =
    { lᵉ : Level}
    ( Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
    iso-Large-Precategoryᵉ Dᵉ
      ( obj-functor-Large-Precategoryᵉ Fᵉ Xᵉ)
      ( obj-functor-Large-Precategoryᵉ Gᵉ Xᵉ)

  record natural-isomorphism-Large-Precategoryᵉ : UUωᵉ
    where
    constructor make-natural-isomorphismᵉ
    field
      iso-natural-isomorphism-Large-Precategoryᵉ :
        iso-family-functor-Large-Precategoryᵉ
      naturality-natural-isomorphism-Large-Precategoryᵉ :
        { l1ᵉ l2ᵉ : Level}
        { Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
        { Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
        ( fᵉ : hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ) →
        coherence-square-hom-Large-Precategoryᵉ Dᵉ
          ( hom-functor-Large-Precategoryᵉ Fᵉ fᵉ)
          ( hom-iso-Large-Precategoryᵉ Dᵉ
            ( iso-natural-isomorphism-Large-Precategoryᵉ Xᵉ))
          ( hom-iso-Large-Precategoryᵉ Dᵉ
            ( iso-natural-isomorphism-Large-Precategoryᵉ Yᵉ))
          ( hom-functor-Large-Precategoryᵉ Gᵉ fᵉ)

  open natural-isomorphism-Large-Precategoryᵉ public

  natural-transformation-natural-isomorphism-Large-Precategoryᵉ :
    natural-isomorphism-Large-Precategoryᵉ →
    natural-transformation-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  hom-natural-transformation-Large-Precategoryᵉ
    ( natural-transformation-natural-isomorphism-Large-Precategoryᵉ γᵉ) Xᵉ =
    hom-iso-Large-Precategoryᵉ Dᵉ
      ( iso-natural-isomorphism-Large-Precategoryᵉ γᵉ Xᵉ)
  naturality-natural-transformation-Large-Precategoryᵉ
    ( natural-transformation-natural-isomorphism-Large-Precategoryᵉ γᵉ) =
      naturality-natural-isomorphism-Large-Precategoryᵉ γᵉ
```