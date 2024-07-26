# Dependent products of large precategories

```agda
module category-theory.dependent-products-of-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [largeᵉ precategories](category-theory.large-precategories.mdᵉ)
`Pᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Pᵢ`ᵉ isᵉ aᵉ largeᵉ
precategoryᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ objectᵉ ofᵉ
`Pᵢ`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Large-Precategoryᵉ αᵉ βᵉ)
  where

  obj-Π-Large-Precategoryᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ αᵉ l2ᵉ)
  obj-Π-Large-Precategoryᵉ l2ᵉ = (iᵉ : Iᵉ) → obj-Large-Precategoryᵉ (Cᵉ iᵉ) l2ᵉ

  hom-set-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Π-Large-Precategoryᵉ l2ᵉ → obj-Π-Large-Precategoryᵉ l3ᵉ → Setᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-set-Π-Large-Precategoryᵉ xᵉ yᵉ =
    Π-Set'ᵉ Iᵉ (λ iᵉ → hom-set-Large-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))

  hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Π-Large-Precategoryᵉ l2ᵉ → obj-Π-Large-Precategoryᵉ l3ᵉ → UUᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-Π-Large-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Π-Large-Precategoryᵉ xᵉ yᵉ)

  comp-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Precategoryᵉ l4ᵉ} →
    hom-Π-Large-Precategoryᵉ yᵉ zᵉ →
    hom-Π-Large-Precategoryᵉ xᵉ yᵉ →
    hom-Π-Large-Precategoryᵉ xᵉ zᵉ
  comp-hom-Π-Large-Precategoryᵉ fᵉ gᵉ iᵉ =
    comp-hom-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ)

  involutive-eq-associative-comp-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Precategoryᵉ l4ᵉ}
    {wᵉ : obj-Π-Large-Precategoryᵉ l5ᵉ} →
    (hᵉ : hom-Π-Large-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Large-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Large-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Π-Large-Precategoryᵉ (comp-hom-Π-Large-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
    ( comp-hom-Π-Large-Precategoryᵉ hᵉ (comp-hom-Π-Large-Precategoryᵉ gᵉ fᵉ))
  involutive-eq-associative-comp-hom-Π-Large-Precategoryᵉ hᵉ gᵉ fᵉ =
    involutive-eq-involutive-htpyᵉ
      ( λ iᵉ →
        involutive-eq-associative-comp-hom-Large-Precategoryᵉ
          ( Cᵉ iᵉ)
          ( hᵉ iᵉ)
          ( gᵉ iᵉ)
          ( fᵉ iᵉ))

  associative-comp-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Precategoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Precategoryᵉ l4ᵉ}
    {wᵉ : obj-Π-Large-Precategoryᵉ l5ᵉ} →
    (hᵉ : hom-Π-Large-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Large-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Large-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Π-Large-Precategoryᵉ (comp-hom-Π-Large-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-hom-Π-Large-Precategoryᵉ hᵉ (comp-hom-Π-Large-Precategoryᵉ gᵉ fᵉ))
  associative-comp-hom-Π-Large-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( involutive-eq-associative-comp-hom-Π-Large-Precategoryᵉ hᵉ gᵉ fᵉ)

  id-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ : Level} {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ} → hom-Π-Large-Precategoryᵉ xᵉ xᵉ
  id-hom-Π-Large-Precategoryᵉ iᵉ = id-hom-Large-Precategoryᵉ (Cᵉ iᵉ)

  left-unit-law-comp-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Precategoryᵉ l3ᵉ}
    (fᵉ : hom-Π-Large-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Precategoryᵉ id-hom-Π-Large-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Π-Large-Precategoryᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-comp-hom-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))

  right-unit-law-comp-hom-Π-Large-Precategoryᵉ :
    {l2ᵉ l3ᵉ : Level}
    {xᵉ : obj-Π-Large-Precategoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Precategoryᵉ l3ᵉ}
    (fᵉ : hom-Π-Large-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Precategoryᵉ fᵉ id-hom-Π-Large-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Π-Large-Precategoryᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-comp-hom-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))

  Π-Large-Precategoryᵉ :
    Large-Precategoryᵉ (λ l2ᵉ → l1ᵉ ⊔ αᵉ l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  obj-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    obj-Π-Large-Precategoryᵉ
  hom-set-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    hom-set-Π-Large-Precategoryᵉ
  comp-hom-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    comp-hom-Π-Large-Precategoryᵉ
  id-hom-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    id-hom-Π-Large-Precategoryᵉ
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    involutive-eq-associative-comp-hom-Π-Large-Precategoryᵉ
  left-unit-law-comp-hom-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    left-unit-law-comp-hom-Π-Large-Precategoryᵉ
  right-unit-law-comp-hom-Large-Precategoryᵉ Π-Large-Precategoryᵉ =
    right-unit-law-comp-hom-Π-Large-Precategoryᵉ
```

## Properties

### Isomorphisms in the large dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Large-Precategoryᵉ αᵉ βᵉ)
  {xᵉ : obj-Π-Large-Precategoryᵉ Iᵉ Cᵉ l2ᵉ}
  {yᵉ : obj-Π-Large-Precategoryᵉ Iᵉ Cᵉ l3ᵉ}
  where

  is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ :
    (fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)
  pr1ᵉ (is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ) =
    hom-inv-is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ is-iso-fᵉ iᵉ
  pr1ᵉ (pr2ᵉ (is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ)) =
    htpy-eqᵉ
      ( is-section-hom-inv-is-iso-Large-Precategoryᵉ
        ( Π-Large-Precategoryᵉ Iᵉ Cᵉ)
        ( fᵉ)
        ( is-iso-fᵉ))
      ( iᵉ)
  pr2ᵉ (pr2ᵉ (is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ)) =
    htpy-eqᵉ
      ( is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
        ( Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ
        ( is-iso-fᵉ))
      ( iᵉ)

  fiberwise-iso-iso-Π-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)
  pr1ᵉ (fiberwise-iso-iso-Π-Large-Precategoryᵉ eᵉ iᵉ) =
    hom-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) eᵉ iᵉ
  pr2ᵉ (fiberwise-iso-iso-Π-Large-Precategoryᵉ eᵉ iᵉ) =
    is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ
      ( hom-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) eᵉ)
      ( is-iso-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) eᵉ)
      ( iᵉ)

  is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ :
    (fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) →
    is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ
  pr1ᵉ (is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ) iᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ) (is-fiberwise-iso-fᵉ iᵉ)
  pr1ᵉ (pr2ᵉ (is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ)) =
    eq-htpyᵉ
      ( λ iᵉ →
        is-section-hom-inv-is-iso-Large-Precategoryᵉ
          ( Cᵉ iᵉ)
          ( fᵉ iᵉ)
          ( is-fiberwise-iso-fᵉ iᵉ))
  pr2ᵉ (pr2ᵉ (is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ)) =
    eq-htpyᵉ
      ( λ iᵉ →
        is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
          ( Cᵉ iᵉ)
          (fᵉ iᵉ) ( is-fiberwise-iso-fᵉ iᵉ))

  iso-fiberwise-iso-Π-Large-Precategoryᵉ :
    ((iᵉ : Iᵉ) → iso-Large-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  pr1ᵉ (iso-fiberwise-iso-Π-Large-Precategoryᵉ eᵉ) iᵉ =
    hom-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ)
  pr2ᵉ (iso-fiberwise-iso-Π-Large-Precategoryᵉ eᵉ) =
    is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ
      ( λ iᵉ → hom-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ))
      ( λ iᵉ → is-iso-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ))

  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ :
    (fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
      ( is-prop-Πᵉ (λ iᵉ → is-prop-is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)))
      ( is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ)

  equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ :
    (fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))
  pr1ᵉ (equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ) =
    is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ) =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ

  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ :
    (fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-Πᵉ (λ iᵉ → is-prop-is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)))
      ( is-prop-is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
      ( is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ fᵉ)

  equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ :
    ( fᵉ : hom-Π-Large-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Large-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
  pr1ᵉ (equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ) =
    is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ) =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ fᵉ

  is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Π-Large-Precategoryᵉ
  is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( iso-fiberwise-iso-Π-Large-Precategoryᵉ)
      ( λ eᵉ →
        eq-htpyᵉ
          ( λ iᵉ → eq-type-subtypeᵉ (is-iso-prop-Large-Precategoryᵉ (Cᵉ iᵉ)) reflᵉ))
      ( λ eᵉ →
        eq-type-subtypeᵉ
          ( is-iso-prop-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ))
          ( reflᵉ))

  equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ :
    ( iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))
  pr1ᵉ equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ =
    fiberwise-iso-iso-Π-Large-Precategoryᵉ
  pr2ᵉ equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ

  is-equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Π-Large-Precategoryᵉ
  is-equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ =
    is-equiv-map-inv-is-equivᵉ is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ

  equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Large-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Large-Precategoryᵉ (Π-Large-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  pr1ᵉ equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ =
    iso-fiberwise-iso-Π-Large-Precategoryᵉ
  pr2ᵉ equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ
```