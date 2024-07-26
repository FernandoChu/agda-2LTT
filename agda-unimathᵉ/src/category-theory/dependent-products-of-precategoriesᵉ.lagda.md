# Dependent products of precategories

```agda
module category-theory.dependent-products-of-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

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

Givenᵉ aᵉ familyᵉ ofᵉ [precategories](category-theory.precategories.mdᵉ) `Pᵢ`ᵉ indexedᵉ
byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Pᵢ`ᵉ isᵉ aᵉ precategoryᵉ consistingᵉ ofᵉ
dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ objectᵉ ofᵉ `Pᵢ`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ
structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Precategoryᵉ l2ᵉ l3ᵉ)
  where

  obj-Π-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  obj-Π-Precategoryᵉ = (iᵉ : Iᵉ) → obj-Precategoryᵉ (Cᵉ iᵉ)

  hom-set-Π-Precategoryᵉ : obj-Π-Precategoryᵉ → obj-Π-Precategoryᵉ → Setᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-set-Π-Precategoryᵉ xᵉ yᵉ =
    Π-Set'ᵉ Iᵉ (λ iᵉ → hom-set-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))

  hom-Π-Precategoryᵉ : obj-Π-Precategoryᵉ → obj-Π-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-Π-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Π-Precategoryᵉ xᵉ yᵉ)

  comp-hom-Π-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Π-Precategoryᵉ} →
    hom-Π-Precategoryᵉ yᵉ zᵉ →
    hom-Π-Precategoryᵉ xᵉ yᵉ →
    hom-Π-Precategoryᵉ xᵉ zᵉ
  comp-hom-Π-Precategoryᵉ fᵉ gᵉ iᵉ = comp-hom-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ)

  involutive-eq-associative-comp-hom-Π-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Π-Precategoryᵉ}
    (hᵉ : hom-Π-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Π-Precategoryᵉ (comp-hom-Π-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
    ( comp-hom-Π-Precategoryᵉ hᵉ (comp-hom-Π-Precategoryᵉ gᵉ fᵉ))
  involutive-eq-associative-comp-hom-Π-Precategoryᵉ hᵉ gᵉ fᵉ =
    involutive-eq-involutive-htpyᵉ
      ( λ iᵉ →
        involutive-eq-associative-comp-hom-Precategoryᵉ (Cᵉ iᵉ) (hᵉ iᵉ) (gᵉ iᵉ) (fᵉ iᵉ))

  associative-comp-hom-Π-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Π-Precategoryᵉ}
    (hᵉ : hom-Π-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-Π-Precategoryᵉ (comp-hom-Π-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-hom-Π-Precategoryᵉ hᵉ (comp-hom-Π-Precategoryᵉ gᵉ fᵉ))
  associative-comp-hom-Π-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ (involutive-eq-associative-comp-hom-Π-Precategoryᵉ hᵉ gᵉ fᵉ)

  associative-composition-operation-Π-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Π-Precategoryᵉ
  pr1ᵉ associative-composition-operation-Π-Precategoryᵉ = comp-hom-Π-Precategoryᵉ
  pr2ᵉ associative-composition-operation-Π-Precategoryᵉ =
    involutive-eq-associative-comp-hom-Π-Precategoryᵉ

  id-hom-Π-Precategoryᵉ : {xᵉ : obj-Π-Precategoryᵉ} → hom-Π-Precategoryᵉ xᵉ xᵉ
  id-hom-Π-Precategoryᵉ iᵉ = id-hom-Precategoryᵉ (Cᵉ iᵉ)

  left-unit-law-comp-hom-Π-Precategoryᵉ :
    {xᵉ yᵉ : obj-Π-Precategoryᵉ}
    (fᵉ : hom-Π-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Precategoryᵉ id-hom-Π-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Π-Precategoryᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-comp-hom-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))

  right-unit-law-comp-hom-Π-Precategoryᵉ :
    {xᵉ yᵉ : obj-Π-Precategoryᵉ} (fᵉ : hom-Π-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Precategoryᵉ fᵉ id-hom-Π-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Π-Precategoryᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-comp-hom-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))

  is-unital-Π-Precategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Π-Precategoryᵉ
      comp-hom-Π-Precategoryᵉ
  pr1ᵉ is-unital-Π-Precategoryᵉ xᵉ = id-hom-Π-Precategoryᵉ
  pr1ᵉ (pr2ᵉ is-unital-Π-Precategoryᵉ) = left-unit-law-comp-hom-Π-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-unital-Π-Precategoryᵉ) = right-unit-law-comp-hom-Π-Precategoryᵉ

  Π-Precategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  pr1ᵉ Π-Precategoryᵉ = obj-Π-Precategoryᵉ
  pr1ᵉ (pr2ᵉ Π-Precategoryᵉ) = hom-set-Π-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ Π-Precategoryᵉ)) =
    associative-composition-operation-Π-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ Π-Precategoryᵉ)) = is-unital-Π-Precategoryᵉ
```

## Properties

### Isomorphisms in the dependent product precategory are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Precategoryᵉ l2ᵉ l3ᵉ)
  {xᵉ yᵉ : obj-Π-Precategoryᵉ Iᵉ Cᵉ}
  where

  is-fiberwise-iso-is-iso-Π-Precategoryᵉ :
    (fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)
  pr1ᵉ (is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ) =
    hom-inv-is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) is-iso-fᵉ iᵉ
  pr1ᵉ (pr2ᵉ (is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ)) =
    htpy-eqᵉ
      ( is-section-hom-inv-is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) is-iso-fᵉ)
      ( iᵉ)
  pr2ᵉ (pr2ᵉ (is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ is-iso-fᵉ iᵉ)) =
    htpy-eqᵉ
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ
        ( Π-Precategoryᵉ Iᵉ Cᵉ)
        ( is-iso-fᵉ))
      ( iᵉ)

  fiberwise-iso-iso-Π-Precategoryᵉ :
    iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)
  pr1ᵉ (fiberwise-iso-iso-Π-Precategoryᵉ eᵉ iᵉ) =
    hom-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) eᵉ iᵉ
  pr2ᵉ (fiberwise-iso-iso-Π-Precategoryᵉ eᵉ iᵉ) =
    is-fiberwise-iso-is-iso-Π-Precategoryᵉ
      ( hom-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) eᵉ)
      ( is-iso-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) eᵉ)
      ( iᵉ)

  is-iso-is-fiberwise-iso-Π-Precategoryᵉ :
    (fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) →
    is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ
  pr1ᵉ (is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ) iᵉ =
    hom-inv-is-iso-Precategoryᵉ (Cᵉ iᵉ) (is-fiberwise-iso-fᵉ iᵉ)
  pr1ᵉ (pr2ᵉ (is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ)) =
    eq-htpyᵉ
      ( λ iᵉ →
        is-section-hom-inv-is-iso-Precategoryᵉ (Cᵉ iᵉ) (is-fiberwise-iso-fᵉ iᵉ))
  pr2ᵉ (pr2ᵉ (is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ is-fiberwise-iso-fᵉ)) =
    eq-htpyᵉ
      ( λ iᵉ →
        is-retraction-hom-inv-is-iso-Precategoryᵉ
          ( Cᵉ iᵉ)
          ( is-fiberwise-iso-fᵉ iᵉ))

  iso-fiberwise-iso-Π-Precategoryᵉ :
    ((iᵉ : Iᵉ) → iso-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  pr1ᵉ (iso-fiberwise-iso-Π-Precategoryᵉ eᵉ) iᵉ = hom-iso-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ)
  pr2ᵉ (iso-fiberwise-iso-Π-Precategoryᵉ eᵉ) =
    is-iso-is-fiberwise-iso-Π-Precategoryᵉ
      ( λ iᵉ → hom-iso-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ))
      ( λ iᵉ → is-iso-iso-Precategoryᵉ (Cᵉ iᵉ) (eᵉ iᵉ))

  is-equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ :
    (fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
      ( is-prop-Πᵉ (λ iᵉ → is-prop-is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)))
      ( is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ)

  equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ :
    (fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))
  pr1ᵉ (equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ) =
    is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ) =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ

  is-equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ :
    (fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-Πᵉ (λ iᵉ → is-prop-is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)))
      ( is-prop-is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
      ( is-fiberwise-iso-is-iso-Π-Precategoryᵉ fᵉ)

  equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ :
    ( fᵉ : hom-Π-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Precategoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
  pr1ᵉ (equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ) =
    is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ) =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ fᵉ

  is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Π-Precategoryᵉ
  is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ =
    is-equiv-is-invertibleᵉ
      ( iso-fiberwise-iso-Π-Precategoryᵉ)
      ( λ eᵉ →
        eq-htpyᵉ
          ( λ iᵉ → eq-type-subtypeᵉ (is-iso-prop-Precategoryᵉ (Cᵉ iᵉ)) reflᵉ))
      ( λ eᵉ →
        eq-type-subtypeᵉ (is-iso-prop-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ)) reflᵉ)

  equiv-fiberwise-iso-iso-Π-Precategoryᵉ :
    ( iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))
  pr1ᵉ equiv-fiberwise-iso-iso-Π-Precategoryᵉ =
    fiberwise-iso-iso-Π-Precategoryᵉ
  pr2ᵉ equiv-fiberwise-iso-iso-Π-Precategoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ

  is-equiv-iso-fiberwise-iso-Π-Precategoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Π-Precategoryᵉ
  is-equiv-iso-fiberwise-iso-Π-Precategoryᵉ =
    is-equiv-map-inv-is-equivᵉ is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ

  equiv-iso-fiberwise-iso-Π-Precategoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Precategoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Precategoryᵉ (Π-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  pr1ᵉ equiv-iso-fiberwise-iso-Π-Precategoryᵉ =
    iso-fiberwise-iso-Π-Precategoryᵉ
  pr2ᵉ equiv-iso-fiberwise-iso-Π-Precategoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Precategoryᵉ
```