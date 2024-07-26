# Dependent products of large categories

```agda
module category-theory.dependent-products-of-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.dependent-products-of-large-precategoriesᵉ
open import category-theory.isomorphisms-in-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [largeᵉ categories](category-theory.large-categories.mdᵉ) `Cᵢ`ᵉ
indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ `Π(iᵉ : I),ᵉ Cᵢ`ᵉ isᵉ aᵉ largeᵉ categoryᵉ
consistingᵉ ofᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ objectᵉ ofᵉ `Cᵢ`.ᵉ Everyᵉ componentᵉ ofᵉ
theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Large-Categoryᵉ αᵉ βᵉ)
  where

  large-precategory-Π-Large-Categoryᵉ :
    Large-Precategoryᵉ (λ l2ᵉ → l1ᵉ ⊔ αᵉ l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  large-precategory-Π-Large-Categoryᵉ =
    Π-Large-Precategoryᵉ Iᵉ (λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  abstract
    is-large-category-Π-Large-Categoryᵉ :
      is-large-category-Large-Precategoryᵉ large-precategory-Π-Large-Categoryᵉ
    is-large-category-Π-Large-Categoryᵉ xᵉ yᵉ =
      is-equiv-htpy-equivᵉ
        ( ( equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
            ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))) ∘eᵉ
          ( equiv-Π-equiv-familyᵉ
            ( λ iᵉ → extensionality-obj-Large-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))) ∘eᵉ
          ( equiv-funextᵉ))
        ( λ where reflᵉ → reflᵉ)

  Π-Large-Categoryᵉ : Large-Categoryᵉ (λ l2ᵉ → l1ᵉ ⊔ αᵉ l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  large-precategory-Large-Categoryᵉ
    Π-Large-Categoryᵉ =
    large-precategory-Π-Large-Categoryᵉ
  is-large-category-Large-Categoryᵉ Π-Large-Categoryᵉ =
    is-large-category-Π-Large-Categoryᵉ

  obj-Π-Large-Categoryᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ αᵉ l2ᵉ)
  obj-Π-Large-Categoryᵉ = obj-Large-Categoryᵉ Π-Large-Categoryᵉ

  hom-set-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Π-Large-Categoryᵉ l2ᵉ → obj-Π-Large-Categoryᵉ l3ᵉ → Setᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-set-Π-Large-Categoryᵉ = hom-set-Large-Categoryᵉ Π-Large-Categoryᵉ

  hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} →
    obj-Π-Large-Categoryᵉ l2ᵉ → obj-Π-Large-Categoryᵉ l3ᵉ → UUᵉ (l1ᵉ ⊔ βᵉ l2ᵉ l3ᵉ)
  hom-Π-Large-Categoryᵉ = hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  comp-hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Categoryᵉ l4ᵉ} →
    hom-Π-Large-Categoryᵉ yᵉ zᵉ →
    hom-Π-Large-Categoryᵉ xᵉ yᵉ →
    hom-Π-Large-Categoryᵉ xᵉ zᵉ
  comp-hom-Π-Large-Categoryᵉ = comp-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  associative-comp-hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Categoryᵉ l4ᵉ}
    {wᵉ : obj-Π-Large-Categoryᵉ l5ᵉ} →
    (hᵉ : hom-Π-Large-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Large-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Large-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Categoryᵉ (comp-hom-Π-Large-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Π-Large-Categoryᵉ hᵉ (comp-hom-Π-Large-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Π-Large-Categoryᵉ =
    associative-comp-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  involutive-eq-associative-comp-hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
    {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ}
    {yᵉ : obj-Π-Large-Categoryᵉ l3ᵉ}
    {zᵉ : obj-Π-Large-Categoryᵉ l4ᵉ}
    {wᵉ : obj-Π-Large-Categoryᵉ l5ᵉ} →
    (hᵉ : hom-Π-Large-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Large-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Large-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Categoryᵉ (comp-hom-Π-Large-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Π-Large-Categoryᵉ hᵉ (comp-hom-Π-Large-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Π-Large-Categoryᵉ =
    involutive-eq-associative-comp-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  id-hom-Π-Large-Categoryᵉ :
    {l2ᵉ : Level} {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ} →
    hom-Π-Large-Categoryᵉ xᵉ xᵉ
  id-hom-Π-Large-Categoryᵉ = id-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  left-unit-law-comp-hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ} {yᵉ : obj-Π-Large-Categoryᵉ l3ᵉ}
    (fᵉ : hom-Π-Large-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Categoryᵉ id-hom-Π-Large-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Π-Large-Categoryᵉ =
    left-unit-law-comp-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  right-unit-law-comp-hom-Π-Large-Categoryᵉ :
    {l2ᵉ l3ᵉ : Level} {xᵉ : obj-Π-Large-Categoryᵉ l2ᵉ} {yᵉ : obj-Π-Large-Categoryᵉ l3ᵉ}
    (fᵉ : hom-Π-Large-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Large-Categoryᵉ fᵉ id-hom-Π-Large-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Π-Large-Categoryᵉ =
    right-unit-law-comp-hom-Large-Categoryᵉ Π-Large-Categoryᵉ

  extensionality-obj-Π-Large-Categoryᵉ :
    {l2ᵉ : Level} (xᵉ yᵉ : obj-Π-Large-Categoryᵉ l2ᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ iso-Large-Categoryᵉ Π-Large-Categoryᵉ xᵉ yᵉ
  extensionality-obj-Π-Large-Categoryᵉ =
    extensionality-obj-Large-Categoryᵉ Π-Large-Categoryᵉ
```

## Properties

### Isomorphisms in the large dependent product category are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Large-Categoryᵉ αᵉ βᵉ)
  {xᵉ : obj-Π-Large-Categoryᵉ Iᵉ Cᵉ l2ᵉ} {yᵉ : obj-Π-Large-Categoryᵉ Iᵉ Cᵉ l3ᵉ}
  where

  is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ :
    (fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ =
    is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  fiberwise-iso-iso-Π-Large-Categoryᵉ :
    iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Large-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-Π-Large-Categoryᵉ =
    fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ :
    (fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) →
    is-iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ =
    is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  iso-fiberwise-iso-Π-Large-Categoryᵉ :
    ((iᵉ : Iᵉ) → iso-Large-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-fiberwise-iso-Π-Large-Categoryᵉ =
    iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ :
    (fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ :
    (fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-Π-Large-Categoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ :
    (fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ :
    ( fᵉ : hom-Π-Large-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Large-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-is-fiberwise-iso-Π-Large-Categoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  is-equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Π-Large-Categoryᵉ
  is-equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ :
    ( iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Large-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-Π-Large-Categoryᵉ =
    equiv-fiberwise-iso-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  is-equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Π-Large-Categoryᵉ
  is-equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))

  equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Large-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Large-Categoryᵉ (Π-Large-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-fiberwise-iso-Π-Large-Categoryᵉ =
    equiv-iso-fiberwise-iso-Π-Large-Precategoryᵉ Iᵉ
      ( λ iᵉ → large-precategory-Large-Categoryᵉ (Cᵉ iᵉ))
```