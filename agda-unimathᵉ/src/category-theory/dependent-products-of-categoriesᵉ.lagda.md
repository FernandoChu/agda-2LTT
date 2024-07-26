# Dependent products of categories

```agda
module category-theory.dependent-products-of-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.dependent-products-of-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ [categories](category-theory.categories.mdᵉ) `Cᵢ`ᵉ indexedᵉ byᵉ
`iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ typeᵉ `Π(iᵉ : I),ᵉ Cᵢ`ᵉ isᵉ aᵉ categoryᵉ consistingᵉ ofᵉ
functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ objectᵉ ofᵉ `Cᵢ`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ
isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Categoryᵉ l2ᵉ l3ᵉ)
  where

  precategory-Π-Categoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  precategory-Π-Categoryᵉ = Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  abstract
    is-category-Π-Categoryᵉ :
      is-category-Precategoryᵉ precategory-Π-Categoryᵉ
    is-category-Π-Categoryᵉ xᵉ yᵉ =
      is-equiv-htpy-equivᵉ
        ( equiv-iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ) ∘eᵉ
          equiv-Π-equiv-familyᵉ
            ( λ iᵉ → extensionality-obj-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) ∘eᵉ
          equiv-funextᵉ)
        ( λ where reflᵉ → reflᵉ)

  Π-Categoryᵉ : Categoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  pr1ᵉ Π-Categoryᵉ = Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)
  pr2ᵉ Π-Categoryᵉ = is-category-Π-Categoryᵉ

  obj-Π-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  obj-Π-Categoryᵉ = obj-Categoryᵉ Π-Categoryᵉ

  hom-set-Π-Categoryᵉ :
    obj-Π-Categoryᵉ → obj-Π-Categoryᵉ → Setᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-set-Π-Categoryᵉ = hom-set-Categoryᵉ Π-Categoryᵉ

  hom-Π-Categoryᵉ :
    obj-Π-Categoryᵉ → obj-Π-Categoryᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-Π-Categoryᵉ = hom-Categoryᵉ Π-Categoryᵉ

  comp-hom-Π-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Π-Categoryᵉ} →
    hom-Π-Categoryᵉ yᵉ zᵉ →
    hom-Π-Categoryᵉ xᵉ yᵉ →
    hom-Π-Categoryᵉ xᵉ zᵉ
  comp-hom-Π-Categoryᵉ = comp-hom-Categoryᵉ Π-Categoryᵉ

  involutive-eq-associative-comp-hom-Π-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Π-Categoryᵉ}
    (hᵉ : hom-Π-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Categoryᵉ (comp-hom-Π-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Π-Categoryᵉ hᵉ (comp-hom-Π-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Π-Categoryᵉ =
    involutive-eq-associative-comp-hom-Categoryᵉ Π-Categoryᵉ

  associative-comp-hom-Π-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Π-Categoryᵉ}
    (hᵉ : hom-Π-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Π-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Π-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Categoryᵉ (comp-hom-Π-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Π-Categoryᵉ hᵉ (comp-hom-Π-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-Π-Categoryᵉ =
    associative-comp-hom-Categoryᵉ Π-Categoryᵉ

  associative-composition-operation-Π-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Π-Categoryᵉ
  associative-composition-operation-Π-Categoryᵉ =
    associative-composition-operation-Categoryᵉ Π-Categoryᵉ

  id-hom-Π-Categoryᵉ :
    {xᵉ : obj-Π-Categoryᵉ} → hom-Π-Categoryᵉ xᵉ xᵉ
  id-hom-Π-Categoryᵉ = id-hom-Categoryᵉ Π-Categoryᵉ

  left-unit-law-comp-hom-Π-Categoryᵉ :
    {xᵉ yᵉ : obj-Π-Categoryᵉ}
    (fᵉ : hom-Π-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Categoryᵉ id-hom-Π-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Π-Categoryᵉ =
    left-unit-law-comp-hom-Categoryᵉ Π-Categoryᵉ

  right-unit-law-comp-hom-Π-Categoryᵉ :
    {xᵉ yᵉ : obj-Π-Categoryᵉ} (fᵉ : hom-Π-Categoryᵉ xᵉ yᵉ) →
    comp-hom-Π-Categoryᵉ fᵉ id-hom-Π-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-Π-Categoryᵉ =
    right-unit-law-comp-hom-Categoryᵉ Π-Categoryᵉ

  is-unital-Π-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-Π-Categoryᵉ
      comp-hom-Π-Categoryᵉ
  is-unital-Π-Categoryᵉ = is-unital-composition-operation-Categoryᵉ Π-Categoryᵉ

  extensionality-obj-Π-Categoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Π-Categoryᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ iso-Categoryᵉ Π-Categoryᵉ xᵉ yᵉ
  extensionality-obj-Π-Categoryᵉ = extensionality-obj-Categoryᵉ Π-Categoryᵉ
```

## Properties

### Isomorphisms in the dependent product category are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Iᵉ → Categoryᵉ l2ᵉ l3ᵉ)
  {xᵉ yᵉ : obj-Π-Categoryᵉ Iᵉ Cᵉ}
  where

  is-fiberwise-iso-is-iso-Π-Categoryᵉ :
    (fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-Π-Categoryᵉ =
    is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  fiberwise-iso-iso-Π-Categoryᵉ :
    iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-Π-Categoryᵉ =
    fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  is-iso-is-fiberwise-iso-Π-Categoryᵉ :
    (fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) →
    is-iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-is-fiberwise-iso-Π-Categoryᵉ =
    is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  iso-fiberwise-iso-Π-Categoryᵉ :
    ((iᵉ : Iᵉ) → iso-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-fiberwise-iso-Π-Categoryᵉ =
    iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  is-equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ :
    (fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-Π-Categoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ :
    (fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  is-equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ :
    (fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-is-fiberwise-iso-Π-Categoryᵉ fᵉ)
  is-equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ :
    ( fᵉ : hom-Π-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Categoryᵉ (Cᵉ iᵉ) (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  is-equiv-fiberwise-iso-iso-Π-Categoryᵉ :
    is-equivᵉ fiberwise-iso-iso-Π-Categoryᵉ
  is-equiv-fiberwise-iso-iso-Π-Categoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  equiv-fiberwise-iso-iso-Π-Categoryᵉ :
    ( iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-Π-Categoryᵉ =
    equiv-fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  is-equiv-iso-fiberwise-iso-Π-Categoryᵉ :
    is-equivᵉ iso-fiberwise-iso-Π-Categoryᵉ
  is-equiv-iso-fiberwise-iso-Π-Categoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)

  equiv-iso-fiberwise-iso-Π-Categoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Categoryᵉ (Cᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Categoryᵉ (Π-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-fiberwise-iso-Π-Categoryᵉ =
    equiv-iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (precategory-Categoryᵉ ∘ᵉ Cᵉ)
```