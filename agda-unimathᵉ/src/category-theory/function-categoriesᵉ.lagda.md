# Function categories

```agda
module category-theory.function-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.dependent-products-of-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ andᵉ anyᵉ typeᵉ `I`,ᵉ theᵉ
functionᵉ typeᵉ `Iᵉ → C`ᵉ isᵉ aᵉ categoryᵉ consistingᵉ ofᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ
objectᵉ ofᵉ `C`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Categoryᵉ l2ᵉ l3ᵉ)
  where

  function-Categoryᵉ : Categoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  function-Categoryᵉ = Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  precategory-function-Categoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  precategory-function-Categoryᵉ = precategory-Categoryᵉ function-Categoryᵉ

  is-category-function-Categoryᵉ :
    is-category-Precategoryᵉ precategory-function-Categoryᵉ
  is-category-function-Categoryᵉ =
    is-category-Categoryᵉ function-Categoryᵉ

  obj-function-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  obj-function-Categoryᵉ = obj-Categoryᵉ function-Categoryᵉ

  hom-set-function-Categoryᵉ :
    obj-function-Categoryᵉ → obj-function-Categoryᵉ → Setᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-set-function-Categoryᵉ = hom-set-Categoryᵉ function-Categoryᵉ

  hom-function-Categoryᵉ :
    obj-function-Categoryᵉ → obj-function-Categoryᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-function-Categoryᵉ = hom-Categoryᵉ function-Categoryᵉ

  comp-hom-function-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-function-Categoryᵉ} →
    hom-function-Categoryᵉ yᵉ zᵉ →
    hom-function-Categoryᵉ xᵉ yᵉ →
    hom-function-Categoryᵉ xᵉ zᵉ
  comp-hom-function-Categoryᵉ = comp-hom-Categoryᵉ function-Categoryᵉ

  associative-comp-hom-function-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-function-Categoryᵉ}
    (hᵉ : hom-function-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-function-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-function-Categoryᵉ (comp-hom-function-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-function-Categoryᵉ hᵉ (comp-hom-function-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-function-Categoryᵉ =
    associative-comp-hom-Categoryᵉ function-Categoryᵉ

  involutive-eq-associative-comp-hom-function-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-function-Categoryᵉ}
    (hᵉ : hom-function-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-function-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-function-Categoryᵉ (comp-hom-function-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-function-Categoryᵉ hᵉ (comp-hom-function-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-function-Categoryᵉ =
    involutive-eq-associative-comp-hom-Categoryᵉ function-Categoryᵉ

  associative-composition-operation-function-Categoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-function-Categoryᵉ
  associative-composition-operation-function-Categoryᵉ =
    associative-composition-operation-Categoryᵉ function-Categoryᵉ

  id-hom-function-Categoryᵉ :
    {xᵉ : obj-function-Categoryᵉ} → hom-function-Categoryᵉ xᵉ xᵉ
  id-hom-function-Categoryᵉ = id-hom-Categoryᵉ function-Categoryᵉ

  left-unit-law-comp-hom-function-Categoryᵉ :
    {xᵉ yᵉ : obj-function-Categoryᵉ}
    (fᵉ : hom-function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-function-Categoryᵉ id-hom-function-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-function-Categoryᵉ =
    left-unit-law-comp-hom-Categoryᵉ function-Categoryᵉ

  right-unit-law-comp-hom-function-Categoryᵉ :
    {xᵉ yᵉ : obj-function-Categoryᵉ} (fᵉ : hom-function-Categoryᵉ xᵉ yᵉ) →
    comp-hom-function-Categoryᵉ fᵉ id-hom-function-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-function-Categoryᵉ =
    right-unit-law-comp-hom-Categoryᵉ function-Categoryᵉ

  is-unital-function-Categoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-function-Categoryᵉ
      comp-hom-function-Categoryᵉ
  is-unital-function-Categoryᵉ =
    is-unital-composition-operation-Categoryᵉ function-Categoryᵉ

  extensionality-obj-function-Categoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ function-Categoryᵉ) →
    (xᵉ ＝ᵉ yᵉ) ≃ᵉ iso-Categoryᵉ function-Categoryᵉ xᵉ yᵉ
  extensionality-obj-function-Categoryᵉ =
    extensionality-obj-Categoryᵉ function-Categoryᵉ
```

### Isomorphisms in the function category are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Categoryᵉ l2ᵉ l3ᵉ)
  {xᵉ yᵉ : obj-function-Categoryᵉ Iᵉ Cᵉ}
  where

  is-fiberwise-iso-is-iso-function-Categoryᵉ :
    (fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Categoryᵉ Cᵉ (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-function-Categoryᵉ =
    is-fiberwise-iso-is-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  fiberwise-iso-iso-function-Categoryᵉ :
    iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-function-Categoryᵉ =
    fiberwise-iso-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-iso-function-is-fiberwise-iso-Categoryᵉ :
    (fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Categoryᵉ Cᵉ (fᵉ iᵉ)) →
    is-iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-function-is-fiberwise-iso-Categoryᵉ =
    is-iso-is-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  iso-function-fiberwise-iso-Categoryᵉ :
    ((iᵉ : Iᵉ) → iso-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-function-fiberwise-iso-Categoryᵉ =
    iso-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-fiberwise-iso-is-iso-function-Categoryᵉ :
    (fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-function-Categoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-function-Categoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-fiberwise-iso-is-iso-function-Categoryᵉ :
    (fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Categoryᵉ Cᵉ (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-function-Categoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-iso-function-is-fiberwise-iso-Categoryᵉ :
    (fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-function-is-fiberwise-iso-Categoryᵉ fᵉ)
  is-equiv-is-iso-function-is-fiberwise-iso-Categoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-iso-function-is-fiberwise-iso-Categoryᵉ :
    ( fᵉ : hom-function-Categoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Categoryᵉ Cᵉ (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-function-is-fiberwise-iso-Categoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-fiberwise-iso-iso-function-Categoryᵉ :
    is-equivᵉ fiberwise-iso-iso-function-Categoryᵉ
  is-equiv-fiberwise-iso-iso-function-Categoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-fiberwise-iso-iso-function-Categoryᵉ :
    ( iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-function-Categoryᵉ =
    equiv-fiberwise-iso-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-iso-function-fiberwise-iso-Categoryᵉ :
    is-equivᵉ iso-function-fiberwise-iso-Categoryᵉ
  is-equiv-iso-function-fiberwise-iso-Categoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-iso-function-fiberwise-iso-Categoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Categoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Categoryᵉ (function-Categoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-function-fiberwise-iso-Categoryᵉ =
    equiv-iso-fiberwise-iso-Π-Categoryᵉ Iᵉ (λ _ → Cᵉ)
```