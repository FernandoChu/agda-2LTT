# Function precategories

```agda
module category-theory.function-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.dependent-products-of-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ anyᵉ typeᵉ `I`,ᵉ
theᵉ functionᵉ typeᵉ `Iᵉ → C`ᵉ isᵉ aᵉ precategoryᵉ consistingᵉ ofᵉ functionsᵉ takingᵉ
`iᵉ : I`ᵉ to anᵉ objectᵉ ofᵉ `C`.ᵉ Everyᵉ componentᵉ ofᵉ theᵉ structureᵉ isᵉ givenᵉ
pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Precategoryᵉ l2ᵉ l3ᵉ)
  where

  function-Precategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l2ᵉ) (l1ᵉ ⊔ l3ᵉ)
  function-Precategoryᵉ = Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  obj-function-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  obj-function-Precategoryᵉ = obj-Precategoryᵉ function-Precategoryᵉ

  hom-set-function-Precategoryᵉ :
    obj-function-Precategoryᵉ → obj-function-Precategoryᵉ → Setᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-set-function-Precategoryᵉ = hom-set-Precategoryᵉ function-Precategoryᵉ

  hom-function-Precategoryᵉ :
    obj-function-Precategoryᵉ → obj-function-Precategoryᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  hom-function-Precategoryᵉ = hom-Precategoryᵉ function-Precategoryᵉ

  comp-hom-function-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-function-Precategoryᵉ} →
    hom-function-Precategoryᵉ yᵉ zᵉ →
    hom-function-Precategoryᵉ xᵉ yᵉ →
    hom-function-Precategoryᵉ xᵉ zᵉ
  comp-hom-function-Precategoryᵉ = comp-hom-Precategoryᵉ function-Precategoryᵉ

  associative-comp-hom-function-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-function-Precategoryᵉ}
    (hᵉ : hom-function-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-function-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-function-Precategoryᵉ (comp-hom-function-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-function-Precategoryᵉ hᵉ (comp-hom-function-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-function-Precategoryᵉ =
    associative-comp-hom-Precategoryᵉ function-Precategoryᵉ

  involutive-eq-associative-comp-hom-function-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-function-Precategoryᵉ}
    (hᵉ : hom-function-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-function-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-function-Precategoryᵉ (comp-hom-function-Precategoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-function-Precategoryᵉ hᵉ (comp-hom-function-Precategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-function-Precategoryᵉ =
    involutive-eq-associative-comp-hom-Precategoryᵉ function-Precategoryᵉ

  associative-composition-operation-function-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-function-Precategoryᵉ
  associative-composition-operation-function-Precategoryᵉ =
    associative-composition-operation-Precategoryᵉ function-Precategoryᵉ

  id-hom-function-Precategoryᵉ :
    {xᵉ : obj-function-Precategoryᵉ} → hom-function-Precategoryᵉ xᵉ xᵉ
  id-hom-function-Precategoryᵉ = id-hom-Precategoryᵉ function-Precategoryᵉ

  left-unit-law-comp-hom-function-Precategoryᵉ :
    {xᵉ yᵉ : obj-function-Precategoryᵉ}
    (fᵉ : hom-function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-function-Precategoryᵉ id-hom-function-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-function-Precategoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ function-Precategoryᵉ

  right-unit-law-comp-hom-function-Precategoryᵉ :
    {xᵉ yᵉ : obj-function-Precategoryᵉ} (fᵉ : hom-function-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-function-Precategoryᵉ fᵉ id-hom-function-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-function-Precategoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ function-Precategoryᵉ

  is-unital-function-Precategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      hom-set-function-Precategoryᵉ
      comp-hom-function-Precategoryᵉ
  is-unital-function-Precategoryᵉ =
    is-unital-composition-operation-Precategoryᵉ function-Precategoryᵉ
```

### Isomorphisms in the function precategory are fiberwise isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Cᵉ : Precategoryᵉ l2ᵉ l3ᵉ)
  {xᵉ yᵉ : obj-function-Precategoryᵉ Iᵉ Cᵉ}
  where

  is-fiberwise-iso-is-iso-function-Precategoryᵉ :
    (fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) fᵉ →
    (iᵉ : Iᵉ) → is-iso-Precategoryᵉ Cᵉ (fᵉ iᵉ)
  is-fiberwise-iso-is-iso-function-Precategoryᵉ =
    is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  fiberwise-iso-iso-function-Precategoryᵉ :
    iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ →
    (iᵉ : Iᵉ) → iso-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)
  fiberwise-iso-iso-function-Precategoryᵉ =
    fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-iso-function-is-fiberwise-iso-Precategoryᵉ :
    (fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ((iᵉ : Iᵉ) → is-iso-Precategoryᵉ Cᵉ (fᵉ iᵉ)) →
    is-iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) fᵉ
  is-iso-function-is-fiberwise-iso-Precategoryᵉ =
    is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  iso-function-fiberwise-iso-Precategoryᵉ :
    ((iᵉ : Iᵉ) → iso-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) →
    iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ
  iso-function-fiberwise-iso-Precategoryᵉ =
    iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-fiberwise-iso-is-iso-function-Precategoryᵉ :
    (fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-fiberwise-iso-is-iso-function-Precategoryᵉ fᵉ)
  is-equiv-is-fiberwise-iso-is-iso-function-Precategoryᵉ =
    is-equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-fiberwise-iso-is-iso-function-Precategoryᵉ :
    (fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( is-iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) fᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → is-iso-Precategoryᵉ Cᵉ (fᵉ iᵉ))
  equiv-is-fiberwise-iso-is-iso-function-Precategoryᵉ =
    equiv-is-fiberwise-iso-is-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-is-iso-function-is-fiberwise-iso-Precategoryᵉ :
    (fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    is-equivᵉ (is-iso-function-is-fiberwise-iso-Precategoryᵉ fᵉ)
  is-equiv-is-iso-function-is-fiberwise-iso-Precategoryᵉ =
    is-equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-is-iso-function-is-fiberwise-iso-Precategoryᵉ :
    ( fᵉ : hom-function-Precategoryᵉ Iᵉ Cᵉ xᵉ yᵉ) →
    ( (iᵉ : Iᵉ) → is-iso-Precategoryᵉ Cᵉ (fᵉ iᵉ)) ≃ᵉ
    ( is-iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) fᵉ)
  equiv-is-iso-function-is-fiberwise-iso-Precategoryᵉ =
    equiv-is-iso-is-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-fiberwise-iso-iso-function-Precategoryᵉ :
    is-equivᵉ fiberwise-iso-iso-function-Precategoryᵉ
  is-equiv-fiberwise-iso-iso-function-Precategoryᵉ =
    is-equiv-fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-fiberwise-iso-iso-function-Precategoryᵉ :
    ( iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ) ≃ᵉ
    ( (iᵉ : Iᵉ) → iso-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ))
  equiv-fiberwise-iso-iso-function-Precategoryᵉ =
    equiv-fiberwise-iso-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  is-equiv-iso-function-fiberwise-iso-Precategoryᵉ :
    is-equivᵉ iso-function-fiberwise-iso-Precategoryᵉ
  is-equiv-iso-function-fiberwise-iso-Precategoryᵉ =
    is-equiv-iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)

  equiv-iso-function-fiberwise-iso-Precategoryᵉ :
    ( (iᵉ : Iᵉ) → iso-Precategoryᵉ Cᵉ (xᵉ iᵉ) (yᵉ iᵉ)) ≃ᵉ
    ( iso-Precategoryᵉ (function-Precategoryᵉ Iᵉ Cᵉ) xᵉ yᵉ)
  equiv-iso-function-fiberwise-iso-Precategoryᵉ =
    equiv-iso-fiberwise-iso-Π-Precategoryᵉ Iᵉ (λ _ → Cᵉ)
```