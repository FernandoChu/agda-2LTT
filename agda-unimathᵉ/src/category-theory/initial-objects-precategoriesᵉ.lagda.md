# Initial objects in a precategory

```agda
module category-theory.initial-objects-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ **initialᵉ object**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.md),ᵉ ifᵉ
itᵉ exists,ᵉ isᵉ anᵉ objectᵉ with theᵉ universalᵉ propertyᵉ thatᵉ thereᵉ isᵉ aᵉ
[unique](foundation-core.contractible-types.mdᵉ) morphismᵉ fromᵉ itᵉ to anyᵉ object.ᵉ

## Definitions

### The universal property of an initial object in a precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (xᵉ : obj-Precategoryᵉ Cᵉ)
  where

  is-initial-prop-obj-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-initial-prop-obj-Precategoryᵉ =
    Π-Propᵉ
      ( obj-Precategoryᵉ Cᵉ)
      ( λ yᵉ → is-contr-Propᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ))

  is-initial-obj-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-initial-obj-Precategoryᵉ = type-Propᵉ is-initial-prop-obj-Precategoryᵉ

  is-prop-is-initial-obj-Precategoryᵉ : is-propᵉ is-initial-obj-Precategoryᵉ
  is-prop-is-initial-obj-Precategoryᵉ =
    is-prop-type-Propᵉ is-initial-prop-obj-Precategoryᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ : obj-Precategoryᵉ Cᵉ)
  (tᵉ : is-initial-obj-Precategoryᵉ Cᵉ xᵉ)
  where

  hom-is-initial-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  hom-is-initial-obj-Precategoryᵉ = centerᵉ ∘ᵉ tᵉ

  is-unique-hom-is-initial-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-is-initial-obj-Precategoryᵉ yᵉ ＝ᵉ fᵉ
  is-unique-hom-is-initial-obj-Precategoryᵉ = contractionᵉ ∘ᵉ tᵉ
```

### Initial objects in precategories

```agda
initial-obj-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
initial-obj-Precategoryᵉ Cᵉ =
  Σᵉ (obj-Precategoryᵉ Cᵉ) (is-initial-obj-Precategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : initial-obj-Precategoryᵉ Cᵉ)
  where

  obj-initial-obj-Precategoryᵉ : obj-Precategoryᵉ Cᵉ
  obj-initial-obj-Precategoryᵉ = pr1ᵉ tᵉ

  is-initial-obj-initial-obj-Precategoryᵉ :
    is-initial-obj-Precategoryᵉ Cᵉ obj-initial-obj-Precategoryᵉ
  is-initial-obj-initial-obj-Precategoryᵉ = pr2ᵉ tᵉ

  hom-initial-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ obj-initial-obj-Precategoryᵉ yᵉ
  hom-initial-obj-Precategoryᵉ =
    hom-is-initial-obj-Precategoryᵉ Cᵉ
      ( obj-initial-obj-Precategoryᵉ)
      ( is-initial-obj-initial-obj-Precategoryᵉ)

  is-unique-hom-initial-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ obj-initial-obj-Precategoryᵉ yᵉ) →
    hom-initial-obj-Precategoryᵉ yᵉ ＝ᵉ fᵉ
  is-unique-hom-initial-obj-Precategoryᵉ =
    is-unique-hom-is-initial-obj-Precategoryᵉ Cᵉ
      ( obj-initial-obj-Precategoryᵉ)
      ( is-initial-obj-initial-obj-Precategoryᵉ)
```