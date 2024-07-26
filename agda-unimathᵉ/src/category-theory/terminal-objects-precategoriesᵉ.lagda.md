# Terminal objects in a precategory

```agda
module category-theory.terminal-objects-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **terminalᵉ object**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.md),ᵉ ifᵉ
itᵉ exists,ᵉ isᵉ anᵉ objectᵉ with theᵉ universalᵉ propertyᵉ thatᵉ thereᵉ isᵉ aᵉ
[unique](foundation-core.contractible-types.mdᵉ) morphismᵉ intoᵉ itᵉ fromᵉ anyᵉ
object.ᵉ

## Definition

### The universal property of a terminal object in a precategory

```agda
is-terminal-obj-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → obj-Precategoryᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-terminal-obj-Precategoryᵉ Cᵉ xᵉ =
  (yᵉ : obj-Precategoryᵉ Cᵉ) → is-contrᵉ (hom-Precategoryᵉ Cᵉ yᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (xᵉ : obj-Precategoryᵉ Cᵉ)
  (tᵉ : is-terminal-obj-Precategoryᵉ Cᵉ xᵉ)
  where

  hom-is-terminal-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ yᵉ xᵉ
  hom-is-terminal-obj-Precategoryᵉ = centerᵉ ∘ᵉ tᵉ

  is-unique-hom-is-terminal-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ xᵉ) →
    hom-is-terminal-obj-Precategoryᵉ yᵉ ＝ᵉ fᵉ
  is-unique-hom-is-terminal-obj-Precategoryᵉ = contractionᵉ ∘ᵉ tᵉ
```

### Terminal objects in precategories

```agda
terminal-obj-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
terminal-obj-Precategoryᵉ Cᵉ =
  Σᵉ (obj-Precategoryᵉ Cᵉ) (is-terminal-obj-Precategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (tᵉ : terminal-obj-Precategoryᵉ Cᵉ)
  where

  obj-terminal-obj-Precategoryᵉ : obj-Precategoryᵉ Cᵉ
  obj-terminal-obj-Precategoryᵉ = pr1ᵉ tᵉ

  is-terminal-obj-terminal-obj-Precategoryᵉ :
    is-terminal-obj-Precategoryᵉ Cᵉ obj-terminal-obj-Precategoryᵉ
  is-terminal-obj-terminal-obj-Precategoryᵉ = pr2ᵉ tᵉ

  hom-terminal-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    hom-Precategoryᵉ Cᵉ yᵉ obj-terminal-obj-Precategoryᵉ
  hom-terminal-obj-Precategoryᵉ =
    hom-is-terminal-obj-Precategoryᵉ Cᵉ
      ( obj-terminal-obj-Precategoryᵉ)
      ( is-terminal-obj-terminal-obj-Precategoryᵉ)

  is-unique-hom-terminal-obj-Precategoryᵉ :
    (yᵉ : obj-Precategoryᵉ Cᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ yᵉ obj-terminal-obj-Precategoryᵉ) →
    hom-terminal-obj-Precategoryᵉ yᵉ ＝ᵉ fᵉ
  is-unique-hom-terminal-obj-Precategoryᵉ =
    is-unique-hom-is-terminal-obj-Precategoryᵉ Cᵉ
      ( obj-terminal-obj-Precategoryᵉ)
      ( is-terminal-obj-terminal-obj-Precategoryᵉ)
```