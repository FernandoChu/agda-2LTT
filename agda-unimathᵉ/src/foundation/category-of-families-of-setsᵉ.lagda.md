# The category of families of sets

```agda
module foundation.category-of-families-of-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-function-categoriesᵉ
open import category-theory.large-function-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **[largeᵉ category](category-theory.large-categories.mdᵉ) ofᵉ familiesᵉ ofᵉ
[sets](foundation.sets.mdᵉ) overᵉ aᵉ type**ᵉ `A`ᵉ isᵉ theᵉ
[largeᵉ functionᵉ category](category-theory.large-function-categories.mdᵉ)
`Aᵉ → Set`.ᵉ

## Definition

### The large precategory of families of sets over a type

```agda
Family-Of-Sets-Large-Precategoryᵉ :
  {lᵉ : Level} → UUᵉ lᵉ →
  Large-Precategoryᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
Family-Of-Sets-Large-Precategoryᵉ Aᵉ =
  Large-Function-Precategoryᵉ Aᵉ Set-Large-Precategoryᵉ
```

### The small precategory of families of sets over a type

```agda
Family-Of-Sets-Precategoryᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → Precategoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Family-Of-Sets-Precategoryᵉ l2ᵉ Aᵉ =
  precategory-Large-Precategoryᵉ (Family-Of-Sets-Large-Precategoryᵉ Aᵉ) l2ᵉ
```

### The large category of families of sets over a type

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  Family-Of-Sets-Large-Categoryᵉ :
    Large-Categoryᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  Family-Of-Sets-Large-Categoryᵉ =
    Large-Function-Categoryᵉ Aᵉ Set-Large-Categoryᵉ

  is-large-category-Family-Of-Sets-Large-Categoryᵉ :
    is-large-category-Large-Precategoryᵉ (Family-Of-Sets-Large-Precategoryᵉ Aᵉ)
  is-large-category-Family-Of-Sets-Large-Categoryᵉ =
    is-large-category-Large-Categoryᵉ Family-Of-Sets-Large-Categoryᵉ
```

### The small category of families of sets over a type

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ)
  where

  Family-Of-Sets-Categoryᵉ : Categoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  Family-Of-Sets-Categoryᵉ =
    category-Large-Categoryᵉ (Family-Of-Sets-Large-Categoryᵉ Aᵉ) l2ᵉ

  is-category-Family-Of-Sets-Categoryᵉ :
    is-category-Precategoryᵉ (Family-Of-Sets-Precategoryᵉ l2ᵉ Aᵉ)
  is-category-Family-Of-Sets-Categoryᵉ =
    is-category-Categoryᵉ Family-Of-Sets-Categoryᵉ
```