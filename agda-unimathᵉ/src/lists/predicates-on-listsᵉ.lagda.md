# Predicates on lists

```agda
module lists.predicates-on-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ
```

</details>

## Definitions

### For all

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Pᵉ : Xᵉ → Propᵉ l2ᵉ)
  where

  for-all-list-Propᵉ :
    (lᵉ : listᵉ Xᵉ) → Propᵉ l2ᵉ
  for-all-list-Propᵉ nilᵉ = raise-unit-Propᵉ l2ᵉ
  for-all-list-Propᵉ (consᵉ xᵉ lᵉ) = product-Propᵉ (Pᵉ xᵉ) (for-all-list-Propᵉ lᵉ)

  for-all-listᵉ :
    (lᵉ : listᵉ Xᵉ) → UUᵉ l2ᵉ
  for-all-listᵉ lᵉ = type-Propᵉ (for-all-list-Propᵉ lᵉ)

  is-prop-for-all-listᵉ :
    (lᵉ : listᵉ Xᵉ) → is-propᵉ (for-all-listᵉ lᵉ)
  is-prop-for-all-listᵉ lᵉ = is-prop-type-Propᵉ (for-all-list-Propᵉ lᵉ)
```