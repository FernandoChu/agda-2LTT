# Pointed types

```agda
module structured-types.pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **pointedᵉ type**ᵉ isᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with anᵉ elementᵉ `aᵉ : A`.ᵉ

## Definition

### The universe of pointed types

```agda
Pointed-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Pointed-Typeᵉ lᵉ = Σᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ)

module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  type-Pointed-Typeᵉ : UUᵉ lᵉ
  type-Pointed-Typeᵉ = pr1ᵉ Aᵉ

  point-Pointed-Typeᵉ : type-Pointed-Typeᵉ
  point-Pointed-Typeᵉ = pr2ᵉ Aᵉ
```

### Evaluation at the base point

```agda
ev-point-Pointed-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} →
  (type-Pointed-Typeᵉ Aᵉ → Bᵉ) → Bᵉ
ev-point-Pointed-Typeᵉ Aᵉ fᵉ = fᵉ (point-Pointed-Typeᵉ Aᵉ)
```

## See also

-ᵉ Theᵉ notionᵉ ofᵉ _nonemptyᵉ typesᵉ_ isᵉ treatedᵉ in
  [`foundation.empty-types`](foundation.empty-types.md).ᵉ
-ᵉ Theᵉ notionᵉ ofᵉ _inhabitedᵉ typesᵉ_ isᵉ treatedᵉ in
  [`foundation.inhabited-types`](foundation.inhabited-types.md).ᵉ