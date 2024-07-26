# Pointed families of types

```agda
module structured-types.pointed-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ pointedᵉ familyᵉ ofᵉ typesᵉ overᵉ aᵉ pointedᵉ typeᵉ `A`ᵉ isᵉ aᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ overᵉ
theᵉ underlyingᵉ typeᵉ ofᵉ `A`ᵉ equippedᵉ with aᵉ baseᵉ pointᵉ overᵉ theᵉ baseᵉ pointᵉ ofᵉ
`A`.ᵉ Noteᵉ thatᵉ aᵉ pointedᵉ familyᵉ ofᵉ typesᵉ shouldᵉ notᵉ beᵉ confusedᵉ with aᵉ familyᵉ ofᵉ
pointedᵉ typesᵉ overᵉ `A`.ᵉ

## Definition

```agda
Pointed-Famᵉ :
  {l1ᵉ : Level} (lᵉ : Level) (Aᵉ : Pointed-Typeᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Pointed-Famᵉ lᵉ Aᵉ =
  Σᵉ (type-Pointed-Typeᵉ Aᵉ → UUᵉ lᵉ) (λ Pᵉ → Pᵉ (point-Pointed-Typeᵉ Aᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ)
  where

  fam-Pointed-Famᵉ : type-Pointed-Typeᵉ Aᵉ → UUᵉ l2ᵉ
  fam-Pointed-Famᵉ = pr1ᵉ Bᵉ

  point-Pointed-Famᵉ : fam-Pointed-Famᵉ (point-Pointed-Typeᵉ Aᵉ)
  point-Pointed-Famᵉ = pr2ᵉ Bᵉ
```

## Examples

### The constant pointed family

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  constant-Pointed-Famᵉ :
    (Aᵉ : Pointed-Typeᵉ l1ᵉ) → Pointed-Typeᵉ l2ᵉ → Pointed-Famᵉ l2ᵉ Aᵉ
  constant-Pointed-Famᵉ Aᵉ Bᵉ =
    pairᵉ (λ _ → type-Pointed-Typeᵉ Bᵉ) (point-Pointed-Typeᵉ Bᵉ)
```