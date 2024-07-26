# Wild semigroups

```agda
module structured-types.wild-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.magmasᵉ
```

</details>

## Idea

Aᵉ wildᵉ semigroupᵉ isᵉ aᵉ magmaᵉ ofᵉ with associativeᵉ multiplicationᵉ

## Definition

```agda
Wild-Semigroupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Wild-Semigroupᵉ lᵉ =
  Σᵉ ( Magmaᵉ lᵉ)
    ( λ Mᵉ →
      (xᵉ yᵉ zᵉ : type-Magmaᵉ Mᵉ) →
      Idᵉ (mul-Magmaᵉ Mᵉ (mul-Magmaᵉ Mᵉ xᵉ yᵉ) zᵉ) (mul-Magmaᵉ Mᵉ xᵉ (mul-Magmaᵉ Mᵉ yᵉ zᵉ)))

module _
  {lᵉ : Level} (Gᵉ : Wild-Semigroupᵉ lᵉ)
  where

  magma-Wild-Semigroupᵉ : Magmaᵉ lᵉ
  magma-Wild-Semigroupᵉ = pr1ᵉ Gᵉ

  type-Wild-Semigroupᵉ : UUᵉ lᵉ
  type-Wild-Semigroupᵉ = type-Magmaᵉ magma-Wild-Semigroupᵉ

  mul-Wild-Semigroupᵉ : (xᵉ yᵉ : type-Wild-Semigroupᵉ) → type-Wild-Semigroupᵉ
  mul-Wild-Semigroupᵉ = mul-Magmaᵉ magma-Wild-Semigroupᵉ

  mul-Wild-Semigroup'ᵉ : (xᵉ yᵉ : type-Wild-Semigroupᵉ) → type-Wild-Semigroupᵉ
  mul-Wild-Semigroup'ᵉ = mul-Magma'ᵉ magma-Wild-Semigroupᵉ

  associative-mul-Wild-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Wild-Semigroupᵉ) →
    Idᵉ
      ( mul-Wild-Semigroupᵉ (mul-Wild-Semigroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-Wild-Semigroupᵉ xᵉ (mul-Wild-Semigroupᵉ yᵉ zᵉ))
  associative-mul-Wild-Semigroupᵉ = pr2ᵉ Gᵉ
```