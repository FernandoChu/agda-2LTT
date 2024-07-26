# Wild quasigroups

```agda
module structured-types.wild-quasigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.magmasᵉ
```

</details>

## Idea

Aᵉ wildᵉ quasigroupᵉ isᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ binaryᵉ equivalenceᵉ
`μᵉ : Aᵉ → Aᵉ → A`.ᵉ

## Definition

```agda
Wild-Quasigroupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Wild-Quasigroupᵉ lᵉ = Σᵉ (Magmaᵉ lᵉ) (λ Mᵉ → is-binary-equivᵉ (mul-Magmaᵉ Mᵉ))

module _
  {lᵉ : Level} (Aᵉ : Wild-Quasigroupᵉ lᵉ)
  where

  magma-Wild-Quasigroupᵉ : Magmaᵉ lᵉ
  magma-Wild-Quasigroupᵉ = pr1ᵉ Aᵉ

  type-Wild-Quasigroupᵉ : UUᵉ lᵉ
  type-Wild-Quasigroupᵉ = type-Magmaᵉ magma-Wild-Quasigroupᵉ

  mul-Wild-Quasigroupᵉ : (xᵉ yᵉ : type-Wild-Quasigroupᵉ) → type-Wild-Quasigroupᵉ
  mul-Wild-Quasigroupᵉ = mul-Magmaᵉ magma-Wild-Quasigroupᵉ

  mul-Wild-Quasigroup'ᵉ : (xᵉ yᵉ : type-Wild-Quasigroupᵉ) → type-Wild-Quasigroupᵉ
  mul-Wild-Quasigroup'ᵉ xᵉ yᵉ = mul-Wild-Quasigroupᵉ yᵉ xᵉ

  is-binary-equiv-mul-Wild-Quasigroupᵉ :
    is-binary-equivᵉ mul-Wild-Quasigroupᵉ
  is-binary-equiv-mul-Wild-Quasigroupᵉ = pr2ᵉ Aᵉ

  is-equiv-mul-Wild-Quasigroupᵉ :
    (xᵉ : type-Wild-Quasigroupᵉ) → is-equivᵉ (mul-Wild-Quasigroupᵉ xᵉ)
  is-equiv-mul-Wild-Quasigroupᵉ = pr2ᵉ is-binary-equiv-mul-Wild-Quasigroupᵉ

  equiv-mul-Wild-Quasigroupᵉ : type-Wild-Quasigroupᵉ → Autᵉ type-Wild-Quasigroupᵉ
  pr1ᵉ (equiv-mul-Wild-Quasigroupᵉ xᵉ) = mul-Wild-Quasigroupᵉ xᵉ
  pr2ᵉ (equiv-mul-Wild-Quasigroupᵉ xᵉ) = is-equiv-mul-Wild-Quasigroupᵉ xᵉ

  is-equiv-mul-Wild-Quasigroup'ᵉ :
    (xᵉ : type-Wild-Quasigroupᵉ) → is-equivᵉ (mul-Wild-Quasigroup'ᵉ xᵉ)
  is-equiv-mul-Wild-Quasigroup'ᵉ = pr1ᵉ is-binary-equiv-mul-Wild-Quasigroupᵉ

  equiv-mul-Wild-Quasigroup'ᵉ : type-Wild-Quasigroupᵉ → Autᵉ type-Wild-Quasigroupᵉ
  pr1ᵉ (equiv-mul-Wild-Quasigroup'ᵉ xᵉ) = mul-Wild-Quasigroup'ᵉ xᵉ
  pr2ᵉ (equiv-mul-Wild-Quasigroup'ᵉ xᵉ) = is-equiv-mul-Wild-Quasigroup'ᵉ xᵉ
```