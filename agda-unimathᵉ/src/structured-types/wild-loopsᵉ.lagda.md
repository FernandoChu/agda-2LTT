# Wild loops

```agda
module structured-types.wild-loopsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.magmasᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.wild-quasigroupsᵉ
```

</details>

## Idea

Aᵉ wildᵉ loopᵉ isᵉ aᵉ wildᵉ quasigroupᵉ equippedᵉ with aᵉ unitᵉ element.ᵉ

## Definition

```agda
Wild-Loopᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Wild-Loopᵉ lᵉ =
  Σᵉ (H-Spaceᵉ lᵉ) (λ Mᵉ → is-binary-equivᵉ (mul-H-Spaceᵉ Mᵉ))

module _
  {lᵉ : Level} (Lᵉ : Wild-Loopᵉ lᵉ)
  where

  h-space-Wild-Loopᵉ : H-Spaceᵉ lᵉ
  h-space-Wild-Loopᵉ = pr1ᵉ Lᵉ

  pointed-type-Wild-Loopᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-Wild-Loopᵉ =
    pointed-type-H-Spaceᵉ h-space-Wild-Loopᵉ

  type-Wild-Loopᵉ : UUᵉ lᵉ
  type-Wild-Loopᵉ = type-H-Spaceᵉ h-space-Wild-Loopᵉ

  unit-Wild-Loopᵉ : type-Wild-Loopᵉ
  unit-Wild-Loopᵉ = unit-H-Spaceᵉ h-space-Wild-Loopᵉ

  unital-mul-Wild-Loopᵉ : coherent-unital-mul-Pointed-Typeᵉ pointed-type-Wild-Loopᵉ
  unital-mul-Wild-Loopᵉ =
    coherent-unital-mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  mul-Wild-Loopᵉ : type-Wild-Loopᵉ → type-Wild-Loopᵉ → type-Wild-Loopᵉ
  mul-Wild-Loopᵉ = mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  mul-Wild-Loop'ᵉ : type-Wild-Loopᵉ → type-Wild-Loopᵉ → type-Wild-Loopᵉ
  mul-Wild-Loop'ᵉ = mul-H-Space'ᵉ h-space-Wild-Loopᵉ

  ap-mul-Wild-Loopᵉ :
    {aᵉ bᵉ cᵉ dᵉ : type-Wild-Loopᵉ} → Idᵉ aᵉ bᵉ → Idᵉ cᵉ dᵉ →
    Idᵉ (mul-Wild-Loopᵉ aᵉ cᵉ) (mul-Wild-Loopᵉ bᵉ dᵉ)
  ap-mul-Wild-Loopᵉ = ap-mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  magma-Wild-Loopᵉ : Magmaᵉ lᵉ
  magma-Wild-Loopᵉ = magma-H-Spaceᵉ h-space-Wild-Loopᵉ

  left-unit-law-mul-Wild-Loopᵉ :
    (xᵉ : type-Wild-Loopᵉ) → Idᵉ (mul-Wild-Loopᵉ unit-Wild-Loopᵉ xᵉ) xᵉ
  left-unit-law-mul-Wild-Loopᵉ =
    left-unit-law-mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  right-unit-law-mul-Wild-Loopᵉ :
    (xᵉ : type-Wild-Loopᵉ) → Idᵉ (mul-Wild-Loopᵉ xᵉ unit-Wild-Loopᵉ) xᵉ
  right-unit-law-mul-Wild-Loopᵉ =
    right-unit-law-mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  coh-unit-laws-mul-Wild-Loopᵉ :
    Idᵉ
      ( left-unit-law-mul-Wild-Loopᵉ unit-Wild-Loopᵉ)
      ( right-unit-law-mul-Wild-Loopᵉ unit-Wild-Loopᵉ)
  coh-unit-laws-mul-Wild-Loopᵉ =
    coh-unit-laws-mul-H-Spaceᵉ h-space-Wild-Loopᵉ

  is-binary-equiv-mul-Wild-Loopᵉ : is-binary-equivᵉ mul-Wild-Loopᵉ
  is-binary-equiv-mul-Wild-Loopᵉ = pr2ᵉ Lᵉ

  wild-quasigroup-Wild-Loopᵉ : Wild-Quasigroupᵉ lᵉ
  pr1ᵉ wild-quasigroup-Wild-Loopᵉ = magma-Wild-Loopᵉ
  pr2ᵉ wild-quasigroup-Wild-Loopᵉ = is-binary-equiv-mul-Wild-Loopᵉ

  is-equiv-mul-Wild-Loopᵉ : (xᵉ : type-Wild-Loopᵉ) → is-equivᵉ (mul-Wild-Loopᵉ xᵉ)
  is-equiv-mul-Wild-Loopᵉ = pr2ᵉ is-binary-equiv-mul-Wild-Loopᵉ

  equiv-mul-Wild-Loopᵉ : type-Wild-Loopᵉ → Autᵉ type-Wild-Loopᵉ
  equiv-mul-Wild-Loopᵉ = equiv-mul-Wild-Quasigroupᵉ wild-quasigroup-Wild-Loopᵉ

  is-equiv-mul-Wild-Loop'ᵉ : (xᵉ : type-Wild-Loopᵉ) → is-equivᵉ (mul-Wild-Loop'ᵉ xᵉ)
  is-equiv-mul-Wild-Loop'ᵉ = pr1ᵉ is-binary-equiv-mul-Wild-Loopᵉ

  equiv-mul-Wild-Loop'ᵉ : type-Wild-Loopᵉ → Autᵉ type-Wild-Loopᵉ
  equiv-mul-Wild-Loop'ᵉ = equiv-mul-Wild-Quasigroup'ᵉ wild-quasigroup-Wild-Loopᵉ
```