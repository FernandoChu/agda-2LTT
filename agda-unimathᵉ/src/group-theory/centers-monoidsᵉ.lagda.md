# Center of a monoid

```agda
module group-theory.centers-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-monoidsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.submonoidsᵉ
```

</details>

## Idea

Theᵉ **center**ᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) consistsᵉ ofᵉ thoseᵉ elementsᵉ
thatᵉ areᵉ central.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  subtype-center-Monoidᵉ : type-Monoidᵉ Mᵉ → Propᵉ lᵉ
  subtype-center-Monoidᵉ = is-central-element-prop-Monoidᵉ Mᵉ

  center-Monoidᵉ : Submonoidᵉ lᵉ Mᵉ
  pr1ᵉ center-Monoidᵉ = subtype-center-Monoidᵉ
  pr1ᵉ (pr2ᵉ center-Monoidᵉ) = is-central-element-unit-Monoidᵉ Mᵉ
  pr2ᵉ (pr2ᵉ center-Monoidᵉ) = is-central-element-mul-Monoidᵉ Mᵉ

  monoid-center-Monoidᵉ : Monoidᵉ lᵉ
  monoid-center-Monoidᵉ = monoid-Submonoidᵉ Mᵉ center-Monoidᵉ

  type-center-Monoidᵉ : UUᵉ lᵉ
  type-center-Monoidᵉ =
    type-Submonoidᵉ Mᵉ center-Monoidᵉ

  mul-center-Monoidᵉ :
    (xᵉ yᵉ : type-center-Monoidᵉ) → type-center-Monoidᵉ
  mul-center-Monoidᵉ = mul-Submonoidᵉ Mᵉ center-Monoidᵉ

  associative-mul-center-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-center-Monoidᵉ) →
    mul-center-Monoidᵉ (mul-center-Monoidᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-center-Monoidᵉ xᵉ (mul-center-Monoidᵉ yᵉ zᵉ)
  associative-mul-center-Monoidᵉ =
    associative-mul-Submonoidᵉ Mᵉ center-Monoidᵉ

  inclusion-center-Monoidᵉ :
    type-center-Monoidᵉ → type-Monoidᵉ Mᵉ
  inclusion-center-Monoidᵉ =
    inclusion-Submonoidᵉ Mᵉ center-Monoidᵉ

  preserves-mul-inclusion-center-Monoidᵉ :
    {xᵉ yᵉ : type-center-Monoidᵉ} →
    inclusion-center-Monoidᵉ (mul-center-Monoidᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Mᵉ
      ( inclusion-center-Monoidᵉ xᵉ)
      ( inclusion-center-Monoidᵉ yᵉ)
  preserves-mul-inclusion-center-Monoidᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Submonoidᵉ Mᵉ center-Monoidᵉ {xᵉ} {yᵉ}

  hom-inclusion-center-Monoidᵉ :
    hom-Monoidᵉ monoid-center-Monoidᵉ Mᵉ
  hom-inclusion-center-Monoidᵉ =
    hom-inclusion-Submonoidᵉ Mᵉ center-Monoidᵉ
```