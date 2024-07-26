# Center of a semigroup

```agda
module group-theory.centers-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-semigroupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsemigroupsᵉ
```

</details>

## Idea

Theᵉ centerᵉ ofᵉ aᵉ semigroupᵉ consistsᵉ ofᵉ thoseᵉ elementsᵉ thatᵉ areᵉ central.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  subtype-center-Semigroupᵉ : type-Semigroupᵉ Gᵉ → Propᵉ lᵉ
  subtype-center-Semigroupᵉ = is-central-element-prop-Semigroupᵉ Gᵉ

  center-Semigroupᵉ : Subsemigroupᵉ lᵉ Gᵉ
  pr1ᵉ center-Semigroupᵉ = subtype-center-Semigroupᵉ
  pr2ᵉ center-Semigroupᵉ {xᵉ} {yᵉ} = is-central-element-mul-Semigroupᵉ Gᵉ xᵉ yᵉ

  semigroup-center-Semigroupᵉ : Semigroupᵉ lᵉ
  semigroup-center-Semigroupᵉ = semigroup-Subsemigroupᵉ Gᵉ center-Semigroupᵉ

  type-center-Semigroupᵉ : UUᵉ lᵉ
  type-center-Semigroupᵉ =
    type-Subsemigroupᵉ Gᵉ center-Semigroupᵉ

  mul-center-Semigroupᵉ :
    (xᵉ yᵉ : type-center-Semigroupᵉ) → type-center-Semigroupᵉ
  mul-center-Semigroupᵉ = mul-Subsemigroupᵉ Gᵉ center-Semigroupᵉ

  associative-mul-center-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-center-Semigroupᵉ) →
    mul-center-Semigroupᵉ (mul-center-Semigroupᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-center-Semigroupᵉ xᵉ (mul-center-Semigroupᵉ yᵉ zᵉ)
  associative-mul-center-Semigroupᵉ =
    associative-mul-Subsemigroupᵉ Gᵉ center-Semigroupᵉ

  inclusion-center-Semigroupᵉ :
    type-center-Semigroupᵉ → type-Semigroupᵉ Gᵉ
  inclusion-center-Semigroupᵉ =
    inclusion-Subsemigroupᵉ Gᵉ center-Semigroupᵉ

  preserves-mul-inclusion-center-Semigroupᵉ :
    {xᵉ yᵉ : type-center-Semigroupᵉ} →
    inclusion-center-Semigroupᵉ (mul-center-Semigroupᵉ xᵉ yᵉ) ＝ᵉ
    mul-Semigroupᵉ Gᵉ
      ( inclusion-center-Semigroupᵉ xᵉ)
      ( inclusion-center-Semigroupᵉ yᵉ)
  preserves-mul-inclusion-center-Semigroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subsemigroupᵉ Gᵉ center-Semigroupᵉ {xᵉ} {yᵉ}

  hom-inclusion-center-Semigroupᵉ :
    hom-Semigroupᵉ semigroup-center-Semigroupᵉ Gᵉ
  hom-inclusion-center-Semigroupᵉ =
    hom-inclusion-Subsemigroupᵉ Gᵉ center-Semigroupᵉ
```