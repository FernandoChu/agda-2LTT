# Central elements of semirings

```agda
module group-theory.central-elements-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ semigroupᵉ `G`ᵉ isᵉ saidᵉ to beᵉ centralᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ forᵉ everyᵉ
`yᵉ : G`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  is-central-element-prop-Semigroupᵉ : type-Semigroupᵉ Gᵉ → Propᵉ lᵉ
  is-central-element-prop-Semigroupᵉ xᵉ =
    Π-Propᵉ
      ( type-Semigroupᵉ Gᵉ)
      ( λ yᵉ →
        Id-Propᵉ
          ( set-Semigroupᵉ Gᵉ)
          ( mul-Semigroupᵉ Gᵉ xᵉ yᵉ)
          ( mul-Semigroupᵉ Gᵉ yᵉ xᵉ))

  is-central-element-Semigroupᵉ : type-Semigroupᵉ Gᵉ → UUᵉ lᵉ
  is-central-element-Semigroupᵉ xᵉ =
    type-Propᵉ (is-central-element-prop-Semigroupᵉ xᵉ)

  is-prop-is-central-element-Semigroupᵉ :
    (xᵉ : type-Semigroupᵉ Gᵉ) → is-propᵉ (is-central-element-Semigroupᵉ xᵉ)
  is-prop-is-central-element-Semigroupᵉ xᵉ =
    is-prop-type-Propᵉ (is-central-element-prop-Semigroupᵉ xᵉ)
```

## Properties

### The product of two central elements is central

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  is-central-element-mul-Semigroupᵉ :
    (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) →
    is-central-element-Semigroupᵉ Gᵉ xᵉ → is-central-element-Semigroupᵉ Gᵉ yᵉ →
    is-central-element-Semigroupᵉ Gᵉ (mul-Semigroupᵉ Gᵉ xᵉ yᵉ)
  is-central-element-mul-Semigroupᵉ xᵉ yᵉ Hᵉ Kᵉ zᵉ =
    ( associative-mul-Semigroupᵉ Gᵉ xᵉ yᵉ zᵉ) ∙ᵉ
    ( apᵉ (mul-Semigroupᵉ Gᵉ xᵉ) (Kᵉ zᵉ)) ∙ᵉ
    ( invᵉ (associative-mul-Semigroupᵉ Gᵉ xᵉ zᵉ yᵉ)) ∙ᵉ
    ( apᵉ (mul-Semigroup'ᵉ Gᵉ yᵉ) (Hᵉ zᵉ)) ∙ᵉ
    ( associative-mul-Semigroupᵉ Gᵉ zᵉ xᵉ yᵉ)
```