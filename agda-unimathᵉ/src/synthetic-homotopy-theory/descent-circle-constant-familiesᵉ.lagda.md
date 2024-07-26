# Descent data for constant type families over the circle

```agda
module synthetic-homotopy-theory.descent-circle-constant-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-type-familiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.descent-circleᵉ
open import synthetic-homotopy-theory.free-loopsᵉ
```

</details>

## Idea

[Descentᵉ data forᵉ theᵉ circle](synthetic-homotopy-theory.descent-circle.mdᵉ) forᵉ aᵉ
[constantᵉ typeᵉ family](foundation.constant-type-families.mdᵉ) isᵉ theᵉ typeᵉ itᵉ
evaluatesᵉ to,ᵉ togetherᵉ with theᵉ identity.ᵉ

## Definitions

### Descent data for constant type families over the circle

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Xᵉ : UUᵉ l2ᵉ)
  where

  descent-data-circle-constant-typeᵉ : descent-data-circleᵉ l2ᵉ
  pr1ᵉ descent-data-circle-constant-typeᵉ = Xᵉ
  pr2ᵉ descent-data-circle-constant-typeᵉ = id-equivᵉ

  family-descent-data-circle-constant-typeᵉ : Sᵉ → UUᵉ l2ᵉ
  family-descent-data-circle-constant-typeᵉ xᵉ = Xᵉ
```

## Properties

### Characterization of descent data for constant type families over the circle

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} (lᵉ : free-loopᵉ Sᵉ)
  ( Xᵉ : UUᵉ l2ᵉ)
  where

  eq-descent-data-circle-constant-typeᵉ :
    equiv-descent-data-circleᵉ
      ( descent-data-circle-constant-typeᵉ lᵉ Xᵉ)
      ( descent-data-family-circleᵉ lᵉ
        ( family-descent-data-circle-constant-typeᵉ lᵉ Xᵉ))
  pr1ᵉ eq-descent-data-circle-constant-typeᵉ = id-equivᵉ
  pr2ᵉ eq-descent-data-circle-constant-typeᵉ xᵉ =
    invᵉ (tr-constant-type-familyᵉ (loop-free-loopᵉ lᵉ) xᵉ)

  family-with-descent-data-constant-typeᵉ :
    family-with-descent-data-circleᵉ lᵉ l2ᵉ
  pr1ᵉ family-with-descent-data-constant-typeᵉ =
    family-descent-data-circle-constant-typeᵉ lᵉ Xᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-constant-typeᵉ) =
    descent-data-circle-constant-typeᵉ lᵉ Xᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-constant-typeᵉ) =
    eq-descent-data-circle-constant-typeᵉ
```