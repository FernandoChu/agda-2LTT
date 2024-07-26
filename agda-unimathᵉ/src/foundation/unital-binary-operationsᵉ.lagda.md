# Unital binary operations

```agda
module foundation.unital-binary-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ binaryᵉ operationᵉ ofᵉ typeᵉ `Aᵉ → Aᵉ → A`ᵉ isᵉ **unital**ᵉ ifᵉ thereᵉ isᵉ aᵉ unitᵉ ofᵉ typeᵉ
`A`ᵉ thatᵉ satisfiesᵉ bothᵉ theᵉ leftᵉ andᵉ rightᵉ unitᵉ laws.ᵉ Furthermore,ᵉ aᵉ binaryᵉ
operationᵉ isᵉ **coherentlyᵉ unital**ᵉ ifᵉ theᵉ proofsᵉ ofᵉ theᵉ leftᵉ andᵉ rightᵉ unitᵉ lawsᵉ
agreeᵉ onᵉ theᵉ caseᵉ where bothᵉ argumentsᵉ ofᵉ theᵉ operationᵉ areᵉ theᵉ unit.ᵉ

## Definitions

### Unit laws

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (μᵉ : Aᵉ → Aᵉ → Aᵉ) (eᵉ : Aᵉ)
  where

  left-unit-lawᵉ : UUᵉ lᵉ
  left-unit-lawᵉ = (xᵉ : Aᵉ) → μᵉ eᵉ xᵉ ＝ᵉ xᵉ

  right-unit-lawᵉ : UUᵉ lᵉ
  right-unit-lawᵉ = (xᵉ : Aᵉ) → μᵉ xᵉ eᵉ ＝ᵉ xᵉ

  coh-unit-lawsᵉ : left-unit-lawᵉ → right-unit-lawᵉ → UUᵉ lᵉ
  coh-unit-lawsᵉ αᵉ βᵉ = (αᵉ eᵉ ＝ᵉ βᵉ eᵉ)

  unit-lawsᵉ : UUᵉ lᵉ
  unit-lawsᵉ = left-unit-lawᵉ ×ᵉ right-unit-lawᵉ

  coherent-unit-lawsᵉ : UUᵉ lᵉ
  coherent-unit-lawsᵉ =
    Σᵉ left-unit-lawᵉ (λ αᵉ → Σᵉ right-unit-lawᵉ (coh-unit-lawsᵉ αᵉ))
```

### Unital binary operations

```agda
is-unitalᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (μᵉ : Aᵉ → Aᵉ → Aᵉ) → UUᵉ lᵉ
is-unitalᵉ {Aᵉ = Aᵉ} μᵉ = Σᵉ Aᵉ (unit-lawsᵉ μᵉ)
```

### Coherently unital binary operations

```agda
is-coherently-unitalᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (μᵉ : Aᵉ → Aᵉ → Aᵉ) → UUᵉ lᵉ
is-coherently-unitalᵉ {Aᵉ = Aᵉ} μᵉ = Σᵉ Aᵉ (coherent-unit-lawsᵉ μᵉ)
```

## Properties

### The unit laws for an operation `μ` with unit `e` can be upgraded to coherent unit laws

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (μᵉ : Aᵉ → Aᵉ → Aᵉ) {eᵉ : Aᵉ}
  where

  coherent-unit-laws-unit-lawsᵉ : unit-lawsᵉ μᵉ eᵉ → coherent-unit-lawsᵉ μᵉ eᵉ
  pr1ᵉ (coherent-unit-laws-unit-lawsᵉ (pairᵉ Hᵉ Kᵉ)) = Hᵉ
  pr1ᵉ (pr2ᵉ (coherent-unit-laws-unit-lawsᵉ (pairᵉ Hᵉ Kᵉ))) xᵉ =
    ( invᵉ (apᵉ (μᵉ xᵉ) (Kᵉ eᵉ))) ∙ᵉ (( apᵉ (μᵉ xᵉ) (Hᵉ eᵉ)) ∙ᵉ (Kᵉ xᵉ))
  pr2ᵉ (pr2ᵉ (coherent-unit-laws-unit-lawsᵉ (pairᵉ Hᵉ Kᵉ))) =
    left-transpose-eq-concatᵉ
      ( apᵉ (μᵉ eᵉ) (Kᵉ eᵉ))
      ( Hᵉ eᵉ)
      ( (apᵉ (μᵉ eᵉ) (Hᵉ eᵉ)) ∙ᵉ (Kᵉ eᵉ))
      ( ( inv-nat-htpy-idᵉ (Hᵉ) (Kᵉ eᵉ)) ∙ᵉ
        ( right-whisker-concatᵉ (coh-htpy-idᵉ (Hᵉ) eᵉ) (Kᵉ eᵉ)))

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {μᵉ : Aᵉ → Aᵉ → Aᵉ}
  where

  is-coherently-unital-is-unitalᵉ : is-unitalᵉ μᵉ → is-coherently-unitalᵉ μᵉ
  pr1ᵉ (is-coherently-unital-is-unitalᵉ (pairᵉ eᵉ Hᵉ)) = eᵉ
  pr2ᵉ (is-coherently-unital-is-unitalᵉ (pairᵉ eᵉ Hᵉ)) =
    coherent-unit-laws-unit-lawsᵉ μᵉ Hᵉ
```