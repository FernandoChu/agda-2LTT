# Connected types

```agda
module foundation.connected-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.truncationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ **`k`-connected**ᵉ ifᵉ itsᵉ `k`-truncationᵉ isᵉ contractible.ᵉ

## Definition

```agda
is-connected-Propᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → Propᵉ lᵉ
is-connected-Propᵉ kᵉ Aᵉ = is-contr-Propᵉ (type-truncᵉ kᵉ Aᵉ)

is-connectedᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
is-connectedᵉ kᵉ Aᵉ = type-Propᵉ (is-connected-Propᵉ kᵉ Aᵉ)

is-prop-is-connectedᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-connectedᵉ kᵉ Aᵉ)
is-prop-is-connectedᵉ kᵉ Aᵉ = is-prop-type-Propᵉ (is-connected-Propᵉ kᵉ Aᵉ)
```

## Properties

### All types are `(-2)`-connected

```agda
is-neg-two-connectedᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-connectedᵉ neg-two-𝕋ᵉ Aᵉ
is-neg-two-connectedᵉ Aᵉ = is-trunc-type-truncᵉ
```

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-exponential-is-connectedᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-connectedᵉ kᵉ Aᵉ →
  is-equivᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Bᵉ) Aᵉ)
is-equiv-diagonal-exponential-is-connectedᵉ {kᵉ = kᵉ} {Aᵉ} Bᵉ Hᵉ =
  is-equiv-compᵉ
    ( precompᵉ unit-truncᵉ (type-Truncated-Typeᵉ Bᵉ))
    ( diagonal-exponentialᵉ (type-Truncated-Typeᵉ Bᵉ) (type-truncᵉ kᵉ Aᵉ))
    ( is-equiv-diagonal-exponential-is-contrᵉ Hᵉ (type-Truncated-Typeᵉ Bᵉ))
    ( is-truncation-truncᵉ Bᵉ)

is-connected-is-equiv-diagonal-exponentialᵉ :
  {l1ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  ( {l2ᵉ : Level} (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
    is-equivᵉ (diagonal-exponentialᵉ (type-Truncated-Typeᵉ Bᵉ) Aᵉ)) →
  is-connectedᵉ kᵉ Aᵉ
is-connected-is-equiv-diagonal-exponentialᵉ {kᵉ = kᵉ} {Aᵉ} Hᵉ =
  totᵉ
    ( λ xᵉ →
      function-dependent-universal-property-truncᵉ
        ( Id-Truncated-Type'ᵉ (truncᵉ kᵉ Aᵉ) xᵉ))
    ( totᵉ
      ( λ _ → htpy-eqᵉ)
      ( centerᵉ (is-contr-map-is-equivᵉ (Hᵉ (truncᵉ kᵉ Aᵉ)) unit-truncᵉ)))
```

### A contractible type is `k`-connected for any `k`

```agda
module _
  {l1ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
  where

  is-connected-is-contrᵉ : is-contrᵉ Aᵉ → is-connectedᵉ kᵉ Aᵉ
  is-connected-is-contrᵉ Hᵉ =
    is-connected-is-equiv-diagonal-exponentialᵉ
      ( λ Bᵉ → is-equiv-diagonal-exponential-is-contrᵉ Hᵉ (type-Truncated-Typeᵉ Bᵉ))
```

### A type that is `(k+1)`-connected is `k`-connected

```agda
is-connected-is-connected-succ-𝕋ᵉ :
  {l1ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} →
  is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-connectedᵉ kᵉ Aᵉ
is-connected-is-connected-succ-𝕋ᵉ kᵉ Hᵉ =
  is-connected-is-equiv-diagonal-exponentialᵉ
    ( λ Bᵉ →
      is-equiv-diagonal-exponential-is-connectedᵉ
        ( truncated-type-succ-Truncated-Typeᵉ kᵉ Bᵉ)
        ( Hᵉ))
```

### The total space of a family of `k`-connected types over a `k`-connected type is `k`-connected

```agda
is-connected-Σᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  is-connectedᵉ kᵉ Aᵉ → ((xᵉ : Aᵉ) → is-connectedᵉ kᵉ (Bᵉ xᵉ)) →
  is-connectedᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
is-connected-Σᵉ kᵉ Hᵉ Kᵉ =
  is-contr-equivᵉ _ (equiv-truncᵉ kᵉ (equiv-pr1ᵉ Kᵉ) ∘eᵉ equiv-trunc-Σᵉ kᵉ) Hᵉ
```

### An inhabited type `A` is `k + 1`-connected if and only if its identity types are `k`-connected

```agda
module _
  {l1ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-inhabited-is-connectedᵉ :
      is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-inhabitedᵉ Aᵉ
    is-inhabited-is-connectedᵉ Hᵉ =
      map-universal-property-truncᵉ
        ( truncated-type-Propᵉ kᵉ (is-inhabited-Propᵉ Aᵉ))
        ( unit-trunc-Propᵉ)
        ( centerᵉ Hᵉ)

  abstract
    is-connected-eq-is-connectedᵉ :
      is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → {xᵉ yᵉ : Aᵉ} → is-connectedᵉ kᵉ (xᵉ ＝ᵉ yᵉ)
    is-connected-eq-is-connectedᵉ Hᵉ {xᵉ} {yᵉ} =
      is-contr-equivᵉ
        ( unit-truncᵉ xᵉ ＝ᵉ unit-truncᵉ yᵉ)
        ( effectiveness-truncᵉ kᵉ xᵉ yᵉ)
        ( is-prop-is-contrᵉ Hᵉ (unit-truncᵉ xᵉ) (unit-truncᵉ yᵉ))

  abstract
    is-connected-succ-is-connected-eqᵉ :
      is-inhabitedᵉ Aᵉ → ((xᵉ yᵉ : Aᵉ) → is-connectedᵉ kᵉ (xᵉ ＝ᵉ yᵉ)) →
      is-connectedᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
    is-connected-succ-is-connected-eqᵉ Hᵉ Kᵉ =
      apply-universal-property-trunc-Propᵉ Hᵉ
        ( is-connected-Propᵉ (succ-𝕋ᵉ kᵉ) Aᵉ)
        ( λ aᵉ →
          ( unit-truncᵉ aᵉ) ,ᵉ
          ( function-dependent-universal-property-truncᵉ
            ( Id-Truncated-Typeᵉ
              ( truncated-type-succ-Truncated-Typeᵉ
                ( succ-𝕋ᵉ kᵉ)
                ( truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ))
              ( unit-truncᵉ aᵉ))
            ( λ xᵉ →
              map-universal-property-truncᵉ
                ( Id-Truncated-Typeᵉ
                  ( truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ)
                  ( unit-truncᵉ aᵉ)
                  ( unit-truncᵉ xᵉ))
                ( λ where reflᵉ → reflᵉ)
                ( centerᵉ (Kᵉ aᵉ xᵉ)))))
```

### Being connected is invariant under equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-connected-is-equivᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-connectedᵉ kᵉ Bᵉ → is-connectedᵉ kᵉ Aᵉ
  is-connected-is-equivᵉ fᵉ eᵉ =
    is-contr-is-equivᵉ
      ( type-truncᵉ kᵉ Bᵉ)
      ( map-truncᵉ kᵉ fᵉ)
      ( is-equiv-map-equiv-truncᵉ kᵉ (fᵉ ,ᵉ eᵉ))

  is-connected-equivᵉ :
    Aᵉ ≃ᵉ Bᵉ → is-connectedᵉ kᵉ Bᵉ → is-connectedᵉ kᵉ Aᵉ
  is-connected-equivᵉ fᵉ =
    is-connected-is-equivᵉ (map-equivᵉ fᵉ) (is-equiv-map-equivᵉ fᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-connected-equiv'ᵉ :
    Aᵉ ≃ᵉ Bᵉ → is-connectedᵉ kᵉ Aᵉ → is-connectedᵉ kᵉ Bᵉ
  is-connected-equiv'ᵉ fᵉ = is-connected-equivᵉ (inv-equivᵉ fᵉ)

  is-connected-is-equiv'ᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ → is-connectedᵉ kᵉ Aᵉ → is-connectedᵉ kᵉ Bᵉ
  is-connected-is-equiv'ᵉ fᵉ eᵉ = is-connected-equiv'ᵉ (fᵉ ,ᵉ eᵉ)
```

### Retracts of `k`-connected types are `k`-connected

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-connected-retract-ofᵉ :
    Aᵉ retract-ofᵉ Bᵉ →
    is-connectedᵉ kᵉ Bᵉ →
    is-connectedᵉ kᵉ Aᵉ
  is-connected-retract-ofᵉ Rᵉ cᵉ =
    is-contr-retract-ofᵉ (type-truncᵉ kᵉ Bᵉ) (retract-of-trunc-retract-ofᵉ Rᵉ) cᵉ
```