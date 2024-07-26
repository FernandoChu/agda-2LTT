# The unit type

```agda
module foundation.unit-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ **unitᵉ type**ᵉ isᵉ aᵉ typeᵉ inductivelyᵉ generatedᵉ byᵉ aᵉ singleᵉ point.ᵉ

## Definition

### The unit type

```agda
record unitᵉ : UUᵉ lzero where
  instance constructor starᵉ


```

### The induction principle of the unit type

```agda
ind-unitᵉ : {lᵉ : Level} {Pᵉ : unitᵉ → UUᵉ lᵉ} → Pᵉ starᵉ → (xᵉ : unitᵉ) → Pᵉ xᵉ
ind-unitᵉ pᵉ starᵉ = pᵉ
```

### The terminal map out of a type

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  terminal-mapᵉ : Aᵉ → unitᵉ
  terminal-mapᵉ = constᵉ Aᵉ starᵉ
```

### Points as maps out of the unit type

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  pointᵉ : Aᵉ → (unitᵉ → Aᵉ)
  pointᵉ = diagonal-exponentialᵉ Aᵉ unitᵉ
```

### Raising the universe level of the unit type

```agda
raise-unitᵉ : (lᵉ : Level) → UUᵉ lᵉ
raise-unitᵉ lᵉ = raiseᵉ lᵉ unitᵉ

raise-starᵉ : {lᵉ : Level} → raiseᵉ lᵉ unitᵉ
raise-starᵉ = map-raiseᵉ starᵉ

raise-terminal-mapᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Aᵉ → raise-unitᵉ l2ᵉ
raise-terminal-mapᵉ {l2ᵉ = l2ᵉ} Aᵉ = constᵉ Aᵉ raise-starᵉ

compute-raise-unitᵉ : (lᵉ : Level) → unitᵉ ≃ᵉ raise-unitᵉ lᵉ
compute-raise-unitᵉ lᵉ = compute-raiseᵉ lᵉ unitᵉ
```

## Properties

### The unit type is contractible

```agda
abstract
  is-contr-unitᵉ : is-contrᵉ unitᵉ
  pr1ᵉ is-contr-unitᵉ = starᵉ
  pr2ᵉ is-contr-unitᵉ starᵉ = reflᵉ
```

### Any contractible type is equivalent to the unit type

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-equiv-terminal-map-is-contrᵉ :
      is-contrᵉ Aᵉ → is-equivᵉ (terminal-mapᵉ Aᵉ)
    pr1ᵉ (pr1ᵉ (is-equiv-terminal-map-is-contrᵉ Hᵉ)) = ind-unitᵉ (centerᵉ Hᵉ)
    pr2ᵉ (pr1ᵉ (is-equiv-terminal-map-is-contrᵉ Hᵉ)) = ind-unitᵉ reflᵉ
    pr1ᵉ (pr2ᵉ (is-equiv-terminal-map-is-contrᵉ Hᵉ)) xᵉ = centerᵉ Hᵉ
    pr2ᵉ (pr2ᵉ (is-equiv-terminal-map-is-contrᵉ Hᵉ)) = contractionᵉ Hᵉ

  equiv-unit-is-contrᵉ : is-contrᵉ Aᵉ → Aᵉ ≃ᵉ unitᵉ
  pr1ᵉ (equiv-unit-is-contrᵉ Hᵉ) = terminal-mapᵉ Aᵉ
  pr2ᵉ (equiv-unit-is-contrᵉ Hᵉ) = is-equiv-terminal-map-is-contrᵉ Hᵉ

  abstract
    is-contr-is-equiv-constᵉ : is-equivᵉ (terminal-mapᵉ Aᵉ) → is-contrᵉ Aᵉ
    pr1ᵉ (is-contr-is-equiv-constᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ (hᵉ ,ᵉ Hᵉ))) = hᵉ starᵉ
    pr2ᵉ (is-contr-is-equiv-constᵉ ((gᵉ ,ᵉ Gᵉ) ,ᵉ (hᵉ ,ᵉ Hᵉ))) = Hᵉ
```

### The unit type is a proposition

```agda
abstract
  is-prop-unitᵉ : is-propᵉ unitᵉ
  is-prop-unitᵉ = is-prop-is-contrᵉ is-contr-unitᵉ

unit-Propᵉ : Propᵉ lzero
pr1ᵉ unit-Propᵉ = unitᵉ
pr2ᵉ unit-Propᵉ = is-prop-unitᵉ
```

### The unit type is a set

```agda
abstract
  is-set-unitᵉ : is-setᵉ unitᵉ
  is-set-unitᵉ = is-trunc-succ-is-truncᵉ neg-one-𝕋ᵉ is-prop-unitᵉ

unit-Setᵉ : Setᵉ lzero
pr1ᵉ unit-Setᵉ = unitᵉ
pr2ᵉ unit-Setᵉ = is-set-unitᵉ
```

```agda
abstract
  is-contr-raise-unitᵉ :
    {l1ᵉ : Level} → is-contrᵉ (raise-unitᵉ l1ᵉ)
  is-contr-raise-unitᵉ {l1ᵉ} =
    is-contr-equiv'ᵉ unitᵉ (compute-raiseᵉ l1ᵉ unitᵉ) is-contr-unitᵉ

abstract
  is-prop-raise-unitᵉ :
    {l1ᵉ : Level} → is-propᵉ (raise-unitᵉ l1ᵉ)
  is-prop-raise-unitᵉ {l1ᵉ} =
    is-prop-equiv'ᵉ (compute-raiseᵉ l1ᵉ unitᵉ) is-prop-unitᵉ

raise-unit-Propᵉ :
  (l1ᵉ : Level) → Propᵉ l1ᵉ
pr1ᵉ (raise-unit-Propᵉ l1ᵉ) = raise-unitᵉ l1ᵉ
pr2ᵉ (raise-unit-Propᵉ l1ᵉ) = is-prop-raise-unitᵉ

abstract
  is-set-raise-unitᵉ :
    {l1ᵉ : Level} → is-setᵉ (raise-unitᵉ l1ᵉ)
  is-set-raise-unitᵉ = is-trunc-succ-is-truncᵉ neg-one-𝕋ᵉ is-prop-raise-unitᵉ

raise-unit-Setᵉ : Setᵉ lzero
pr1ᵉ raise-unit-Setᵉ = unitᵉ
pr2ᵉ raise-unit-Setᵉ = is-set-unitᵉ
```

### All parallel maps into `unit` are equal

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ gᵉ : Aᵉ → unitᵉ}
  where

  eq-map-into-unitᵉ : fᵉ ＝ᵉ gᵉ
  eq-map-into-unitᵉ = reflᵉ
```

### The map `point x` is injective for every `x`

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (xᵉ : Aᵉ)
  where

  is-injective-pointᵉ : is-injectiveᵉ (pointᵉ xᵉ)
  is-injective-pointᵉ _ = reflᵉ

  point-injectionᵉ : injectionᵉ unitᵉ Aᵉ
  pr1ᵉ point-injectionᵉ = pointᵉ xᵉ
  pr2ᵉ point-injectionᵉ = is-injective-pointᵉ
```