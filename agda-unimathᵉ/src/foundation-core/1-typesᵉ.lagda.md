# `1`-Types

```agda
module foundation-core.1-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.truncated-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

Aᵉ 1-typeᵉ isᵉ aᵉ typeᵉ thatᵉ isᵉ 1-truncated.ᵉ

```agda
is-1-typeᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-1-typeᵉ = is-truncᵉ one-𝕋ᵉ

1-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
1-Typeᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-1-typeᵉ

type-1-Typeᵉ : {lᵉ : Level} → 1-Typeᵉ lᵉ → UUᵉ lᵉ
type-1-Typeᵉ = pr1ᵉ

abstract
  is-1-type-type-1-Typeᵉ :
    {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) → is-1-typeᵉ (type-1-Typeᵉ Aᵉ)
  is-1-type-type-1-Typeᵉ = pr2ᵉ
```

## Properties

### The identity type of a 1-type takes values in sets

```agda
Id-Setᵉ : {lᵉ : Level} (Xᵉ : 1-Typeᵉ lᵉ) (xᵉ yᵉ : type-1-Typeᵉ Xᵉ) → Setᵉ lᵉ
pr1ᵉ (Id-Setᵉ Xᵉ xᵉ yᵉ) = (xᵉ ＝ᵉ yᵉ)
pr2ᵉ (Id-Setᵉ Xᵉ xᵉ yᵉ) = is-1-type-type-1-Typeᵉ Xᵉ xᵉ yᵉ
```

### Any set is a 1-type

```agda
abstract
  is-1-type-is-setᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ → is-1-typeᵉ Aᵉ
  is-1-type-is-setᵉ = is-trunc-succ-is-truncᵉ zero-𝕋ᵉ

1-type-Setᵉ :
  {lᵉ : Level} → Setᵉ lᵉ → 1-Typeᵉ lᵉ
1-type-Setᵉ = truncated-type-succ-Truncated-Typeᵉ zero-𝕋ᵉ
```

### Any proposition is a 1-type

```agda
abstract
  is-1-type-is-propᵉ :
    {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → is-propᵉ Pᵉ → is-1-typeᵉ Pᵉ
  is-1-type-is-propᵉ = is-trunc-iterated-succ-is-truncᵉ neg-one-𝕋ᵉ 2

1-type-Propᵉ :
  {lᵉ : Level} → Propᵉ lᵉ → 1-Typeᵉ lᵉ
1-type-Propᵉ Pᵉ = truncated-type-iterated-succ-Truncated-Typeᵉ neg-one-𝕋ᵉ 2 Pᵉ
```

### Any contractible type is a 1-type

```agda
abstract
  is-1-type-is-contrᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → is-1-typeᵉ Aᵉ
  is-1-type-is-contrᵉ = is-trunc-is-contrᵉ one-𝕋ᵉ
```

### The 1-types are closed under equivalences

```agda
abstract
  is-1-type-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ →
    is-1-typeᵉ Bᵉ → is-1-typeᵉ Aᵉ
  is-1-type-is-equivᵉ = is-trunc-is-equivᵉ one-𝕋ᵉ

abstract
  is-1-type-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-1-typeᵉ Bᵉ → is-1-typeᵉ Aᵉ
  is-1-type-equivᵉ = is-trunc-equivᵉ one-𝕋ᵉ

abstract
  is-1-type-is-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ fᵉ → is-1-typeᵉ Aᵉ → is-1-typeᵉ Bᵉ
  is-1-type-is-equiv'ᵉ = is-trunc-is-equiv'ᵉ one-𝕋ᵉ

abstract
  is-1-type-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-1-typeᵉ Aᵉ → is-1-typeᵉ Bᵉ
  is-1-type-equiv'ᵉ = is-trunc-equiv'ᵉ one-𝕋ᵉ
```