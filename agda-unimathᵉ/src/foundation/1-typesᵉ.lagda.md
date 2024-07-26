# `1`-Types

```agda
module foundation.1-typesᵉ where

open import foundation-core.1-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.truncated-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

### Being a 1-type is a property

```agda
abstract
  is-prop-is-1-typeᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-1-typeᵉ Aᵉ)
  is-prop-is-1-typeᵉ Aᵉ = is-prop-is-truncᵉ one-𝕋ᵉ Aᵉ

is-1-type-Propᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-1-type-Propᵉ = is-trunc-Propᵉ one-𝕋ᵉ
```

### The type of all 1-types in a universe is a 2-type

```agda
is-trunc-1-Typeᵉ : {lᵉ : Level} → is-truncᵉ two-𝕋ᵉ (1-Typeᵉ lᵉ)
is-trunc-1-Typeᵉ = is-trunc-Truncated-Typeᵉ one-𝕋ᵉ

1-Type-Truncated-Typeᵉ : (lᵉ : Level) → Truncated-Typeᵉ (lsuc lᵉ) two-𝕋ᵉ
1-Type-Truncated-Typeᵉ lᵉ = Truncated-Type-Truncated-Typeᵉ lᵉ one-𝕋ᵉ
```

### Products of families of 1-types are 1-types

```agda
abstract
  is-1-type-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-1-typeᵉ (Bᵉ xᵉ)) → is-1-typeᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  is-1-type-Πᵉ = is-trunc-Πᵉ one-𝕋ᵉ

type-Π-1-Type'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → 1-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-1-Type'ᵉ Aᵉ Bᵉ = (xᵉ : Aᵉ) → type-1-Typeᵉ (Bᵉ xᵉ)

is-1-type-type-Π-1-Type'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → 1-Typeᵉ l2ᵉ) →
  is-1-typeᵉ (type-Π-1-Type'ᵉ Aᵉ Bᵉ)
is-1-type-type-Π-1-Type'ᵉ Aᵉ Bᵉ =
  is-1-type-Πᵉ (λ xᵉ → is-1-type-type-1-Typeᵉ (Bᵉ xᵉ))

Π-1-Type'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → 1-Typeᵉ l2ᵉ) → 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-1-Type'ᵉ Aᵉ Bᵉ) = type-Π-1-Type'ᵉ Aᵉ Bᵉ
pr2ᵉ (Π-1-Type'ᵉ Aᵉ Bᵉ) = is-1-type-type-Π-1-Type'ᵉ Aᵉ Bᵉ

type-Π-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : type-1-Typeᵉ Aᵉ → 1-Typeᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-1-Typeᵉ Aᵉ = type-Π-1-Type'ᵉ (type-1-Typeᵉ Aᵉ)

is-1-type-type-Π-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : type-1-Typeᵉ Aᵉ → 1-Typeᵉ l2ᵉ) →
  is-1-typeᵉ (type-Π-1-Typeᵉ Aᵉ Bᵉ)
is-1-type-type-Π-1-Typeᵉ Aᵉ = is-1-type-type-Π-1-Type'ᵉ (type-1-Typeᵉ Aᵉ)

Π-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : type-1-Typeᵉ Aᵉ → 1-Typeᵉ l2ᵉ) →
  1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
Π-1-Typeᵉ = Π-Truncated-Typeᵉ one-𝕋ᵉ
```

### The type of functions into a 1-type is a 1-type

```agda
abstract
  is-1-type-function-typeᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-1-typeᵉ Bᵉ → is-1-typeᵉ (Aᵉ → Bᵉ)
  is-1-type-function-typeᵉ = is-trunc-function-typeᵉ one-𝕋ᵉ

type-hom-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : 1-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-hom-1-Typeᵉ Aᵉ Bᵉ = type-1-Typeᵉ Aᵉ → type-1-Typeᵉ Bᵉ

is-1-type-type-hom-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : 1-Typeᵉ l2ᵉ) →
  is-1-typeᵉ (type-hom-1-Typeᵉ Aᵉ Bᵉ)
is-1-type-type-hom-1-Typeᵉ Aᵉ Bᵉ =
  is-1-type-function-typeᵉ (is-1-type-type-1-Typeᵉ Bᵉ)

hom-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : 1-Typeᵉ l2ᵉ) → 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
hom-1-Typeᵉ = hom-Truncated-Typeᵉ one-𝕋ᵉ
```

### 1-Types are closed under dependent pair types

```agda
abstract
  is-1-type-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-1-typeᵉ Aᵉ → ((xᵉ : Aᵉ) → is-1-typeᵉ (Bᵉ xᵉ)) → is-1-typeᵉ (Σᵉ Aᵉ Bᵉ)
  is-1-type-Σᵉ = is-trunc-Σᵉ {kᵉ = one-𝕋ᵉ}

Σ-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : pr1ᵉ Aᵉ → 1-Typeᵉ l2ᵉ) → 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
Σ-1-Typeᵉ = Σ-Truncated-Typeᵉ
```

### 1-Types are closed under cartesian product types

```agda
abstract
  is-1-type-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-1-typeᵉ Aᵉ → is-1-typeᵉ Bᵉ → is-1-typeᵉ (Aᵉ ×ᵉ Bᵉ)
  is-1-type-productᵉ = is-trunc-productᵉ one-𝕋ᵉ

product-1-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : 1-Typeᵉ l2ᵉ) → 1-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
product-1-Typeᵉ Aᵉ Bᵉ = Σ-1-Typeᵉ Aᵉ (λ xᵉ → Bᵉ)
```

### Subtypes of 1-types are 1-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-1-type-type-subtypeᵉ : is-1-typeᵉ Aᵉ → is-1-typeᵉ (type-subtypeᵉ Pᵉ)
    is-1-type-type-subtypeᵉ = is-trunc-type-subtypeᵉ zero-𝕋ᵉ Pᵉ
```

```agda
module _
  {lᵉ : Level} (Xᵉ : 1-Typeᵉ lᵉ)
  where

  type-equiv-1-Typeᵉ : {l2ᵉ : Level} (Yᵉ : 1-Typeᵉ l2ᵉ) → UUᵉ (lᵉ ⊔ l2ᵉ)
  type-equiv-1-Typeᵉ Yᵉ = type-1-Typeᵉ Xᵉ ≃ᵉ type-1-Typeᵉ Yᵉ

  equiv-eq-1-Typeᵉ : (Yᵉ : 1-Typeᵉ lᵉ) → Xᵉ ＝ᵉ Yᵉ → type-equiv-1-Typeᵉ Yᵉ
  equiv-eq-1-Typeᵉ = equiv-eq-subuniverseᵉ is-1-type-Propᵉ Xᵉ

  abstract
    is-torsorial-equiv-1-Typeᵉ :
      is-torsorialᵉ (λ (Yᵉ : 1-Typeᵉ lᵉ) → type-equiv-1-Typeᵉ Yᵉ)
    is-torsorial-equiv-1-Typeᵉ =
      is-torsorial-equiv-subuniverseᵉ is-1-type-Propᵉ Xᵉ

  abstract
    is-equiv-equiv-eq-1-Typeᵉ : (Yᵉ : 1-Typeᵉ lᵉ) → is-equivᵉ (equiv-eq-1-Typeᵉ Yᵉ)
    is-equiv-equiv-eq-1-Typeᵉ = is-equiv-equiv-eq-subuniverseᵉ is-1-type-Propᵉ Xᵉ

  extensionality-1-Typeᵉ :
    (Yᵉ : 1-Typeᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ type-equiv-1-Typeᵉ Yᵉ
  pr1ᵉ (extensionality-1-Typeᵉ Yᵉ) = equiv-eq-1-Typeᵉ Yᵉ
  pr2ᵉ (extensionality-1-Typeᵉ Yᵉ) = is-equiv-equiv-eq-1-Typeᵉ Yᵉ

  eq-equiv-1-Typeᵉ : (Yᵉ : 1-Typeᵉ lᵉ) → type-equiv-1-Typeᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-1-Typeᵉ Yᵉ = eq-equiv-subuniverseᵉ is-1-type-Propᵉ
```