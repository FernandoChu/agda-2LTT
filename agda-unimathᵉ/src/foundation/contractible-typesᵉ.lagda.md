# Contractible types

```agda
module foundation.contractible-typesᵉ where

open import foundation-core.contractible-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subuniversesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

### The proposition of being contractible

```agda
is-contr-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
pr1ᵉ (is-contr-Propᵉ Aᵉ) = is-contrᵉ Aᵉ
pr2ᵉ (is-contr-Propᵉ Aᵉ) = is-property-is-contrᵉ
```

### The subuniverse of contractible types

```agda
Contrᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Contrᵉ lᵉ = type-subuniverseᵉ is-contr-Propᵉ

type-Contrᵉ : {lᵉ : Level} → Contrᵉ lᵉ → UUᵉ lᵉ
type-Contrᵉ Aᵉ = pr1ᵉ Aᵉ

abstract
  is-contr-type-Contrᵉ :
    {lᵉ : Level} (Aᵉ : Contrᵉ lᵉ) → is-contrᵉ (type-Contrᵉ Aᵉ)
  is-contr-type-Contrᵉ Aᵉ = pr2ᵉ Aᵉ

equiv-Contrᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Contrᵉ l1ᵉ) (Yᵉ : Contrᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-Contrᵉ Xᵉ Yᵉ = type-Contrᵉ Xᵉ ≃ᵉ type-Contrᵉ Yᵉ

equiv-eq-Contrᵉ :
  {l1ᵉ : Level} (Xᵉ Yᵉ : Contrᵉ l1ᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-Contrᵉ Xᵉ Yᵉ
equiv-eq-Contrᵉ Xᵉ Yᵉ = equiv-eq-subuniverseᵉ is-contr-Propᵉ Xᵉ Yᵉ

abstract
  is-equiv-equiv-eq-Contrᵉ :
    {l1ᵉ : Level} (Xᵉ Yᵉ : Contrᵉ l1ᵉ) → is-equivᵉ (equiv-eq-Contrᵉ Xᵉ Yᵉ)
  is-equiv-equiv-eq-Contrᵉ Xᵉ Yᵉ =
    is-equiv-equiv-eq-subuniverseᵉ is-contr-Propᵉ Xᵉ Yᵉ

eq-equiv-Contrᵉ :
  {l1ᵉ : Level} {Xᵉ Yᵉ : Contrᵉ l1ᵉ} → equiv-Contrᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
eq-equiv-Contrᵉ = eq-equiv-subuniverseᵉ is-contr-Propᵉ

abstract
  center-Contrᵉ : (lᵉ : Level) → Contrᵉ lᵉ
  center-Contrᵉ lᵉ = pairᵉ (raise-unitᵉ lᵉ) is-contr-raise-unitᵉ

  contraction-Contrᵉ :
    {lᵉ : Level} (Aᵉ : Contrᵉ lᵉ) → center-Contrᵉ lᵉ ＝ᵉ Aᵉ
  contraction-Contrᵉ Aᵉ =
    eq-equiv-Contrᵉ
      ( equiv-is-contrᵉ is-contr-raise-unitᵉ (is-contr-type-Contrᵉ Aᵉ))

abstract
  is-contr-Contrᵉ : (lᵉ : Level) → is-contrᵉ (Contrᵉ lᵉ)
  is-contr-Contrᵉ lᵉ = pairᵉ (center-Contrᵉ lᵉ) contraction-Contrᵉ
```

### The predicate that a subuniverse contains any contractible types

```agda
contains-contractible-types-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} → subuniverseᵉ l1ᵉ l2ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
contains-contractible-types-subuniverseᵉ {l1ᵉ} Pᵉ =
  (Xᵉ : UUᵉ l1ᵉ) → is-contrᵉ Xᵉ → is-in-subuniverseᵉ Pᵉ Xᵉ
```

### The predicate that a subuniverse is closed under the `is-contr` predicate

Weᵉ stateᵉ aᵉ generalᵉ formᵉ involvingᵉ twoᵉ universes,ᵉ andᵉ aᵉ moreᵉ traditionalᵉ formᵉ
using aᵉ singleᵉ universeᵉ

```agda
is-closed-under-is-contr-subuniversesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l1ᵉ l3ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-closed-under-is-contr-subuniversesᵉ Pᵉ Qᵉ =
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ Qᵉ (is-contrᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))

is-closed-under-is-contr-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-closed-under-is-contr-subuniverseᵉ Pᵉ =
  is-closed-under-is-contr-subuniversesᵉ Pᵉ Pᵉ
```

## Properties

### If two types are equivalent then so are the propositions that they are contractible

```agda
equiv-is-contr-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → Aᵉ ≃ᵉ Bᵉ → is-contrᵉ Aᵉ ≃ᵉ is-contrᵉ Bᵉ
equiv-is-contr-equivᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} eᵉ =
  equiv-iff-is-propᵉ
    ( is-property-is-contrᵉ)
    ( is-property-is-contrᵉ)
    ( is-contr-retract-ofᵉ Aᵉ
      ( map-inv-equivᵉ eᵉ ,ᵉ map-equivᵉ eᵉ ,ᵉ is-section-map-inv-equivᵉ eᵉ))
    ( is-contr-retract-ofᵉ Bᵉ
      ( map-equivᵉ eᵉ ,ᵉ map-inv-equivᵉ eᵉ ,ᵉ is-retraction-map-inv-equivᵉ eᵉ))
```

### Contractible types are `k`-truncated for any `k`

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-trunc-is-contrᵉ : (kᵉ : 𝕋ᵉ) → is-contrᵉ Aᵉ → is-truncᵉ kᵉ Aᵉ
    is-trunc-is-contrᵉ neg-two-𝕋ᵉ is-contr-Aᵉ = is-contr-Aᵉ
    is-trunc-is-contrᵉ (succ-𝕋ᵉ kᵉ) is-contr-Aᵉ =
      is-trunc-succ-is-truncᵉ kᵉ (is-trunc-is-contrᵉ kᵉ is-contr-Aᵉ)
```

### Contractibility of Σ-types where the dependent type is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ)
  where

  is-contr-Σ-is-propᵉ :
    ((xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)) → ((xᵉ : Aᵉ) → Bᵉ xᵉ → aᵉ ＝ᵉ xᵉ) → is-contrᵉ (Σᵉ Aᵉ Bᵉ)
  pr1ᵉ (is-contr-Σ-is-propᵉ pᵉ fᵉ) = pairᵉ aᵉ bᵉ
  pr2ᵉ (is-contr-Σ-is-propᵉ pᵉ fᵉ) (pairᵉ xᵉ yᵉ) =
    eq-type-subtypeᵉ
      ( λ x'ᵉ → pairᵉ (Bᵉ x'ᵉ) (pᵉ x'ᵉ))
      ( fᵉ xᵉ yᵉ)
```

### The diagonal of contractible types

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponentialᵉ :
      ({lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ)) →
      is-equivᵉ (diagonal-exponentialᵉ Aᵉ Aᵉ)
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponentialᵉ Hᵉ = Hᵉ Aᵉ

  abstract
    is-contr-is-equiv-self-diagonal-exponentialᵉ :
      is-equivᵉ (diagonal-exponentialᵉ Aᵉ Aᵉ) → is-contrᵉ Aᵉ
    is-contr-is-equiv-self-diagonal-exponentialᵉ Hᵉ =
      totᵉ (λ xᵉ → htpy-eqᵉ) (centerᵉ (is-contr-map-is-equivᵉ Hᵉ idᵉ))

  abstract
    is-contr-is-equiv-diagonal-exponentialᵉ :
      ({lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ)) →
      is-contrᵉ Aᵉ
    is-contr-is-equiv-diagonal-exponentialᵉ Hᵉ =
      is-contr-is-equiv-self-diagonal-exponentialᵉ
        ( is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponentialᵉ Hᵉ)

  abstract
    is-equiv-diagonal-exponential-is-contrᵉ :
      is-contrᵉ Aᵉ →
      {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (diagonal-exponentialᵉ Xᵉ Aᵉ)
    is-equiv-diagonal-exponential-is-contrᵉ Hᵉ Xᵉ =
      is-equiv-is-invertibleᵉ
        ( ev-point'ᵉ (centerᵉ Hᵉ))
        ( λ fᵉ → eq-htpyᵉ (λ xᵉ → apᵉ fᵉ (contractionᵉ Hᵉ xᵉ)))
        ( λ xᵉ → reflᵉ)

  equiv-diagonal-exponential-is-contrᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-contrᵉ Aᵉ → Xᵉ ≃ᵉ (Aᵉ → Xᵉ)
  pr1ᵉ (equiv-diagonal-exponential-is-contrᵉ Xᵉ Hᵉ) =
    diagonal-exponentialᵉ Xᵉ Aᵉ
  pr2ᵉ (equiv-diagonal-exponential-is-contrᵉ Xᵉ Hᵉ) =
    is-equiv-diagonal-exponential-is-contrᵉ Hᵉ Xᵉ
```