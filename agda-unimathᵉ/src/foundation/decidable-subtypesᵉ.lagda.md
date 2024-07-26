# Decidable subtypes

```agda
module foundation.decidable-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ decidableᵉ subtypeᵉ ofᵉ aᵉ typeᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ decidableᵉ propositionsᵉ
overᵉ it.ᵉ

## Definitions

### Decidable subtypes

```agda
is-decidable-subtype-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-subtype-Propᵉ {Aᵉ = Aᵉ} Pᵉ =
  Π-Propᵉ Aᵉ (λ aᵉ → is-decidable-Propᵉ (Pᵉ aᵉ))

is-decidable-subtypeᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → subtypeᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-subtypeᵉ Pᵉ = type-Propᵉ (is-decidable-subtype-Propᵉ Pᵉ)

is-prop-is-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ) →
  is-propᵉ (is-decidable-subtypeᵉ Pᵉ)
is-prop-is-decidable-subtypeᵉ Pᵉ = is-prop-type-Propᵉ (is-decidable-subtype-Propᵉ Pᵉ)

decidable-subtypeᵉ : {l1ᵉ : Level} (lᵉ : Level) (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
decidable-subtypeᵉ lᵉ Xᵉ = Xᵉ → Decidable-Propᵉ lᵉ
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ)
  where

  subtype-decidable-subtypeᵉ : subtypeᵉ l2ᵉ Aᵉ
  subtype-decidable-subtypeᵉ aᵉ = prop-Decidable-Propᵉ (Pᵉ aᵉ)

  is-decidable-decidable-subtypeᵉ :
    is-decidable-subtypeᵉ subtype-decidable-subtypeᵉ
  is-decidable-decidable-subtypeᵉ aᵉ =
    is-decidable-Decidable-Propᵉ (Pᵉ aᵉ)

  is-in-decidable-subtypeᵉ : Aᵉ → UUᵉ l2ᵉ
  is-in-decidable-subtypeᵉ = is-in-subtypeᵉ subtype-decidable-subtypeᵉ

  is-prop-is-in-decidable-subtypeᵉ :
    (aᵉ : Aᵉ) → is-propᵉ (is-in-decidable-subtypeᵉ aᵉ)
  is-prop-is-in-decidable-subtypeᵉ =
    is-prop-is-in-subtypeᵉ subtype-decidable-subtypeᵉ
```

### The underlying type of a decidable subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ)
  where

  type-decidable-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-decidable-subtypeᵉ = type-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  inclusion-decidable-subtypeᵉ : type-decidable-subtypeᵉ → Aᵉ
  inclusion-decidable-subtypeᵉ = inclusion-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  is-emb-inclusion-decidable-subtypeᵉ : is-embᵉ inclusion-decidable-subtypeᵉ
  is-emb-inclusion-decidable-subtypeᵉ =
    is-emb-inclusion-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  is-injective-inclusion-decidable-subtypeᵉ :
    is-injectiveᵉ inclusion-decidable-subtypeᵉ
  is-injective-inclusion-decidable-subtypeᵉ =
    is-injective-inclusion-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  emb-decidable-subtypeᵉ : type-decidable-subtypeᵉ ↪ᵉ Aᵉ
  emb-decidable-subtypeᵉ = emb-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)
```

## Examples

### The decidable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-decidable-is-leftᵉ : (xᵉ : Aᵉ +ᵉ Bᵉ) → is-decidableᵉ (is-leftᵉ xᵉ)
  is-decidable-is-leftᵉ (inlᵉ xᵉ) = is-decidable-unitᵉ
  is-decidable-is-leftᵉ (inrᵉ xᵉ) = is-decidable-emptyᵉ

  is-left-Decidable-Propᵉ : Aᵉ +ᵉ Bᵉ → Decidable-Propᵉ lzero
  pr1ᵉ (is-left-Decidable-Propᵉ xᵉ) = is-leftᵉ xᵉ
  pr1ᵉ (pr2ᵉ (is-left-Decidable-Propᵉ xᵉ)) = is-prop-is-leftᵉ xᵉ
  pr2ᵉ (pr2ᵉ (is-left-Decidable-Propᵉ xᵉ)) = is-decidable-is-leftᵉ xᵉ

  is-decidable-is-rightᵉ : (xᵉ : Aᵉ +ᵉ Bᵉ) → is-decidableᵉ (is-rightᵉ xᵉ)
  is-decidable-is-rightᵉ (inlᵉ xᵉ) = is-decidable-emptyᵉ
  is-decidable-is-rightᵉ (inrᵉ xᵉ) = is-decidable-unitᵉ

  is-right-Decidable-Propᵉ : Aᵉ +ᵉ Bᵉ → Decidable-Propᵉ lzero
  pr1ᵉ (is-right-Decidable-Propᵉ xᵉ) = is-rightᵉ xᵉ
  pr1ᵉ (pr2ᵉ (is-right-Decidable-Propᵉ xᵉ)) = is-prop-is-rightᵉ xᵉ
  pr2ᵉ (pr2ᵉ (is-right-Decidable-Propᵉ xᵉ)) = is-decidable-is-rightᵉ xᵉ
```

## Properties

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ)
  where

  equiv-universes-decidable-subtypeᵉ :
    (lᵉ l'ᵉ : Level) → decidable-subtypeᵉ lᵉ Xᵉ ≃ᵉ decidable-subtypeᵉ l'ᵉ Xᵉ
  equiv-universes-decidable-subtypeᵉ lᵉ l'ᵉ =
    equiv-Πᵉ
      ( λ _ → Decidable-Propᵉ l'ᵉ)
      ( id-equivᵉ)
      ( λ _ → equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ)

  iff-universes-decidable-subtypeᵉ :
    (lᵉ l'ᵉ : Level) (Sᵉ : decidable-subtypeᵉ lᵉ Xᵉ) →
    ( (xᵉ : Xᵉ) →
      type-Decidable-Propᵉ (Sᵉ xᵉ) ↔ᵉ
      type-Decidable-Propᵉ
        ( map-equivᵉ (equiv-universes-decidable-subtypeᵉ lᵉ l'ᵉ) Sᵉ xᵉ))
  iff-universes-decidable-subtypeᵉ lᵉ l'ᵉ Sᵉ xᵉ =
    trᵉ
      ( λ Pᵉ → type-Decidable-Propᵉ (Sᵉ xᵉ) ↔ᵉ type-Decidable-Propᵉ Pᵉ)
      ( invᵉ
        ( compute-map-equiv-Πᵉ
          ( λ _ → Decidable-Propᵉ l'ᵉ)
          ( id-equivᵉ)
          ( λ _ → equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ)
          ( Sᵉ)
          ( xᵉ)))
      ( iff-universes-Decidable-Propᵉ lᵉ l'ᵉ (Sᵉ xᵉ))
```

### A decidable subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-trunc-type-decidable-subtypeᵉ :
      is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (type-decidable-subtypeᵉ Pᵉ)
    is-trunc-type-decidable-subtypeᵉ =
      is-trunc-type-subtypeᵉ kᵉ (subtype-decidable-subtypeᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ)
  where

  abstract
    is-prop-type-decidable-subtypeᵉ :
      is-propᵉ Aᵉ → is-propᵉ (type-decidable-subtypeᵉ Pᵉ)
    is-prop-type-decidable-subtypeᵉ =
      is-prop-type-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  abstract
    is-set-type-decidable-subtypeᵉ : is-setᵉ Aᵉ → is-setᵉ (type-decidable-subtypeᵉ Pᵉ)
    is-set-type-decidable-subtypeᵉ =
      is-set-type-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

  abstract
    is-1-type-type-decidable-subtypeᵉ :
      is-1-typeᵉ Aᵉ → is-1-typeᵉ (type-decidable-subtypeᵉ Pᵉ)
    is-1-type-type-decidable-subtypeᵉ =
      is-1-type-type-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)

prop-decidable-subpropᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Propᵉ l1ᵉ) (Pᵉ : decidable-subtypeᵉ l2ᵉ (type-Propᵉ Aᵉ)) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ)
prop-decidable-subpropᵉ Aᵉ Pᵉ = prop-subpropᵉ Aᵉ (subtype-decidable-subtypeᵉ Pᵉ)

set-decidable-subsetᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Pᵉ : decidable-subtypeᵉ l2ᵉ (type-Setᵉ Aᵉ)) →
  Setᵉ (l1ᵉ ⊔ l2ᵉ)
set-decidable-subsetᵉ Aᵉ Pᵉ = set-subsetᵉ Aᵉ (subtype-decidable-subtypeᵉ Pᵉ)
```

### The type of decidable subtypes of a type is a set

```agda
is-set-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} → is-setᵉ (decidable-subtypeᵉ l2ᵉ Xᵉ)
is-set-decidable-subtypeᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} =
  is-set-function-typeᵉ is-set-Decidable-Propᵉ
```

### Extensionality of the type of decidable subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ)
  where

  has-same-elements-decidable-subtypeᵉ :
    {l3ᵉ : Level} → decidable-subtypeᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-decidable-subtypeᵉ Qᵉ =
    has-same-elements-subtypeᵉ
      ( subtype-decidable-subtypeᵉ Pᵉ)
      ( subtype-decidable-subtypeᵉ Qᵉ)

  extensionality-decidable-subtypeᵉ :
    (Qᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ) →
    (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ has-same-elements-decidable-subtypeᵉ Qᵉ
  extensionality-decidable-subtypeᵉ =
    extensionality-Πᵉ Pᵉ
      ( λ xᵉ Qᵉ → (type-Decidable-Propᵉ (Pᵉ xᵉ)) ↔ᵉ (type-Decidable-Propᵉ Qᵉ))
      ( λ xᵉ Qᵉ → extensionality-Decidable-Propᵉ (Pᵉ xᵉ) Qᵉ)

  has-same-elements-eq-decidable-subtypeᵉ :
    (Qᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ) →
    (Pᵉ ＝ᵉ Qᵉ) → has-same-elements-decidable-subtypeᵉ Qᵉ
  has-same-elements-eq-decidable-subtypeᵉ Qᵉ =
    map-equivᵉ (extensionality-decidable-subtypeᵉ Qᵉ)

  eq-has-same-elements-decidable-subtypeᵉ :
    (Qᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ) →
    has-same-elements-decidable-subtypeᵉ Qᵉ → Pᵉ ＝ᵉ Qᵉ
  eq-has-same-elements-decidable-subtypeᵉ Qᵉ =
    map-inv-equivᵉ (extensionality-decidable-subtypeᵉ Qᵉ)

  refl-extensionality-decidable-subtypeᵉ :
    map-equivᵉ (extensionality-decidable-subtypeᵉ Pᵉ) reflᵉ ＝ᵉ (λ xᵉ → pairᵉ idᵉ idᵉ)
  refl-extensionality-decidable-subtypeᵉ = reflᵉ
```