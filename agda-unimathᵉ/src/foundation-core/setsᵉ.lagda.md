# Sets

```agda
module foundation-core.setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ aᵉ setᵉ ifᵉ itsᵉ identityᵉ typesᵉ areᵉ propositions.ᵉ

## Definition

```agda
is-setᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-setᵉ Aᵉ = (xᵉ yᵉ : Aᵉ) → is-propᵉ (xᵉ ＝ᵉ yᵉ)

Setᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Setᵉ lᵉ = Σᵉ (UUᵉ lᵉ) is-setᵉ

module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  type-Setᵉ : UUᵉ lᵉ
  type-Setᵉ = pr1ᵉ Xᵉ

  abstract
    is-set-type-Setᵉ : is-setᵉ type-Setᵉ
    is-set-type-Setᵉ = pr2ᵉ Xᵉ

  Id-Propᵉ : (xᵉ yᵉ : type-Setᵉ) → Propᵉ lᵉ
  Id-Propᵉ xᵉ yᵉ = (xᵉ ＝ᵉ yᵉ ,ᵉ is-set-type-Setᵉ xᵉ yᵉ)
```

## Properties

### A type is a set if and only if it satisfies Streicher's axiom K

```agda
instance-axiom-Kᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
instance-axiom-Kᵉ Aᵉ = (xᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ xᵉ) → reflᵉ ＝ᵉ pᵉ

axiom-K-Levelᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
axiom-K-Levelᵉ lᵉ = (Aᵉ : UUᵉ lᵉ) → instance-axiom-Kᵉ Aᵉ

axiom-Kᵉ : UUωᵉ
axiom-Kᵉ = {lᵉ : Level} → axiom-K-Levelᵉ lᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-set-axiom-K'ᵉ :
      instance-axiom-Kᵉ Aᵉ → (xᵉ yᵉ : Aᵉ) → all-elements-equalᵉ (xᵉ ＝ᵉ yᵉ)
    is-set-axiom-K'ᵉ Kᵉ xᵉ .xᵉ reflᵉ qᵉ with Kᵉ xᵉ qᵉ
    ... | reflᵉ = reflᵉ

  abstract
    is-set-axiom-Kᵉ : instance-axiom-Kᵉ Aᵉ → is-setᵉ Aᵉ
    is-set-axiom-Kᵉ Hᵉ xᵉ yᵉ = is-prop-all-elements-equalᵉ (is-set-axiom-K'ᵉ Hᵉ xᵉ yᵉ)

  abstract
    axiom-K-is-setᵉ : is-setᵉ Aᵉ → instance-axiom-Kᵉ Aᵉ
    axiom-K-is-setᵉ Hᵉ xᵉ pᵉ =
      ( invᵉ (contractionᵉ (is-proof-irrelevant-is-propᵉ (Hᵉ xᵉ xᵉ) reflᵉ) reflᵉ)) ∙ᵉ
      ( contractionᵉ (is-proof-irrelevant-is-propᵉ (Hᵉ xᵉ xᵉ) reflᵉ) pᵉ)
```

### If a reflexive binary relation maps into the identity type of `A`, then `A` is a set

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Aᵉ → Aᵉ → UUᵉ l2ᵉ)
  (pᵉ : (xᵉ yᵉ : Aᵉ) → is-propᵉ (Rᵉ xᵉ yᵉ)) (ρᵉ : (xᵉ : Aᵉ) → Rᵉ xᵉ xᵉ)
  (iᵉ : (xᵉ yᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ)
  where

  abstract
    is-equiv-prop-in-idᵉ : (xᵉ yᵉ : Aᵉ) → is-equivᵉ (iᵉ xᵉ yᵉ)
    is-equiv-prop-in-idᵉ xᵉ =
      fundamental-theorem-id-retractionᵉ xᵉ (iᵉ xᵉ)
        ( λ yᵉ →
          pairᵉ
            ( ind-Idᵉ xᵉ (λ zᵉ pᵉ → Rᵉ xᵉ zᵉ) (ρᵉ xᵉ) yᵉ)
            ( λ rᵉ → eq-is-propᵉ (pᵉ xᵉ yᵉ)))

  abstract
    is-set-prop-in-idᵉ : is-setᵉ Aᵉ
    is-set-prop-in-idᵉ xᵉ yᵉ = is-prop-is-equiv'ᵉ (is-equiv-prop-in-idᵉ xᵉ yᵉ) (pᵉ xᵉ yᵉ)
```

### Any proposition is a set

```agda
abstract
  is-set-is-propᵉ :
    {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → is-propᵉ Pᵉ → is-setᵉ Pᵉ
  is-set-is-propᵉ = is-trunc-succ-is-truncᵉ neg-one-𝕋ᵉ

set-Propᵉ :
  {lᵉ : Level} → Propᵉ lᵉ → Setᵉ lᵉ
set-Propᵉ Pᵉ = truncated-type-succ-Truncated-Typeᵉ neg-one-𝕋ᵉ Pᵉ
```

### Sets are closed under equivalences

```agda
abstract
  is-set-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ →
    is-setᵉ Bᵉ → is-setᵉ Aᵉ
  is-set-is-equivᵉ = is-trunc-is-equivᵉ zero-𝕋ᵉ

abstract
  is-set-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-setᵉ Bᵉ → is-setᵉ Aᵉ
  is-set-equivᵉ = is-trunc-equivᵉ zero-𝕋ᵉ

abstract
  is-set-is-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ →
    is-setᵉ Aᵉ → is-setᵉ Bᵉ
  is-set-is-equiv'ᵉ = is-trunc-is-equiv'ᵉ zero-𝕋ᵉ

abstract
  is-set-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-setᵉ Aᵉ → is-setᵉ Bᵉ
  is-set-equiv'ᵉ = is-trunc-equiv'ᵉ zero-𝕋ᵉ

abstract
  is-set-equiv-is-setᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → is-setᵉ Bᵉ → is-setᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-set-equiv-is-setᵉ = is-trunc-equiv-is-truncᵉ zero-𝕋ᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : Setᵉ l2ᵉ)
  where

  equiv-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Setᵉ = type-Setᵉ Aᵉ ≃ᵉ type-Setᵉ Bᵉ

  equiv-set-Setᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ equiv-set-Setᵉ = equiv-Setᵉ
  pr2ᵉ equiv-set-Setᵉ =
    is-set-equiv-is-setᵉ (is-set-type-Setᵉ Aᵉ) (is-set-type-Setᵉ Bᵉ)
```

### If a type injects into a set, then it is a set

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-set-is-injectiveᵉ :
      {fᵉ : Aᵉ → Bᵉ} → is-setᵉ Bᵉ → is-injectiveᵉ fᵉ → is-setᵉ Aᵉ
    is-set-is-injectiveᵉ {fᵉ} Hᵉ Iᵉ =
      is-set-prop-in-idᵉ
        ( λ xᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ yᵉ)
        ( λ xᵉ yᵉ → Hᵉ (fᵉ xᵉ) (fᵉ yᵉ))
        ( λ xᵉ → reflᵉ)
        ( λ xᵉ yᵉ → Iᵉ)
```