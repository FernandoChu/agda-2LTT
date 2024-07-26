# Truncated types

```agda
module foundation.truncated-typesᵉ where

open import foundation-core.truncated-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.truncation-levelsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Definition

### The subuniverse of truncated types is itself truncated

```agda
is-torsorial-equiv-Truncated-Typeᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
  is-torsorialᵉ (type-equiv-Truncated-Typeᵉ Aᵉ)
is-torsorial-equiv-Truncated-Typeᵉ Aᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-equivᵉ (type-Truncated-Typeᵉ Aᵉ))
    ( is-prop-is-truncᵉ _)
    ( type-Truncated-Typeᵉ Aᵉ)
    ( id-equivᵉ)
    ( is-trunc-type-Truncated-Typeᵉ Aᵉ)

extensionality-Truncated-Typeᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ Bᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
  (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ
extensionality-Truncated-Typeᵉ Aᵉ =
  extensionality-type-subtypeᵉ
    ( is-trunc-Propᵉ _)
    ( is-trunc-type-Truncated-Typeᵉ Aᵉ)
    ( id-equivᵉ)
    ( λ Xᵉ → equiv-univalenceᵉ)

abstract
  is-trunc-Truncated-Typeᵉ :
    {lᵉ : Level} (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) (Truncated-Typeᵉ lᵉ kᵉ)
  is-trunc-Truncated-Typeᵉ kᵉ Xᵉ Yᵉ =
    is-trunc-equivᵉ kᵉ
      ( type-equiv-Truncated-Typeᵉ Xᵉ Yᵉ)
      ( extensionality-Truncated-Typeᵉ Xᵉ Yᵉ)
      ( is-trunc-type-equiv-Truncated-Typeᵉ Xᵉ Yᵉ)

Truncated-Type-Truncated-Typeᵉ :
  (lᵉ : Level) (kᵉ : 𝕋ᵉ) → Truncated-Typeᵉ (lsuc lᵉ) (succ-𝕋ᵉ kᵉ)
pr1ᵉ (Truncated-Type-Truncated-Typeᵉ lᵉ kᵉ) = Truncated-Typeᵉ lᵉ kᵉ
pr2ᵉ (Truncated-Type-Truncated-Typeᵉ lᵉ kᵉ) = is-trunc-Truncated-Typeᵉ kᵉ
```

### The embedding of the subuniverse of truncated types into the universe

```agda
emb-type-Truncated-Typeᵉ : (lᵉ : Level) (kᵉ : 𝕋ᵉ) → Truncated-Typeᵉ lᵉ kᵉ ↪ᵉ UUᵉ lᵉ
emb-type-Truncated-Typeᵉ lᵉ kᵉ = emb-subtypeᵉ (is-trunc-Propᵉ kᵉ)
```

### If a type is `k`-truncated, then it is `k+r`-truncated

```agda
abstract
  is-trunc-iterated-succ-is-truncᵉ :
    (kᵉ : 𝕋ᵉ) (rᵉ : ℕᵉ) {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ (iterated-succ-𝕋'ᵉ kᵉ rᵉ) Aᵉ
  is-trunc-iterated-succ-is-truncᵉ kᵉ zero-ℕᵉ is-trunc-Aᵉ = is-trunc-Aᵉ
  is-trunc-iterated-succ-is-truncᵉ kᵉ (succ-ℕᵉ rᵉ) is-trunc-Aᵉ =
    is-trunc-iterated-succ-is-truncᵉ (succ-𝕋ᵉ kᵉ) rᵉ
      ( is-trunc-succ-is-truncᵉ kᵉ is-trunc-Aᵉ)

truncated-type-iterated-succ-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) (rᵉ : ℕᵉ) {lᵉ : Level} →
  Truncated-Typeᵉ lᵉ kᵉ → Truncated-Typeᵉ lᵉ (iterated-succ-𝕋'ᵉ kᵉ rᵉ)
pr1ᵉ (truncated-type-iterated-succ-Truncated-Typeᵉ kᵉ rᵉ Aᵉ) = type-Truncated-Typeᵉ Aᵉ
pr2ᵉ (truncated-type-iterated-succ-Truncated-Typeᵉ kᵉ rᵉ Aᵉ) =
  is-trunc-iterated-succ-is-truncᵉ kᵉ rᵉ (is-trunc-type-Truncated-Typeᵉ Aᵉ)
```

### Two equivalent types are equivalently `k`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-is-trunc-equivᵉ : Aᵉ ≃ᵉ Bᵉ → is-truncᵉ kᵉ Aᵉ ≃ᵉ is-truncᵉ kᵉ Bᵉ
  equiv-is-trunc-equivᵉ eᵉ =
    equiv-iff-is-propᵉ
      ( is-prop-is-truncᵉ kᵉ Aᵉ)
      ( is-prop-is-truncᵉ kᵉ Bᵉ)
      ( is-trunc-equiv'ᵉ kᵉ Aᵉ eᵉ)
      ( is-trunc-equivᵉ kᵉ Bᵉ eᵉ)
```

### If the domain or codomain is `k+1`-truncated, then the type of equivalences is `k+1`-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-equiv-is-trunc-codomainᵉ :
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (Aᵉ ≃ᵉ Bᵉ)
  is-trunc-equiv-is-trunc-codomainᵉ is-trunc-Bᵉ =
    is-trunc-type-subtypeᵉ
      ( kᵉ)
      ( is-equiv-Propᵉ)
      ( is-trunc-function-typeᵉ (succ-𝕋ᵉ kᵉ) is-trunc-Bᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-equiv-is-trunc-domainᵉ :
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (Aᵉ ≃ᵉ Bᵉ)
  is-trunc-equiv-is-trunc-domainᵉ is-trunc-Aᵉ =
    is-trunc-equivᵉ
      ( succ-𝕋ᵉ kᵉ)
      ( Bᵉ ≃ᵉ Aᵉ)
      ( equiv-inv-equivᵉ)
      ( is-trunc-equiv-is-trunc-codomainᵉ kᵉ is-trunc-Aᵉ)
```