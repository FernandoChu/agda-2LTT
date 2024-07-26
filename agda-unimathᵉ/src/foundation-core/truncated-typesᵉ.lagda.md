# Truncated types

```agda
module foundation-core.truncated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ truncatednessᵉ ofᵉ aᵉ typeᵉ isᵉ aᵉ measureᵉ ofᵉ theᵉ complexityᵉ ofᵉ itsᵉ identityᵉ
types.ᵉ Theᵉ simplestᵉ caseᵉ isᵉ aᵉ contractibleᵉ type.ᵉ Thisᵉ isᵉ theᵉ baseᵉ caseᵉ ofᵉ theᵉ
inductive definitionᵉ ofᵉ truncatednessᵉ forᵉ types.ᵉ Aᵉ typeᵉ isᵉ `k+1`-truncatedᵉ ifᵉ
itsᵉ identityᵉ typesᵉ areᵉ `k`-truncated.ᵉ

## Definition

### The condition of truncatedness

```agda
is-truncᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
is-truncᵉ neg-two-𝕋ᵉ Aᵉ = is-contrᵉ Aᵉ
is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ = (xᵉ yᵉ : Aᵉ) → is-truncᵉ kᵉ (xᵉ ＝ᵉ yᵉ)

is-trunc-eqᵉ :
  {lᵉ : Level} {kᵉ k'ᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ} → kᵉ ＝ᵉ k'ᵉ → is-truncᵉ kᵉ Aᵉ → is-truncᵉ k'ᵉ Aᵉ
is-trunc-eqᵉ reflᵉ Hᵉ = Hᵉ
```

### The universe of truncated types

```agda
Truncated-Typeᵉ : (lᵉ : Level) → 𝕋ᵉ → UUᵉ (lsuc lᵉ)
Truncated-Typeᵉ lᵉ kᵉ = Σᵉ (UUᵉ lᵉ) (is-truncᵉ kᵉ)

module _
  {kᵉ : 𝕋ᵉ} {lᵉ : Level}
  where

  type-Truncated-Typeᵉ : Truncated-Typeᵉ lᵉ kᵉ → UUᵉ lᵉ
  type-Truncated-Typeᵉ = pr1ᵉ

  is-trunc-type-Truncated-Typeᵉ :
    (Aᵉ : Truncated-Typeᵉ lᵉ kᵉ) → is-truncᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ)
  is-trunc-type-Truncated-Typeᵉ = pr2ᵉ
```

## Properties

### If a type is `k`-truncated, then it is `k+1`-truncated

```agda
abstract
  is-trunc-succ-is-truncᵉ :
    (kᵉ : 𝕋ᵉ) {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-truncᵉ kᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  pr1ᵉ (is-trunc-succ-is-truncᵉ neg-two-𝕋ᵉ Hᵉ xᵉ yᵉ) = eq-is-contrᵉ Hᵉ
  pr2ᵉ (is-trunc-succ-is-truncᵉ neg-two-𝕋ᵉ Hᵉ xᵉ .xᵉ) reflᵉ = left-invᵉ (pr2ᵉ Hᵉ xᵉ)
  is-trunc-succ-is-truncᵉ (succ-𝕋ᵉ kᵉ) Hᵉ xᵉ yᵉ = is-trunc-succ-is-truncᵉ kᵉ (Hᵉ xᵉ yᵉ)

truncated-type-succ-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {lᵉ : Level} → Truncated-Typeᵉ lᵉ kᵉ → Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ kᵉ)
pr1ᵉ (truncated-type-succ-Truncated-Typeᵉ kᵉ Aᵉ) = type-Truncated-Typeᵉ Aᵉ
pr2ᵉ (truncated-type-succ-Truncated-Typeᵉ kᵉ Aᵉ) =
  is-trunc-succ-is-truncᵉ kᵉ (is-trunc-type-Truncated-Typeᵉ Aᵉ)
```

Theᵉ corollaryᵉ thatᵉ anyᵉ `-1`-truncatedᵉ type,ᵉ i.e.,ᵉ anyᵉ propoosition,ᵉ isᵉ
`k+1`-truncatedᵉ forᵉ anyᵉ truncationᵉ levelᵉ `k`ᵉ isᵉ recordedᵉ in
[Propositions](foundation.propositions.mdᵉ) asᵉ `is-trunc-is-prop`.ᵉ

### The identity type of a `k`-truncated type is `k`-truncated

```agda
abstract
  is-trunc-Idᵉ :
    {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ} →
    is-truncᵉ kᵉ Aᵉ → (xᵉ yᵉ : Aᵉ) → is-truncᵉ kᵉ (xᵉ ＝ᵉ yᵉ)
  is-trunc-Idᵉ {lᵉ} {kᵉ} = is-trunc-succ-is-truncᵉ kᵉ

Id-Truncated-Typeᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ kᵉ)) →
  (xᵉ yᵉ : type-Truncated-Typeᵉ Aᵉ) → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (Id-Truncated-Typeᵉ Aᵉ xᵉ yᵉ) = (xᵉ ＝ᵉ yᵉ)
pr2ᵉ (Id-Truncated-Typeᵉ Aᵉ xᵉ yᵉ) = is-trunc-type-Truncated-Typeᵉ Aᵉ xᵉ yᵉ

Id-Truncated-Type'ᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ lᵉ kᵉ) →
  (xᵉ yᵉ : type-Truncated-Typeᵉ Aᵉ) → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (Id-Truncated-Type'ᵉ Aᵉ xᵉ yᵉ) = (xᵉ ＝ᵉ yᵉ)
pr2ᵉ (Id-Truncated-Type'ᵉ Aᵉ xᵉ yᵉ) =
  is-trunc-Idᵉ (is-trunc-type-Truncated-Typeᵉ Aᵉ) xᵉ yᵉ
```

### `k`-truncated types are closed under retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  is-trunc-retract-ofᵉ :
    {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    Aᵉ retract-ofᵉ Bᵉ → is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ Aᵉ
  is-trunc-retract-ofᵉ {neg-two-𝕋ᵉ} = is-contr-retract-ofᵉ _
  is-trunc-retract-ofᵉ {succ-𝕋ᵉ kᵉ} Rᵉ Hᵉ xᵉ yᵉ =
    is-trunc-retract-ofᵉ (retract-eqᵉ Rᵉ xᵉ yᵉ) (Hᵉ (pr1ᵉ Rᵉ xᵉ) (pr1ᵉ Rᵉ yᵉ))
```

### `k`-truncated types are closed under equivalences

```agda
abstract
  is-trunc-is-equivᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (fᵉ : Aᵉ → Bᵉ) → is-equivᵉ fᵉ →
    is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ Aᵉ
  is-trunc-is-equivᵉ kᵉ Bᵉ fᵉ is-equiv-fᵉ =
    is-trunc-retract-ofᵉ (pairᵉ fᵉ (pr2ᵉ is-equiv-fᵉ))

abstract
  is-trunc-equivᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ Aᵉ
  is-trunc-equivᵉ kᵉ Bᵉ (pairᵉ fᵉ is-equiv-fᵉ) =
    is-trunc-is-equivᵉ kᵉ Bᵉ fᵉ is-equiv-fᵉ

abstract
  is-trunc-is-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ fᵉ → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ
  is-trunc-is-equiv'ᵉ kᵉ Aᵉ fᵉ is-equiv-fᵉ is-trunc-Aᵉ =
    is-trunc-is-equivᵉ kᵉ Aᵉ
      ( map-inv-is-equivᵉ is-equiv-fᵉ)
      ( is-equiv-map-inv-is-equivᵉ is-equiv-fᵉ)
      ( is-trunc-Aᵉ)

abstract
  is-trunc-equiv'ᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ
  is-trunc-equiv'ᵉ kᵉ Aᵉ (pairᵉ fᵉ is-equiv-fᵉ) =
    is-trunc-is-equiv'ᵉ kᵉ Aᵉ fᵉ is-equiv-fᵉ
```

### If a type embeds into a `k+1`-truncated type, then it is `k+1`-truncated

```agda
abstract
  is-trunc-is-embᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-embᵉ fᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-trunc-is-embᵉ kᵉ fᵉ Efᵉ Hᵉ xᵉ yᵉ =
    is-trunc-is-equivᵉ kᵉ (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) (apᵉ fᵉ {xᵉ} {yᵉ}) (Efᵉ xᵉ yᵉ) (Hᵉ (fᵉ xᵉ) (fᵉ yᵉ))

abstract
  is-trunc-embᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↪ᵉ Bᵉ) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-trunc-embᵉ kᵉ fᵉ = is-trunc-is-embᵉ kᵉ (map-embᵉ fᵉ) (is-emb-map-embᵉ fᵉ)
```

### Truncated types are closed under dependent pair types

```agda
abstract
  is-trunc-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-truncᵉ kᵉ Aᵉ → ((xᵉ : Aᵉ) → is-truncᵉ kᵉ (Bᵉ xᵉ)) → is-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
  is-trunc-Σᵉ {kᵉ = neg-two-𝕋ᵉ} is-trunc-Aᵉ is-trunc-Bᵉ =
    is-contr-Σ'ᵉ is-trunc-Aᵉ is-trunc-Bᵉ
  is-trunc-Σᵉ {kᵉ = succ-𝕋ᵉ kᵉ} {Bᵉ = Bᵉ} is-trunc-Aᵉ is-trunc-Bᵉ sᵉ tᵉ =
    is-trunc-equivᵉ kᵉ
      ( Σᵉ (pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) (λ pᵉ → trᵉ Bᵉ pᵉ (pr2ᵉ sᵉ) ＝ᵉ pr2ᵉ tᵉ))
      ( equiv-pair-eq-Σᵉ sᵉ tᵉ)
      ( is-trunc-Σᵉ
        ( is-trunc-Aᵉ (pr1ᵉ sᵉ) (pr1ᵉ tᵉ))
        ( λ pᵉ → is-trunc-Bᵉ (pr1ᵉ tᵉ) (trᵉ Bᵉ pᵉ (pr2ᵉ sᵉ)) (pr2ᵉ tᵉ)))

Σ-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : type-Truncated-Typeᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (Σ-Truncated-Typeᵉ Aᵉ Bᵉ) =
  Σᵉ (type-Truncated-Typeᵉ Aᵉ) (λ aᵉ → type-Truncated-Typeᵉ (Bᵉ aᵉ))
pr2ᵉ (Σ-Truncated-Typeᵉ Aᵉ Bᵉ) =
  is-trunc-Σᵉ
    ( is-trunc-type-Truncated-Typeᵉ Aᵉ)
    ( λ aᵉ → is-trunc-type-Truncated-Typeᵉ (Bᵉ aᵉ))

fiber-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ)
  (fᵉ : type-Truncated-Typeᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ) →
  type-Truncated-Typeᵉ Bᵉ → Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
fiber-Truncated-Typeᵉ Aᵉ Bᵉ fᵉ bᵉ =
  Σ-Truncated-Typeᵉ Aᵉ (λ aᵉ → Id-Truncated-Type'ᵉ Bᵉ (fᵉ aᵉ) bᵉ)
```

### Products of truncated types are truncated

```agda
abstract
  is-trunc-productᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ (Aᵉ ×ᵉ Bᵉ)
  is-trunc-productᵉ kᵉ is-trunc-Aᵉ is-trunc-Bᵉ =
    is-trunc-Σᵉ is-trunc-Aᵉ (λ xᵉ → is-trunc-Bᵉ)

product-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) →
  Truncated-Typeᵉ l1ᵉ kᵉ → Truncated-Typeᵉ l2ᵉ kᵉ → Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (product-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ) =
  type-Truncated-Typeᵉ Aᵉ ×ᵉ type-Truncated-Typeᵉ Bᵉ
pr2ᵉ (product-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ) =
  is-trunc-productᵉ kᵉ
    ( is-trunc-type-Truncated-Typeᵉ Aᵉ)
    ( is-trunc-type-Truncated-Typeᵉ Bᵉ)

is-trunc-product'ᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Bᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) → (Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Bᵉ) →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) (Aᵉ ×ᵉ Bᵉ)
is-trunc-product'ᵉ kᵉ fᵉ gᵉ (pairᵉ aᵉ bᵉ) (pairᵉ a'ᵉ b'ᵉ) =
  is-trunc-equivᵉ kᵉ
    ( Eq-productᵉ (pairᵉ aᵉ bᵉ) (pairᵉ a'ᵉ b'ᵉ))
    ( equiv-pair-eqᵉ (pairᵉ aᵉ bᵉ) (pairᵉ a'ᵉ b'ᵉ))
    ( is-trunc-productᵉ kᵉ (fᵉ bᵉ aᵉ a'ᵉ) (gᵉ aᵉ bᵉ b'ᵉ))

is-trunc-left-factor-productᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-truncᵉ kᵉ (Aᵉ ×ᵉ Bᵉ) → Bᵉ → is-truncᵉ kᵉ Aᵉ
is-trunc-left-factor-productᵉ neg-two-𝕋ᵉ {Aᵉ} {Bᵉ} Hᵉ bᵉ =
  is-contr-left-factor-productᵉ Aᵉ Bᵉ Hᵉ
is-trunc-left-factor-productᵉ (succ-𝕋ᵉ kᵉ) Hᵉ bᵉ aᵉ a'ᵉ =
  is-trunc-left-factor-productᵉ kᵉ {Aᵉ = (aᵉ ＝ᵉ a'ᵉ)} {Bᵉ = (bᵉ ＝ᵉ bᵉ)}
    ( is-trunc-equiv'ᵉ kᵉ
      ( pairᵉ aᵉ bᵉ ＝ᵉ pairᵉ a'ᵉ bᵉ)
      ( equiv-pair-eqᵉ (pairᵉ aᵉ bᵉ) (pairᵉ a'ᵉ bᵉ))
      ( Hᵉ (pairᵉ aᵉ bᵉ) (pairᵉ a'ᵉ bᵉ)))
    ( reflᵉ)

is-trunc-right-factor-productᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-truncᵉ kᵉ (Aᵉ ×ᵉ Bᵉ) → Aᵉ → is-truncᵉ kᵉ Bᵉ
is-trunc-right-factor-productᵉ neg-two-𝕋ᵉ {Aᵉ} {Bᵉ} Hᵉ aᵉ =
  is-contr-right-factor-productᵉ Aᵉ Bᵉ Hᵉ
is-trunc-right-factor-productᵉ (succ-𝕋ᵉ kᵉ) {Aᵉ} {Bᵉ} Hᵉ aᵉ bᵉ b'ᵉ =
  is-trunc-right-factor-productᵉ kᵉ {Aᵉ = (aᵉ ＝ᵉ aᵉ)} {Bᵉ = (bᵉ ＝ᵉ b'ᵉ)}
    ( is-trunc-equiv'ᵉ kᵉ
      ( pairᵉ aᵉ bᵉ ＝ᵉ pairᵉ aᵉ b'ᵉ)
      ( equiv-pair-eqᵉ (pairᵉ aᵉ bᵉ) (pairᵉ aᵉ b'ᵉ))
      ( Hᵉ (pairᵉ aᵉ bᵉ) (pairᵉ aᵉ b'ᵉ)))
    ( reflᵉ)
```

### Products of families of truncated types are truncated

```agda
abstract
  is-trunc-Πᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    ((xᵉ : Aᵉ) → is-truncᵉ kᵉ (Bᵉ xᵉ)) → is-truncᵉ kᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  is-trunc-Πᵉ neg-two-𝕋ᵉ is-trunc-Bᵉ = is-contr-Πᵉ is-trunc-Bᵉ
  is-trunc-Πᵉ (succ-𝕋ᵉ kᵉ) is-trunc-Bᵉ fᵉ gᵉ =
    is-trunc-is-equivᵉ kᵉ (fᵉ ~ᵉ gᵉ) htpy-eqᵉ
      ( funextᵉ fᵉ gᵉ)
      ( is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Bᵉ xᵉ (fᵉ xᵉ) (gᵉ xᵉ)))

type-Π-Truncated-Type'ᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ = (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ)

is-trunc-type-Π-Truncated-Type'ᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-truncᵉ kᵉ (type-Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ)
is-trunc-type-Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ =
  is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-type-Truncated-Typeᵉ (Bᵉ xᵉ))

Π-Truncated-Type'ᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ) = type-Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ
pr2ᵉ (Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ) = is-trunc-type-Π-Truncated-Type'ᵉ kᵉ Aᵉ Bᵉ

type-Π-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : type-Truncated-Typeᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-Π-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ =
  type-Π-Truncated-Type'ᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ) Bᵉ

is-trunc-type-Π-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : type-Truncated-Typeᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-truncᵉ kᵉ (type-Π-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ)
is-trunc-type-Π-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ =
  is-trunc-type-Π-Truncated-Type'ᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ) Bᵉ

Π-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : type-Truncated-Typeᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
Π-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ =
  Π-Truncated-Type'ᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ) Bᵉ
```

### The type of functions into a truncated type is truncated

```agda
abstract
  is-trunc-function-typeᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ (Aᵉ → Bᵉ)
  is-trunc-function-typeᵉ kᵉ {Aᵉ} {Bᵉ} is-trunc-Bᵉ =
    is-trunc-Πᵉ kᵉ {Bᵉ = λ (xᵉ : Aᵉ) → Bᵉ} (λ xᵉ → is-trunc-Bᵉ)

function-type-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (function-type-Truncated-Typeᵉ Aᵉ Bᵉ) = Aᵉ → type-Truncated-Typeᵉ Bᵉ
pr2ᵉ (function-type-Truncated-Typeᵉ Aᵉ Bᵉ) =
  is-trunc-function-typeᵉ _ (is-trunc-type-Truncated-Typeᵉ Bᵉ)

type-hom-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ =
  type-Truncated-Typeᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ

is-trunc-type-hom-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-truncᵉ kᵉ (type-hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ)
is-trunc-type-hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ =
  is-trunc-function-typeᵉ kᵉ (is-trunc-type-Truncated-Typeᵉ Bᵉ)

hom-Truncated-Typeᵉ :
  (kᵉ : 𝕋ᵉ) {l1ᵉ l2ᵉ : Level} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ)
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) → Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ) = type-hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ
pr2ᵉ (hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ) = is-trunc-type-hom-Truncated-Typeᵉ kᵉ Aᵉ Bᵉ
```

### Being truncated is a property

```agda
abstract
  is-prop-is-truncᵉ :
    {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ) → is-propᵉ (is-truncᵉ kᵉ Aᵉ)
  is-prop-is-truncᵉ neg-two-𝕋ᵉ Aᵉ = is-property-is-contrᵉ
  is-prop-is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ =
    is-trunc-Πᵉ neg-one-𝕋ᵉ
      ( λ xᵉ → is-trunc-Πᵉ neg-one-𝕋ᵉ (λ yᵉ → is-prop-is-truncᵉ kᵉ (xᵉ ＝ᵉ yᵉ)))

is-trunc-Propᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ) → Σᵉ (UUᵉ lᵉ) (is-truncᵉ neg-one-𝕋ᵉ)
pr1ᵉ (is-trunc-Propᵉ kᵉ Aᵉ) = is-truncᵉ kᵉ Aᵉ
pr2ᵉ (is-trunc-Propᵉ kᵉ Aᵉ) = is-prop-is-truncᵉ kᵉ Aᵉ
```

### The type of equivalences between truncated types is truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-equiv-is-truncᵉ :
    (kᵉ : 𝕋ᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ Bᵉ → is-truncᵉ kᵉ (Aᵉ ≃ᵉ Bᵉ)
  is-trunc-equiv-is-truncᵉ kᵉ Hᵉ Kᵉ =
    is-trunc-Σᵉ
      ( is-trunc-function-typeᵉ kᵉ Kᵉ)
      ( λ fᵉ →
        is-trunc-Σᵉ
          ( is-trunc-Σᵉ
            ( is-trunc-function-typeᵉ kᵉ Hᵉ)
            ( λ gᵉ →
              is-trunc-Πᵉ kᵉ (λ yᵉ → is-trunc-Idᵉ Kᵉ (fᵉ (gᵉ yᵉ)) yᵉ)))
          ( λ _ →
            is-trunc-Σᵉ
              ( is-trunc-function-typeᵉ kᵉ Hᵉ)
              ( λ hᵉ →
                is-trunc-Πᵉ kᵉ (λ xᵉ → is-trunc-Idᵉ Hᵉ (hᵉ (fᵉ xᵉ)) xᵉ))))

type-equiv-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ =
  type-Truncated-Typeᵉ Aᵉ ≃ᵉ type-Truncated-Typeᵉ Bᵉ

is-trunc-type-equiv-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-truncᵉ kᵉ (type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ)
is-trunc-type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ =
  is-trunc-equiv-is-truncᵉ _
    ( is-trunc-type-Truncated-Typeᵉ Aᵉ)
    ( is-trunc-type-Truncated-Typeᵉ Bᵉ)

equiv-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ l1ᵉ kᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  Truncated-Typeᵉ (l1ᵉ ⊔ l2ᵉ) kᵉ
pr1ᵉ (equiv-Truncated-Typeᵉ Aᵉ Bᵉ) = type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ
pr2ᵉ (equiv-Truncated-Typeᵉ Aᵉ Bᵉ) = is-trunc-type-equiv-Truncated-Typeᵉ Aᵉ Bᵉ
```