# Constant type families

```agda
module foundation.constant-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.dependent-identificationsᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **constant**,ᵉ ifᵉ thereᵉ isᵉ aᵉ typeᵉ `X`ᵉ
equippedᵉ with aᵉ familyᵉ ofᵉ equivalencesᵉ `Xᵉ ≃ᵉ Bᵉ a`ᵉ indexedᵉ byᵉ `aᵉ : A`.ᵉ

Theᵉ **standardᵉ constantᵉ typeᵉ family**ᵉ overᵉ `A`ᵉ with fiberᵉ `B`ᵉ isᵉ theᵉ constantᵉ
mapᵉ `constᵉ Aᵉ 𝒰ᵉ Bᵉ : Aᵉ → 𝒰`,ᵉ where `𝒰`ᵉ isᵉ aᵉ universeᵉ containingᵉ `B`.ᵉ

## Definitions

### The predicate of being a constant type family

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-constant-type-familyᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-constant-type-familyᵉ = Σᵉ (UUᵉ l2ᵉ) (λ Xᵉ → (aᵉ : Aᵉ) → Xᵉ ≃ᵉ Bᵉ aᵉ)

  module _
    (Hᵉ : is-constant-type-familyᵉ)
    where

    type-is-constant-type-familyᵉ : UUᵉ l2ᵉ
    type-is-constant-type-familyᵉ = pr1ᵉ Hᵉ

    equiv-is-constant-type-familyᵉ : (aᵉ : Aᵉ) → type-is-constant-type-familyᵉ ≃ᵉ Bᵉ aᵉ
    equiv-is-constant-type-familyᵉ = pr2ᵉ Hᵉ
```

### The (standard) constant type family

```agda
constant-type-familyᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → Aᵉ → UUᵉ l2ᵉ
constant-type-familyᵉ Aᵉ Bᵉ aᵉ = Bᵉ

is-constant-type-family-constant-type-familyᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  is-constant-type-familyᵉ (constant-type-familyᵉ Aᵉ Bᵉ)
pr1ᵉ (is-constant-type-family-constant-type-familyᵉ Aᵉ Bᵉ) = Bᵉ
pr2ᵉ (is-constant-type-family-constant-type-familyᵉ Aᵉ Bᵉ) aᵉ = id-equivᵉ
```

## Properties

### Transport in a standard constant type family

```agda
tr-constant-type-familyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (bᵉ : Bᵉ) →
  dependent-identificationᵉ (constant-type-familyᵉ Aᵉ Bᵉ) pᵉ bᵉ bᵉ
tr-constant-type-familyᵉ reflᵉ bᵉ = reflᵉ
```

### Computing dependent identifications in constant type families

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-compute-dependent-identification-constant-type-familyᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ y'ᵉ : Bᵉ} →
    x'ᵉ ＝ᵉ y'ᵉ → dependent-identificationᵉ (λ _ → Bᵉ) pᵉ x'ᵉ y'ᵉ
  map-compute-dependent-identification-constant-type-familyᵉ pᵉ {x'ᵉ} qᵉ =
    tr-constant-type-familyᵉ pᵉ x'ᵉ ∙ᵉ qᵉ

  compute-dependent-identification-constant-type-familyᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ y'ᵉ : Bᵉ} →
    (x'ᵉ ＝ᵉ y'ᵉ) ≃ᵉ dependent-identificationᵉ (λ _ → Bᵉ) pᵉ x'ᵉ y'ᵉ
  compute-dependent-identification-constant-type-familyᵉ pᵉ {x'ᵉ} {y'ᵉ} =
    equiv-concatᵉ (tr-constant-type-familyᵉ pᵉ x'ᵉ) y'ᵉ
```

### Dependent action on paths of sections of standard constant type families

```agda
apd-constant-type-familyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  apdᵉ fᵉ pᵉ ＝ᵉ tr-constant-type-familyᵉ pᵉ (fᵉ xᵉ) ∙ᵉ apᵉ fᵉ pᵉ
apd-constant-type-familyᵉ fᵉ reflᵉ = reflᵉ
```

### Naturality of transport in constant type families

Forᵉ everyᵉ equalityᵉ `pᵉ : xᵉ ＝ᵉ x'`ᵉ in `A`ᵉ andᵉ `qᵉ : yᵉ ＝ᵉ y'`ᵉ in `B`ᵉ weᵉ haveᵉ aᵉ
commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
                    apᵉ (trᵉ (λ _ → Bᵉ) pᵉ) qᵉ
          trᵉ (λ _ → Bᵉ) pᵉ yᵉ ------>ᵉ trᵉ (λ _ → Bᵉ) pᵉ y'ᵉ
                         |         |
  tr-constant-familyᵉ pᵉ yᵉ |         | tr-constant-familyᵉ pᵉ y'ᵉ
                         ∨ᵉ         ∨ᵉ
                         yᵉ ------>ᵉ y'.ᵉ
                              qᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  naturality-tr-constant-type-familyᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ (trᵉ (λ _ → Bᵉ) pᵉ) qᵉ)
      ( tr-constant-type-familyᵉ pᵉ yᵉ)
      ( tr-constant-type-familyᵉ pᵉ y'ᵉ)
      ( qᵉ)
  naturality-tr-constant-type-familyᵉ pᵉ reflᵉ = right-unitᵉ

  naturality-inv-tr-constant-type-familyᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ᵉ y'ᵉ) →
    coherence-square-identificationsᵉ
      ( qᵉ)
      ( invᵉ (tr-constant-type-familyᵉ pᵉ yᵉ))
      ( invᵉ (tr-constant-type-familyᵉ pᵉ y'ᵉ))
      ( apᵉ (trᵉ (λ _ → Bᵉ) pᵉ) qᵉ)
  naturality-inv-tr-constant-type-familyᵉ pᵉ reflᵉ = right-unitᵉ
```