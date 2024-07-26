# Mere equivalences

```agda
module foundation.mere-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Twoᵉ typesᵉ `X`ᵉ andᵉ `Y`ᵉ areᵉ saidᵉ to beᵉ merelyᵉ equivalent,ᵉ ifᵉ thereᵉ existsᵉ anᵉ
equivalenceᵉ fromᵉ `X`ᵉ to `Y`.ᵉ Propositionalᵉ truncationsᵉ areᵉ usedᵉ to expressᵉ mereᵉ
equivalence.ᵉ

## Definition

```agda
mere-equiv-Propᵉ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
mere-equiv-Propᵉ Xᵉ Yᵉ = trunc-Propᵉ (Xᵉ ≃ᵉ Yᵉ)

mere-equivᵉ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
mere-equivᵉ Xᵉ Yᵉ = type-Propᵉ (mere-equiv-Propᵉ Xᵉ Yᵉ)

abstract
  is-prop-mere-equivᵉ :
    {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → is-propᵉ (mere-equivᵉ Xᵉ Yᵉ)
  is-prop-mere-equivᵉ Xᵉ Yᵉ = is-prop-type-Propᵉ (mere-equiv-Propᵉ Xᵉ Yᵉ)
```

## Properties

### Mere equivalence is reflexive

```agda
abstract
  refl-mere-equivᵉ : {l1ᵉ : Level} → is-reflexiveᵉ (mere-equivᵉ {l1ᵉ})
  refl-mere-equivᵉ Xᵉ = unit-trunc-Propᵉ id-equivᵉ
```

### Mere equivalence is symmetric

```agda
abstract
  symmetric-mere-equivᵉ :
    {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) → mere-equivᵉ Xᵉ Yᵉ → mere-equivᵉ Yᵉ Xᵉ
  symmetric-mere-equivᵉ Xᵉ Yᵉ =
    map-universal-property-trunc-Propᵉ
      ( mere-equiv-Propᵉ Yᵉ Xᵉ)
      ( λ eᵉ → unit-trunc-Propᵉ (inv-equivᵉ eᵉ))
```

### Mere equivalence is transitive

```agda
abstract
  transitive-mere-equivᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) (Zᵉ : UUᵉ l3ᵉ) →
    mere-equivᵉ Yᵉ Zᵉ → mere-equivᵉ Xᵉ Yᵉ → mere-equivᵉ Xᵉ Zᵉ
  transitive-mere-equivᵉ Xᵉ Yᵉ Zᵉ fᵉ eᵉ =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( mere-equiv-Propᵉ Xᵉ Zᵉ)
      ( λ e'ᵉ →
        apply-universal-property-trunc-Propᵉ fᵉ
          ( mere-equiv-Propᵉ Xᵉ Zᵉ)
          ( λ f'ᵉ → unit-trunc-Propᵉ (f'ᵉ ∘eᵉ e'ᵉ)))
```

### Truncated types are closed under mere equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  is-trunc-mere-equivᵉ : (kᵉ : 𝕋ᵉ) → mere-equivᵉ Xᵉ Yᵉ → is-truncᵉ kᵉ Yᵉ → is-truncᵉ kᵉ Xᵉ
  is-trunc-mere-equivᵉ kᵉ eᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ
      ( eᵉ)
      ( is-trunc-Propᵉ kᵉ Xᵉ)
      ( λ fᵉ → is-trunc-equivᵉ kᵉ Yᵉ fᵉ Hᵉ)

  is-trunc-mere-equiv'ᵉ : (kᵉ : 𝕋ᵉ) → mere-equivᵉ Xᵉ Yᵉ → is-truncᵉ kᵉ Xᵉ → is-truncᵉ kᵉ Yᵉ
  is-trunc-mere-equiv'ᵉ kᵉ eᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ
      ( eᵉ)
      ( is-trunc-Propᵉ kᵉ Yᵉ)
      ( λ fᵉ → is-trunc-equiv'ᵉ kᵉ Xᵉ fᵉ Hᵉ)
```

### Sets are closed under mere equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  is-set-mere-equivᵉ : mere-equivᵉ Xᵉ Yᵉ → is-setᵉ Yᵉ → is-setᵉ Xᵉ
  is-set-mere-equivᵉ = is-trunc-mere-equivᵉ zero-𝕋ᵉ

  is-set-mere-equiv'ᵉ : mere-equivᵉ Xᵉ Yᵉ → is-setᵉ Xᵉ → is-setᵉ Yᵉ
  is-set-mere-equiv'ᵉ = is-trunc-mere-equiv'ᵉ zero-𝕋ᵉ
```

### Types with decidable equality are closed under mere equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  has-decidable-equality-mere-equivᵉ :
    mere-equivᵉ Xᵉ Yᵉ → has-decidable-equalityᵉ Yᵉ → has-decidable-equalityᵉ Xᵉ
  has-decidable-equality-mere-equivᵉ eᵉ dᵉ =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( has-decidable-equality-Propᵉ Xᵉ)
      ( λ fᵉ → has-decidable-equality-equivᵉ fᵉ dᵉ)

  has-decidable-equality-mere-equiv'ᵉ :
    mere-equivᵉ Xᵉ Yᵉ → has-decidable-equalityᵉ Xᵉ → has-decidable-equalityᵉ Yᵉ
  has-decidable-equality-mere-equiv'ᵉ eᵉ dᵉ =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( has-decidable-equality-Propᵉ Yᵉ)
      ( λ fᵉ → has-decidable-equality-equiv'ᵉ fᵉ dᵉ)
```

### Mere equivalence implies mere equality

```agda
abstract
  mere-eq-mere-equivᵉ :
    {lᵉ : Level} {Aᵉ Bᵉ : UUᵉ lᵉ} → mere-equivᵉ Aᵉ Bᵉ → mere-eqᵉ Aᵉ Bᵉ
  mere-eq-mere-equivᵉ = map-trunc-Propᵉ eq-equivᵉ
```