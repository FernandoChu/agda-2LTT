# Decidability of dependent pair types

```agda
module foundation.decidable-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.maybeᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
```

</details>

## Idea

Weᵉ describeᵉ conditionsᵉ underᵉ whichᵉ dependentᵉ sumsᵉ areᵉ decidable.ᵉ

```agda
is-decidable-Σ-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Cᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ) →
  is-decidableᵉ (Σᵉ Aᵉ (Cᵉ ∘ᵉ inlᵉ)) → is-decidableᵉ (Σᵉ Bᵉ (Cᵉ ∘ᵉ inrᵉ)) →
  is-decidableᵉ (Σᵉ (Aᵉ +ᵉ Bᵉ) Cᵉ)
is-decidable-Σ-coproductᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} {Aᵉ} {Bᵉ} Cᵉ dAᵉ dBᵉ =
  is-decidable-equivᵉ
    ( right-distributive-Σ-coproductᵉ Aᵉ Bᵉ Cᵉ)
    ( is-decidable-coproductᵉ dAᵉ dBᵉ)

is-decidable-Σ-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Maybeᵉ Aᵉ → UUᵉ l2ᵉ} →
  is-decidableᵉ (Σᵉ Aᵉ (Bᵉ ∘ᵉ unit-Maybeᵉ)) → is-decidableᵉ (Bᵉ exception-Maybeᵉ) →
  is-decidableᵉ (Σᵉ (Maybeᵉ Aᵉ) Bᵉ)
is-decidable-Σ-Maybeᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} dAᵉ deᵉ =
  is-decidable-Σ-coproductᵉ Bᵉ dAᵉ
    ( is-decidable-equivᵉ
      ( left-unit-law-Σᵉ (Bᵉ ∘ᵉ inrᵉ))
      ( deᵉ))

is-decidable-Σ-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : Bᵉ → UUᵉ l4ᵉ}
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) →
  is-decidableᵉ (Σᵉ Aᵉ Cᵉ) → is-decidableᵉ (Σᵉ Bᵉ Dᵉ)
is-decidable-Σ-equivᵉ {Dᵉ = Dᵉ} eᵉ fᵉ =
  is-decidable-equiv'ᵉ (equiv-Σᵉ Dᵉ eᵉ fᵉ)

is-decidable-Σ-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : Bᵉ → UUᵉ l4ᵉ}
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) →
  is-decidableᵉ (Σᵉ Bᵉ Dᵉ) → is-decidableᵉ (Σᵉ Aᵉ Cᵉ)
is-decidable-Σ-equiv'ᵉ {Dᵉ = Dᵉ} eᵉ fᵉ =
  is-decidable-equivᵉ (equiv-Σᵉ Dᵉ eᵉ fᵉ)
```