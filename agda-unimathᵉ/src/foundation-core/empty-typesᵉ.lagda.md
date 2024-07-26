# Empty types

```agda
module foundation-core.empty-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Anᵉ **emptyᵉ type**ᵉ isᵉ aᵉ typeᵉ with noᵉ elements.ᵉ Theᵉ (standardᵉ) emptyᵉ typeᵉ isᵉ
introducedᵉ asᵉ anᵉ inductive typeᵉ with noᵉ constructors.ᵉ Withᵉ theᵉ standardᵉ emptyᵉ
typeᵉ available,ᵉ weᵉ willᵉ sayᵉ thatᵉ aᵉ typeᵉ isᵉ emptyᵉ ifᵉ itᵉ mapsᵉ intoᵉ theᵉ standardᵉ
emptyᵉ type.ᵉ

## Definition

### Empty types

```agda
data emptyᵉ : UUᵉ lzero where

ind-emptyᵉ : {lᵉ : Level} {Pᵉ : emptyᵉ → UUᵉ lᵉ} → ((xᵉ : emptyᵉ) → Pᵉ xᵉ)
ind-emptyᵉ ()

ex-falsoᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → emptyᵉ → Aᵉ
ex-falsoᵉ = ind-emptyᵉ

is-emptyᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-emptyᵉ Aᵉ = Aᵉ → emptyᵉ

is-nonemptyᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-nonemptyᵉ Aᵉ = is-emptyᵉ (is-emptyᵉ Aᵉ)
```

## Properties

### The map `ex-falso` is an embedding

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-emb-ex-falsoᵉ : is-embᵉ (ex-falsoᵉ {Aᵉ = Aᵉ})
    is-emb-ex-falsoᵉ ()

  ex-falso-embᵉ : emptyᵉ ↪ᵉ Aᵉ
  pr1ᵉ ex-falso-embᵉ = ex-falsoᵉ
  pr2ᵉ ex-falso-embᵉ = is-emb-ex-falsoᵉ
```

### Any map into an empty type is an equivalence

```agda
abstract
  is-equiv-is-emptyᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-emptyᵉ Bᵉ → is-equivᵉ fᵉ
  is-equiv-is-emptyᵉ fᵉ Hᵉ =
    is-equiv-is-invertibleᵉ
      ( ex-falsoᵉ ∘ᵉ Hᵉ)
      ( λ yᵉ → ex-falsoᵉ (Hᵉ yᵉ))
      ( λ xᵉ → ex-falsoᵉ (Hᵉ (fᵉ xᵉ)))

abstract
  is-equiv-is-empty'ᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : is-emptyᵉ Aᵉ) → is-equivᵉ fᵉ
  is-equiv-is-empty'ᵉ fᵉ = is-equiv-is-emptyᵉ fᵉ idᵉ

equiv-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-emptyᵉ Aᵉ → is-emptyᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
equiv-is-emptyᵉ fᵉ gᵉ =
  ( inv-equivᵉ (pairᵉ gᵉ (is-equiv-is-emptyᵉ gᵉ idᵉ))) ∘eᵉ
  ( pairᵉ fᵉ (is-equiv-is-emptyᵉ fᵉ idᵉ))
```

### The empty type is a proposition

```agda
abstract
  is-prop-emptyᵉ : is-propᵉ emptyᵉ
  is-prop-emptyᵉ ()

empty-Propᵉ : Propᵉ lzero
pr1ᵉ empty-Propᵉ = emptyᵉ
pr2ᵉ empty-Propᵉ = is-prop-emptyᵉ

is-prop-is-emptyᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-emptyᵉ Aᵉ → is-propᵉ Aᵉ
is-prop-is-emptyᵉ is-empty-Aᵉ = ex-falsoᵉ ∘ᵉ is-empty-Aᵉ
```

### The empty type is a set

```agda
is-set-emptyᵉ : is-setᵉ emptyᵉ
is-set-emptyᵉ ()

empty-Setᵉ : Setᵉ lzero
pr1ᵉ empty-Setᵉ = emptyᵉ
pr2ᵉ empty-Setᵉ = is-set-emptyᵉ
```

### The empty type is `k`-truncated for any `k ≥ 1`

```agda
abstract
  is-trunc-emptyᵉ : (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) emptyᵉ
  is-trunc-emptyᵉ kᵉ ()

empty-Truncated-Typeᵉ : (kᵉ : 𝕋ᵉ) → Truncated-Typeᵉ lzero (succ-𝕋ᵉ kᵉ)
pr1ᵉ (empty-Truncated-Typeᵉ kᵉ) = emptyᵉ
pr2ᵉ (empty-Truncated-Typeᵉ kᵉ) = is-trunc-emptyᵉ kᵉ

abstract
  is-trunc-is-emptyᵉ :
    {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} → is-emptyᵉ Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-trunc-is-emptyᵉ kᵉ fᵉ xᵉ = ex-falsoᵉ (fᵉ xᵉ)
```