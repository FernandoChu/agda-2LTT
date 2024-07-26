# Endomorphisms

```agda
module foundation-core.endomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Anᵉ endomorphismᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ `Aᵉ → A`.ᵉ

## Definition

```agda
endoᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
endoᵉ Aᵉ = Aᵉ → Aᵉ

endo-Pointed-Typeᵉ : {lᵉ : Level} → UUᵉ lᵉ → Pointed-Typeᵉ lᵉ
pr1ᵉ (endo-Pointed-Typeᵉ Aᵉ) = Aᵉ → Aᵉ
pr2ᵉ (endo-Pointed-Typeᵉ Aᵉ) = idᵉ
```

## Properties

### If the domain is a set the type of endomorphisms is a set

```agda
is-set-endoᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ → is-setᵉ (endoᵉ Aᵉ)
is-set-endoᵉ is-set-Aᵉ = is-set-function-typeᵉ is-set-Aᵉ

endo-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → Setᵉ lᵉ
pr1ᵉ (endo-Setᵉ Aᵉ) = endoᵉ (type-Setᵉ Aᵉ)
pr2ᵉ (endo-Setᵉ Aᵉ) = is-set-endoᵉ (is-set-type-Setᵉ Aᵉ)
```

### If the domain is `k`-truncated the type of endomorphisms is `k`-truncated

```agda
is-trunc-endoᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (kᵉ : 𝕋ᵉ) → is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (endoᵉ Aᵉ)
is-trunc-endoᵉ kᵉ is-trunc-Aᵉ = is-trunc-function-typeᵉ kᵉ is-trunc-Aᵉ

endo-Truncated-Typeᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) → Truncated-Typeᵉ lᵉ kᵉ → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (endo-Truncated-Typeᵉ kᵉ Aᵉ) = endoᵉ (type-Truncated-Typeᵉ Aᵉ)
pr2ᵉ (endo-Truncated-Typeᵉ kᵉ Aᵉ) = is-trunc-endoᵉ kᵉ (is-trunc-type-Truncated-Typeᵉ Aᵉ)
```

## See also

-ᵉ Forᵉ endomorphismsᵉ in aᵉ categoryᵉ seeᵉ
  [`category-theory.endomorphisms-in-categories`](category-theory.endomorphisms-in-categories.md).ᵉ