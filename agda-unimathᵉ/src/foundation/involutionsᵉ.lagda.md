# Involutions

```agda
module foundation.involutionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Anᵉ **involution**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ `fᵉ : Aᵉ → A`ᵉ suchᵉ thatᵉ `(fᵉ ∘ᵉ fᵉ) ~ᵉ id`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-involutionᵉ : (Aᵉ → Aᵉ) → UUᵉ lᵉ
  is-involutionᵉ fᵉ = (fᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ

  is-involution-autᵉ : Autᵉ Aᵉ → UUᵉ lᵉ
  is-involution-autᵉ eᵉ = is-involutionᵉ (map-equivᵉ eᵉ)
```

### The type of involutions on `A`

```agda
involutionᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
involutionᵉ Aᵉ = Σᵉ (Aᵉ → Aᵉ) is-involutionᵉ

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : involutionᵉ Aᵉ)
  where

  map-involutionᵉ : Aᵉ → Aᵉ
  map-involutionᵉ = pr1ᵉ fᵉ

  is-involution-map-involutionᵉ : is-involutionᵉ map-involutionᵉ
  is-involution-map-involutionᵉ = pr2ᵉ fᵉ
```

## Properties

### Involutions are equivalences

```agda
is-equiv-is-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} → is-involutionᵉ fᵉ → is-equivᵉ fᵉ
is-equiv-is-involutionᵉ {fᵉ = fᵉ} is-involution-fᵉ =
  is-equiv-is-invertibleᵉ fᵉ is-involution-fᵉ is-involution-fᵉ

is-equiv-map-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : involutionᵉ Aᵉ) → is-equivᵉ (map-involutionᵉ fᵉ)
is-equiv-map-involutionᵉ = is-equiv-is-involutionᵉ ∘ᵉ is-involution-map-involutionᵉ

equiv-is-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} → is-involutionᵉ fᵉ → Aᵉ ≃ᵉ Aᵉ
pr1ᵉ (equiv-is-involutionᵉ {fᵉ = fᵉ} is-involution-fᵉ) = fᵉ
pr2ᵉ (equiv-is-involutionᵉ is-involution-fᵉ) =
  is-equiv-is-involutionᵉ is-involution-fᵉ

equiv-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → involutionᵉ Aᵉ → Aᵉ ≃ᵉ Aᵉ
equiv-involutionᵉ fᵉ =
  equiv-is-involutionᵉ {fᵉ = map-involutionᵉ fᵉ} (is-involution-map-involutionᵉ fᵉ)
```

### Involutions are their own inverse

```agda
htpy-own-inverse-is-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Autᵉ Aᵉ} →
  is-involution-autᵉ fᵉ → map-inv-equivᵉ fᵉ ~ᵉ map-equivᵉ fᵉ
htpy-own-inverse-is-involutionᵉ {fᵉ = fᵉ} is-involution-fᵉ xᵉ =
  is-injective-equivᵉ fᵉ
    ( htpy-eq-equivᵉ (right-inverse-law-equivᵉ fᵉ) xᵉ ∙ᵉ
      invᵉ (is-involution-fᵉ xᵉ))

own-inverse-is-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Autᵉ Aᵉ} →
  is-involution-autᵉ fᵉ → inv-equivᵉ fᵉ ＝ᵉ fᵉ
own-inverse-is-involutionᵉ {fᵉ = fᵉ} =
  eq-htpy-equivᵉ ∘ᵉ htpy-own-inverse-is-involutionᵉ {fᵉ = fᵉ}
```

### Characterizing equality of involutions

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  coherence-htpy-involutionᵉ :
    (sᵉ tᵉ : involutionᵉ Aᵉ) → map-involutionᵉ sᵉ ~ᵉ map-involutionᵉ tᵉ → UUᵉ lᵉ
  coherence-htpy-involutionᵉ sᵉ tᵉ Hᵉ =
    ( is-involution-map-involutionᵉ sᵉ) ~ᵉ
    ( horizontal-concat-htpyᵉ Hᵉ Hᵉ ∙hᵉ is-involution-map-involutionᵉ tᵉ)

  htpy-involutionᵉ : (sᵉ tᵉ : involutionᵉ Aᵉ) → UUᵉ lᵉ
  htpy-involutionᵉ sᵉ tᵉ =
    Σᵉ ( map-involutionᵉ sᵉ ~ᵉ map-involutionᵉ tᵉ)
      ( coherence-htpy-involutionᵉ sᵉ tᵉ)

  refl-htpy-involutionᵉ : (sᵉ : involutionᵉ Aᵉ) → htpy-involutionᵉ sᵉ sᵉ
  pr1ᵉ (refl-htpy-involutionᵉ sᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-involutionᵉ sᵉ) = refl-htpyᵉ

  htpy-eq-involutionᵉ : (sᵉ tᵉ : involutionᵉ Aᵉ) → sᵉ ＝ᵉ tᵉ → htpy-involutionᵉ sᵉ tᵉ
  htpy-eq-involutionᵉ sᵉ .sᵉ reflᵉ = refl-htpy-involutionᵉ sᵉ

  is-torsorial-htpy-involutionᵉ :
    (sᵉ : involutionᵉ Aᵉ) → is-torsorialᵉ (htpy-involutionᵉ sᵉ)
  is-torsorial-htpy-involutionᵉ sᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-involutionᵉ sᵉ))
      ( map-involutionᵉ sᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-htpyᵉ (is-involution-map-involutionᵉ sᵉ))

  is-equiv-htpy-eq-involutionᵉ :
    (sᵉ tᵉ : involutionᵉ Aᵉ) → is-equivᵉ (htpy-eq-involutionᵉ sᵉ tᵉ)
  is-equiv-htpy-eq-involutionᵉ sᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-involutionᵉ sᵉ)
      ( htpy-eq-involutionᵉ sᵉ)

  extensionality-involutionᵉ :
    (sᵉ tᵉ : involutionᵉ Aᵉ) → (sᵉ ＝ᵉ tᵉ) ≃ᵉ (htpy-involutionᵉ sᵉ tᵉ)
  pr1ᵉ (extensionality-involutionᵉ sᵉ tᵉ) = htpy-eq-involutionᵉ sᵉ tᵉ
  pr2ᵉ (extensionality-involutionᵉ sᵉ tᵉ) = is-equiv-htpy-eq-involutionᵉ sᵉ tᵉ

  eq-htpy-involutionᵉ : (sᵉ tᵉ : involutionᵉ Aᵉ) → htpy-involutionᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-htpy-involutionᵉ sᵉ tᵉ = map-inv-equivᵉ (extensionality-involutionᵉ sᵉ tᵉ)
```

### If `A` is `k`-truncated then the type of involutions is `k`-truncated

```agda
is-trunc-is-involutionᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → (fᵉ : Aᵉ → Aᵉ) → is-truncᵉ kᵉ (is-involutionᵉ fᵉ)
is-trunc-is-involutionᵉ kᵉ is-trunc-Aᵉ fᵉ =
  is-trunc-Πᵉ kᵉ λ xᵉ → is-trunc-Aᵉ (fᵉ (fᵉ xᵉ)) xᵉ

is-involution-Truncated-Typeᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → (Aᵉ → Aᵉ) → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (is-involution-Truncated-Typeᵉ kᵉ is-trunc-Aᵉ fᵉ) = is-involutionᵉ fᵉ
pr2ᵉ (is-involution-Truncated-Typeᵉ kᵉ is-trunc-Aᵉ fᵉ) =
  is-trunc-is-involutionᵉ kᵉ is-trunc-Aᵉ fᵉ

is-trunc-involutionᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} →
  is-truncᵉ kᵉ Aᵉ → is-truncᵉ kᵉ (involutionᵉ Aᵉ)
is-trunc-involutionᵉ kᵉ is-trunc-Aᵉ =
  is-trunc-Σᵉ
    ( is-trunc-function-typeᵉ kᵉ is-trunc-Aᵉ)
    ( is-trunc-is-involutionᵉ kᵉ (is-trunc-succ-is-truncᵉ kᵉ is-trunc-Aᵉ))

involution-Truncated-Typeᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) → Truncated-Typeᵉ lᵉ kᵉ → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (involution-Truncated-Typeᵉ kᵉ (Aᵉ ,ᵉ is-trunc-Aᵉ)) = involutionᵉ Aᵉ
pr2ᵉ (involution-Truncated-Typeᵉ kᵉ (Aᵉ ,ᵉ is-trunc-Aᵉ)) =
  is-trunc-involutionᵉ kᵉ is-trunc-Aᵉ
```

### Involutions on dependent function types

```agda
involution-Π-involution-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  ((xᵉ : Aᵉ) → involutionᵉ (Bᵉ xᵉ)) → involutionᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
pr1ᵉ (involution-Π-involution-famᵉ iᵉ) fᵉ xᵉ =
  map-involutionᵉ (iᵉ xᵉ) (fᵉ xᵉ)
pr2ᵉ (involution-Π-involution-famᵉ iᵉ) fᵉ =
  eq-htpyᵉ (λ xᵉ → is-involution-map-involutionᵉ (iᵉ xᵉ) (fᵉ xᵉ))
```

### Coherence of involutions

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : is-involutionᵉ fᵉ)
  where

  coherence-is-involutionᵉ : UUᵉ lᵉ
  coherence-is-involutionᵉ = fᵉ ·lᵉ Hᵉ ~ᵉ Hᵉ ·rᵉ fᵉ
```

## Examples

### The identity function is an involution

```agda
is-involution-idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-involutionᵉ (idᵉ {Aᵉ = Aᵉ})
is-involution-idᵉ = refl-htpyᵉ

id-involutionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → involutionᵉ Aᵉ
pr1ᵉ id-involutionᵉ = idᵉ
pr2ᵉ id-involutionᵉ = is-involution-idᵉ

involution-Pointed-Typeᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Pointed-Typeᵉ lᵉ
pr1ᵉ (involution-Pointed-Typeᵉ Aᵉ) = involutionᵉ Aᵉ
pr2ᵉ (involution-Pointed-Typeᵉ Aᵉ) = id-involutionᵉ
```