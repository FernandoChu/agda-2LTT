# Powers of loops

```agda
module synthetic-homotopy-theory.powers-of-loopsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterating-automorphismsᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Theᵉ **`n`-thᵉ powerᵉ ofᵉ aᵉ [loop](synthetic-homotopy-theory.loop-spaces.md)**ᵉ `ω`ᵉ
in aᵉ typeᵉ `A`ᵉ isᵉ definedᵉ byᵉ [iterated](foundation.iterating-functions.mdᵉ)
[concatenation](foundation.identity-types.mdᵉ) ofᵉ `ω`ᵉ with itself.ᵉ

## Definitions

### Powers of loops by natural numbers

```agda
power-nat-Ωᵉ :
  {lᵉ : Level} → ℕᵉ → (Aᵉ : Pointed-Typeᵉ lᵉ) → type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ
power-nat-Ωᵉ nᵉ Aᵉ ωᵉ = iterateᵉ nᵉ (concat'ᵉ (point-Pointed-Typeᵉ Aᵉ) ωᵉ) reflᵉ
```

### Powers of loops by integers

```agda
equiv-power-int-Ωᵉ :
  {lᵉ : Level} → ℤᵉ → (Aᵉ : Pointed-Typeᵉ lᵉ) → type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ ≃ᵉ type-Ωᵉ Aᵉ
equiv-power-int-Ωᵉ kᵉ Aᵉ ωᵉ =
  iterate-automorphism-ℤᵉ kᵉ (equiv-concat'ᵉ (point-Pointed-Typeᵉ Aᵉ) ωᵉ)

power-int-Ωᵉ :
  {lᵉ : Level} → ℤᵉ → (Aᵉ : Pointed-Typeᵉ lᵉ) → type-Ωᵉ Aᵉ → type-Ωᵉ Aᵉ
power-int-Ωᵉ kᵉ Aᵉ ωᵉ = map-equivᵉ (equiv-power-int-Ωᵉ kᵉ Aᵉ ωᵉ) reflᵉ
```

## Properties

### `reflⁿ = refl`

```agda
power-nat-refl-Ωᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) →
  power-nat-Ωᵉ nᵉ Aᵉ reflᵉ ＝ᵉ reflᵉ
power-nat-refl-Ωᵉ zero-ℕᵉ Aᵉ = reflᵉ
power-nat-refl-Ωᵉ (succ-ℕᵉ nᵉ) Aᵉ =
  right-whisker-concatᵉ (power-nat-refl-Ωᵉ nᵉ Aᵉ) reflᵉ
```

### `ωⁿ⁺¹ = ωⁿ ∙ ω`

```agda
power-nat-succ-Ωᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  power-nat-Ωᵉ (succ-ℕᵉ nᵉ) Aᵉ ωᵉ ＝ᵉ (power-nat-Ωᵉ nᵉ Aᵉ ωᵉ ∙ᵉ ωᵉ)
power-nat-succ-Ωᵉ nᵉ Aᵉ ωᵉ = reflᵉ

power-nat-succ-Ω'ᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  power-nat-Ωᵉ (succ-ℕᵉ nᵉ) Aᵉ ωᵉ ＝ᵉ (ωᵉ ∙ᵉ power-nat-Ωᵉ nᵉ Aᵉ ωᵉ)
power-nat-succ-Ω'ᵉ zero-ℕᵉ Aᵉ ωᵉ = invᵉ right-unitᵉ
power-nat-succ-Ω'ᵉ (succ-ℕᵉ nᵉ) Aᵉ ωᵉ =
  ( right-whisker-concatᵉ (power-nat-succ-Ω'ᵉ nᵉ Aᵉ ωᵉ) ωᵉ) ∙ᵉ
  ( assocᵉ ωᵉ (power-nat-Ωᵉ nᵉ Aᵉ ωᵉ) ωᵉ)
```

### `ωᵐ⁺ⁿ ＝ ωᵐ ∙ ωⁿ`

```agda
power-nat-add-Ωᵉ :
  {lᵉ : Level} (mᵉ nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  power-nat-Ωᵉ (mᵉ +ℕᵉ nᵉ) Aᵉ ωᵉ ＝ᵉ (power-nat-Ωᵉ mᵉ Aᵉ ωᵉ ∙ᵉ power-nat-Ωᵉ nᵉ Aᵉ ωᵉ)
power-nat-add-Ωᵉ mᵉ zero-ℕᵉ Aᵉ ωᵉ = invᵉ right-unitᵉ
power-nat-add-Ωᵉ mᵉ (succ-ℕᵉ nᵉ) Aᵉ ωᵉ =
  ( right-whisker-concatᵉ (power-nat-add-Ωᵉ mᵉ nᵉ Aᵉ ωᵉ) ωᵉ) ∙ᵉ
  ( assocᵉ (power-nat-Ωᵉ mᵉ Aᵉ ωᵉ) (power-nat-Ωᵉ nᵉ Aᵉ ωᵉ) ωᵉ)
```

### `ωᵐⁿ = (ωᵐ)ⁿ`

```agda
power-nat-mul-Ωᵉ :
  {lᵉ : Level} (mᵉ nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  power-nat-Ωᵉ (mᵉ *ℕᵉ nᵉ) Aᵉ ωᵉ ＝ᵉ power-nat-Ωᵉ mᵉ Aᵉ (power-nat-Ωᵉ nᵉ Aᵉ ωᵉ)
power-nat-mul-Ωᵉ zero-ℕᵉ nᵉ Aᵉ ωᵉ = reflᵉ
power-nat-mul-Ωᵉ (succ-ℕᵉ mᵉ) nᵉ Aᵉ ωᵉ =
  ( power-nat-add-Ωᵉ (mᵉ *ℕᵉ nᵉ) nᵉ Aᵉ ωᵉ) ∙ᵉ
  ( ( right-whisker-concatᵉ
      ( power-nat-mul-Ωᵉ mᵉ nᵉ Aᵉ ωᵉ)
      ( power-nat-Ωᵉ nᵉ Aᵉ ωᵉ)))

power-nat-mul-Ω'ᵉ :
  {lᵉ : Level} (mᵉ nᵉ : ℕᵉ) (Aᵉ : Pointed-Typeᵉ lᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  power-nat-Ωᵉ (mᵉ *ℕᵉ nᵉ) Aᵉ ωᵉ ＝ᵉ power-nat-Ωᵉ nᵉ Aᵉ (power-nat-Ωᵉ mᵉ Aᵉ ωᵉ)
power-nat-mul-Ω'ᵉ mᵉ nᵉ Aᵉ ωᵉ =
  ( apᵉ (λ uᵉ → power-nat-Ωᵉ uᵉ Aᵉ ωᵉ) (commutative-mul-ℕᵉ mᵉ nᵉ)) ∙ᵉ
  ( power-nat-mul-Ωᵉ nᵉ mᵉ Aᵉ ωᵉ)
```

### The action on identifications of a function preserves powers

```agda
map-power-nat-Ωᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (ωᵉ : type-Ωᵉ Aᵉ) →
  map-Ωᵉ fᵉ (power-nat-Ωᵉ nᵉ Aᵉ ωᵉ) ＝ᵉ power-nat-Ωᵉ nᵉ Bᵉ (map-Ωᵉ fᵉ ωᵉ)
map-power-nat-Ωᵉ zero-ℕᵉ {Aᵉ} {Bᵉ} fᵉ ωᵉ = preserves-refl-map-Ωᵉ fᵉ
map-power-nat-Ωᵉ (succ-ℕᵉ nᵉ) {Aᵉ} {Bᵉ} fᵉ ωᵉ =
  ( preserves-mul-map-Ωᵉ fᵉ) ∙ᵉ
  ( right-whisker-concatᵉ (map-power-nat-Ωᵉ nᵉ fᵉ ωᵉ) (map-Ωᵉ fᵉ ωᵉ))
```