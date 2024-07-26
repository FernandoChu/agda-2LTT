# Shifting sequences

```agda
module foundation.shifting-sequencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ sequenceᵉ `fᵉ : ℕᵉ → A`ᵉ andᵉ anᵉ elementᵉ `aᵉ : A`ᵉ weᵉ defineᵉ
`shift-ℕᵉ aᵉ fᵉ : ℕᵉ → A`ᵉ byᵉ

```text
  shift-ℕᵉ aᵉ fᵉ zero-ℕᵉ :=ᵉ aᵉ
  shift-ℕᵉ aᵉ fᵉ (succ-ℕᵉ nᵉ) :=ᵉ fᵉ nᵉ
```

## Definition

```agda
shift-ℕᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ) (fᵉ : ℕᵉ → Aᵉ) → ℕᵉ → Aᵉ
shift-ℕᵉ aᵉ fᵉ zero-ℕᵉ = aᵉ
shift-ℕᵉ aᵉ fᵉ (succ-ℕᵉ nᵉ) = fᵉ nᵉ
```