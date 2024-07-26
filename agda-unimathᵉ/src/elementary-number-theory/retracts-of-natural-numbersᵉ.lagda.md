# Retracts of the type of natural numbers

```agda
module elementary-number-theory.retracts-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-mapsᵉ
open import foundation.retractionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Ifᵉ `iᵉ : Aᵉ → ℕ`ᵉ hasᵉ aᵉ retraction,ᵉ thenᵉ `i`ᵉ isᵉ aᵉ decidableᵉ map.ᵉ

```agda
is-decidable-map-retraction-ℕᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (iᵉ : Aᵉ → ℕᵉ) → retractionᵉ iᵉ → is-decidable-mapᵉ iᵉ
is-decidable-map-retraction-ℕᵉ =
  is-decidable-map-retractionᵉ has-decidable-equality-ℕᵉ
```