# Counting the elements in Maybe

```agda
module univalent-combinatorics.counting-maybeᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.identity-typesᵉ
open import foundation.maybeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
```

</details>

## Idea

Theᵉ elementsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ canᵉ beᵉ countedᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ elementsᵉ ofᵉ
`Maybeᵉ X`ᵉ canᵉ beᵉ counted.ᵉ

```agda
count-Maybeᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ Xᵉ → countᵉ (Maybeᵉ Xᵉ)
count-Maybeᵉ {lᵉ} {Xᵉ} eᵉ = count-coproductᵉ eᵉ count-unitᵉ

abstract
  is-nonzero-number-of-elements-count-Maybeᵉ :
    {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ (Maybeᵉ Xᵉ)) →
    is-nonzero-ℕᵉ (number-of-elements-countᵉ eᵉ)
  is-nonzero-number-of-elements-count-Maybeᵉ eᵉ pᵉ =
    is-empty-is-zero-number-of-elements-countᵉ eᵉ pᵉ exception-Maybeᵉ

is-successor-number-of-elements-count-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ (Maybeᵉ Xᵉ)) →
  is-successor-ℕᵉ (number-of-elements-countᵉ eᵉ)
is-successor-number-of-elements-count-Maybeᵉ eᵉ =
  is-successor-is-nonzero-ℕᵉ (is-nonzero-number-of-elements-count-Maybeᵉ eᵉ)

count-count-Maybeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ (Maybeᵉ Xᵉ) → countᵉ Xᵉ
count-count-Maybeᵉ (pairᵉ kᵉ eᵉ) with
  is-successor-number-of-elements-count-Maybeᵉ (pairᵉ kᵉ eᵉ)
... | pairᵉ lᵉ reflᵉ = pairᵉ lᵉ (equiv-equiv-Maybeᵉ eᵉ)
```