# Multivariable decidable relations

```agda
module foundation.multivariable-decidable-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-subtypesᵉ
open import foundation.multivariable-correspondencesᵉ
open import foundation.multivariable-relationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ typesᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : Finᵉ n`.ᵉ Anᵉ `n`-aryᵉ decidableᵉ
relationᵉ onᵉ theᵉ tuplesᵉ ofᵉ elementsᵉ ofᵉ theᵉ `Aᵉ i`ᵉ isᵉ aᵉ decidableᵉ subtypeᵉ ofᵉ theᵉ
productᵉ ofᵉ theᵉ `Aᵉ i`.ᵉ

## Definition

```agda
multivariable-decidable-relationᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (nᵉ : ℕᵉ) (Aᵉ : Finᵉ nᵉ → UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
multivariable-decidable-relationᵉ l2ᵉ nᵉ Aᵉ =
  decidable-subtypeᵉ l2ᵉ ((iᵉ : Finᵉ nᵉ) → Aᵉ iᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : Finᵉ nᵉ → UUᵉ l1ᵉ}
  (Rᵉ : multivariable-decidable-relationᵉ l2ᵉ nᵉ Aᵉ)
  where

  multivariable-relation-multivariable-decidable-relationᵉ :
    multivariable-relationᵉ l2ᵉ nᵉ Aᵉ
  multivariable-relation-multivariable-decidable-relationᵉ =
    subtype-decidable-subtypeᵉ Rᵉ

  multivariable-correspondence-multivariable-decidable-relationᵉ :
    multivariable-correspondenceᵉ l2ᵉ nᵉ Aᵉ
  multivariable-correspondence-multivariable-decidable-relationᵉ =
    is-in-decidable-subtypeᵉ Rᵉ
```