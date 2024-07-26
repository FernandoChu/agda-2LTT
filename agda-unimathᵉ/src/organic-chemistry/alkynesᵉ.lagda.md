# Alkynes

```agda
module organic-chemistry.alkynesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.universe-levelsᵉ

open import organic-chemistry.hydrocarbonsᵉ
open import organic-chemistry.saturated-carbonsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ **n-alkyne**ᵉ isᵉ aᵉ hydrocarbonᵉ equippedᵉ with aᵉ choiceᵉ ofᵉ $n$ᵉ carbons,ᵉ eachᵉ ofᵉ
whichᵉ hasᵉ aᵉ tripleᵉ bond.ᵉ

## Definition

```agda
n-alkyneᵉ : {l1ᵉ l2ᵉ : Level} → hydrocarbonᵉ l1ᵉ l2ᵉ → ℕᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
n-alkyneᵉ {l1ᵉ} {l2ᵉ} Hᵉ nᵉ =
  Σᵉ ( UU-Finᵉ l1ᵉ nᵉ)
    ( λ carbonsᵉ →
      Σᵉ ( type-UU-Finᵉ nᵉ carbonsᵉ ↪ᵉ vertex-hydrocarbonᵉ Hᵉ)
        ( λ embed-carbonsᵉ →
          (cᵉ : type-UU-Finᵉ nᵉ carbonsᵉ) →
          has-triple-bond-hydrocarbonᵉ Hᵉ (pr1ᵉ embed-carbonsᵉ cᵉ)))
```