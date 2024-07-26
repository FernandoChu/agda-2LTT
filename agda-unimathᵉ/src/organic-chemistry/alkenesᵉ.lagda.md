# Alkenes

```agda
module organic-chemistry.alkenesᵉ where
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

Anᵉ **n-alkene**ᵉ isᵉ aᵉ hydrocarbonᵉ equippedᵉ with aᵉ choiceᵉ ofᵉ $n$ᵉ carbons,ᵉ eachᵉ ofᵉ
whichᵉ hasᵉ aᵉ doubleᵉ bond.ᵉ Forᵉ anᵉ n-alkene,ᵉ theᵉ embeddingᵉ fromᵉ theᵉ givenᵉ typeᵉ (theᵉ
firstᵉ componentᵉ ofᵉ theᵉ n-alkeneᵉ structureᵉ) specifiesᵉ whichᵉ carbonsᵉ haveᵉ doubleᵉ
bonds.ᵉ Forᵉ example,ᵉ 1-buteneᵉ andᵉ but-2-eneᵉ haveᵉ theᵉ sameᵉ geometry,ᵉ andᵉ theᵉ
embeddingᵉ isᵉ whatᵉ differentiatesᵉ themᵉ (whileᵉ theᵉ thirdᵉ tautometer,ᵉ isobutylene,ᵉ
isᵉ branched,ᵉ thusᵉ hasᵉ aᵉ differentᵉ geometry).ᵉ

## Definition

```agda
n-alkeneᵉ : {l1ᵉ l2ᵉ : Level} → hydrocarbonᵉ l1ᵉ l2ᵉ → ℕᵉ → UUᵉ (lsuc lzero ⊔ l1ᵉ ⊔ l2ᵉ)
n-alkeneᵉ Hᵉ nᵉ =
  Σᵉ (UU-Finᵉ lzero nᵉ) λ carbonsᵉ →
    Σᵉ ( type-UU-Finᵉ nᵉ carbonsᵉ ↪ᵉ vertex-hydrocarbonᵉ Hᵉ)
      ( λ embed-carbonsᵉ →
        ( cᵉ : type-UU-Finᵉ nᵉ carbonsᵉ) →
        pr1ᵉ (has-double-bond-hydrocarbonᵉ Hᵉ (pr1ᵉ embed-carbonsᵉ cᵉ)))
```