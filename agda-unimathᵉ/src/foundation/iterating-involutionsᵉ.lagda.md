# Iterating involutions

```agda
module foundation.iterating-involutionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.involutionsᵉ
open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.identity-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

### Iterating involutions

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (fᵉ : Xᵉ → Xᵉ) (Pᵉ : is-involutionᵉ fᵉ)
  where

  iterate-involutionᵉ :
    (nᵉ : ℕᵉ) (xᵉ : Xᵉ) → iterateᵉ nᵉ fᵉ xᵉ ＝ᵉ iterateᵉ (nat-Finᵉ 2 (mod-two-ℕᵉ nᵉ)) fᵉ xᵉ
  iterate-involutionᵉ zero-ℕᵉ xᵉ = reflᵉ
  iterate-involutionᵉ (succ-ℕᵉ nᵉ) xᵉ =
    apᵉ fᵉ (iterate-involutionᵉ nᵉ xᵉ) ∙ᵉ (cases-iterate-involutionᵉ (mod-two-ℕᵉ nᵉ))
    where
    cases-iterate-involutionᵉ :
      (kᵉ : Finᵉ 2ᵉ) →
      fᵉ (iterateᵉ (nat-Finᵉ 2 kᵉ) fᵉ xᵉ) ＝ᵉ iterateᵉ (nat-Finᵉ 2 (succ-Finᵉ 2 kᵉ)) fᵉ xᵉ
    cases-iterate-involutionᵉ (inlᵉ (inrᵉ _)) = reflᵉ
    cases-iterate-involutionᵉ (inrᵉ _) = Pᵉ xᵉ
```