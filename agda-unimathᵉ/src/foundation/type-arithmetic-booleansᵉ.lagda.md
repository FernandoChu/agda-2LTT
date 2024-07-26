# Type arithmetic with the booleans

```agda
module foundation.type-arithmetic-booleansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Weᵉ proveᵉ arithmeticalᵉ lawsᵉ involvingᵉ theᵉ booleansᵉ

## Laws

### Dependent pairs over booleans are equivalent to coproducts

```agda
module _
  {lᵉ : Level} (Aᵉ : boolᵉ → UUᵉ lᵉ)
  where

  map-Σ-bool-coproductᵉ : Σᵉ boolᵉ Aᵉ → Aᵉ trueᵉ +ᵉ Aᵉ falseᵉ
  map-Σ-bool-coproductᵉ (pairᵉ trueᵉ aᵉ) = inlᵉ aᵉ
  map-Σ-bool-coproductᵉ (pairᵉ falseᵉ aᵉ) = inrᵉ aᵉ

  map-inv-Σ-bool-coproductᵉ : Aᵉ trueᵉ +ᵉ Aᵉ falseᵉ → Σᵉ boolᵉ Aᵉ
  map-inv-Σ-bool-coproductᵉ (inlᵉ aᵉ) = pairᵉ trueᵉ aᵉ
  map-inv-Σ-bool-coproductᵉ (inrᵉ aᵉ) = pairᵉ falseᵉ aᵉ

  is-section-map-inv-Σ-bool-coproductᵉ :
    ( map-Σ-bool-coproductᵉ ∘ᵉ map-inv-Σ-bool-coproductᵉ) ~ᵉ idᵉ
  is-section-map-inv-Σ-bool-coproductᵉ (inlᵉ aᵉ) = reflᵉ
  is-section-map-inv-Σ-bool-coproductᵉ (inrᵉ aᵉ) = reflᵉ

  is-retraction-map-inv-Σ-bool-coproductᵉ :
    ( map-inv-Σ-bool-coproductᵉ ∘ᵉ map-Σ-bool-coproductᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-Σ-bool-coproductᵉ (pairᵉ trueᵉ aᵉ) = reflᵉ
  is-retraction-map-inv-Σ-bool-coproductᵉ (pairᵉ falseᵉ aᵉ) = reflᵉ

  is-equiv-map-Σ-bool-coproductᵉ : is-equivᵉ map-Σ-bool-coproductᵉ
  is-equiv-map-Σ-bool-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-Σ-bool-coproductᵉ
      is-section-map-inv-Σ-bool-coproductᵉ
      is-retraction-map-inv-Σ-bool-coproductᵉ

  equiv-Σ-bool-coproductᵉ : Σᵉ boolᵉ Aᵉ ≃ᵉ (Aᵉ trueᵉ +ᵉ Aᵉ falseᵉ)
  pr1ᵉ equiv-Σ-bool-coproductᵉ = map-Σ-bool-coproductᵉ
  pr2ᵉ equiv-Σ-bool-coproductᵉ = is-equiv-map-Σ-bool-coproductᵉ

  is-equiv-map-inv-Σ-bool-coproductᵉ : is-equivᵉ map-inv-Σ-bool-coproductᵉ
  is-equiv-map-inv-Σ-bool-coproductᵉ =
    is-equiv-is-invertibleᵉ
      map-Σ-bool-coproductᵉ
      is-retraction-map-inv-Σ-bool-coproductᵉ
      is-section-map-inv-Σ-bool-coproductᵉ

  inv-equiv-Σ-bool-coproductᵉ : (Aᵉ trueᵉ +ᵉ Aᵉ falseᵉ) ≃ᵉ Σᵉ boolᵉ Aᵉ
  pr1ᵉ inv-equiv-Σ-bool-coproductᵉ = map-inv-Σ-bool-coproductᵉ
  pr2ᵉ inv-equiv-Σ-bool-coproductᵉ = is-equiv-map-inv-Σ-bool-coproductᵉ
```