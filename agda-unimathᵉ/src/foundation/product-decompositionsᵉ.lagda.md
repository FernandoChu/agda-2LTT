# Product decompositions

```agda
module foundation.product-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Definitions

### Binary product decomposition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ)
  where

  binary-product-Decompositionᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  binary-product-Decompositionᵉ =
    Σᵉ (UUᵉ l2ᵉ) (λ Aᵉ → Σᵉ (UUᵉ l3ᵉ) (λ Bᵉ → Xᵉ ≃ᵉ (Aᵉ ×ᵉ Bᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  (dᵉ : binary-product-Decompositionᵉ l2ᵉ l3ᵉ Xᵉ)
  where

  left-summand-binary-product-Decompositionᵉ : UUᵉ l2ᵉ
  left-summand-binary-product-Decompositionᵉ = pr1ᵉ dᵉ

  right-summand-binary-product-Decompositionᵉ : UUᵉ l3ᵉ
  right-summand-binary-product-Decompositionᵉ = pr1ᵉ (pr2ᵉ dᵉ)

  matching-correspondence-binary-product-Decompositionᵉ :
    Xᵉ ≃ᵉ
    ( left-summand-binary-product-Decompositionᵉ ×ᵉ
      right-summand-binary-product-Decompositionᵉ)
  matching-correspondence-binary-product-Decompositionᵉ = pr2ᵉ (pr2ᵉ dᵉ)
```