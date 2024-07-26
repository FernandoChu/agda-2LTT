# Cauchy products of species of types

```agda
module species.cauchy-products-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-decompositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ Cauchyᵉ productᵉ ofᵉ twoᵉ speciesᵉ ofᵉ typesᵉ `S`ᵉ andᵉ `T`ᵉ onᵉ `X`ᵉ isᵉ definedᵉ asᵉ

```text
  Σᵉ (kᵉ : UUᵉ) (Σᵉ (k'ᵉ : UUᵉ) (Σᵉ (eᵉ : kᵉ +ᵉ k'ᵉ ≃ᵉ Xᵉ) S(kᵉ) ×ᵉ T(k'ᵉ)))
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  where

  cauchy-product-species-typesᵉ : species-typesᵉ l1ᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  cauchy-product-species-typesᵉ Xᵉ =
    Σᵉ ( binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
      ( λ dᵉ →
        Sᵉ (left-summand-binary-coproduct-Decompositionᵉ dᵉ) ×ᵉ
        Tᵉ (right-summand-binary-coproduct-Decompositionᵉ dᵉ))
```