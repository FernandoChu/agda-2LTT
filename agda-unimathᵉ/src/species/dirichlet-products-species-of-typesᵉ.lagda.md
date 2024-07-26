# Dirichlet products of species of types

```agda
module species.dirichlet-products-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.product-decompositionsᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ Dirichletᵉ productᵉ ofᵉ twoᵉ speciesᵉ ofᵉ typesᵉ `S`ᵉ andᵉ `T`ᵉ onᵉ `X`ᵉ isᵉ definedᵉ asᵉ

```text
  Σᵉ (kᵉ : UUᵉ) (Σᵉ (k'ᵉ : UUᵉ) (Σᵉ (eᵉ : kᵉ ×ᵉ k'ᵉ ≃ᵉ Xᵉ) S(kᵉ) ×ᵉ T(k'ᵉ)))
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  where

  dirichlet-product-species-typesᵉ : species-typesᵉ l1ᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  dirichlet-product-species-typesᵉ Xᵉ =
    Σᵉ ( binary-product-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ)
      ( λ dᵉ →
        Sᵉ (left-summand-binary-product-Decompositionᵉ dᵉ) ×ᵉ
        Tᵉ (right-summand-binary-product-Decompositionᵉ dᵉ))
```