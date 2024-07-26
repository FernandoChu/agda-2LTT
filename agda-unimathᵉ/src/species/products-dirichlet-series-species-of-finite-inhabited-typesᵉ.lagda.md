# Products of Dirichlet series of species of finite inhabited types

```agda
module species.products-dirichlet-series-species-of-finite-inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import species.dirichlet-series-species-of-finite-inhabited-typesᵉ
open import species.species-of-finite-inhabited-typesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ twoᵉ Dirichletᵉ seriesᵉ isᵉ theᵉ pointwiseᵉ product.ᵉ

## Definition

```agda
product-dirichlet-series-species-Inhabited-𝔽ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} → species-Inhabited-𝔽ᵉ l1ᵉ l2ᵉ →
  species-Inhabited-𝔽ᵉ l1ᵉ l3ᵉ →
  UUᵉ l4ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
product-dirichlet-series-species-Inhabited-𝔽ᵉ Sᵉ Tᵉ Xᵉ =
  dirichlet-series-species-Inhabited-𝔽ᵉ Sᵉ Xᵉ ×ᵉ
  dirichlet-series-species-Inhabited-𝔽ᵉ Tᵉ Xᵉ
```