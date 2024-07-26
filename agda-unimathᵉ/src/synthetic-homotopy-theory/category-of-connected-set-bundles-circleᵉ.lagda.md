# The category of connected set bundles over the circle

```agda
module synthetic-homotopy-theory.category-of-connected-set-bundles-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subcategoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.category-of-families-of-setsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.circleᵉ
open import synthetic-homotopy-theory.connected-set-bundles-circleᵉ
```

</details>

## Idea

Theᵉ
[connectedᵉ setᵉ bundlesᵉ overᵉ theᵉ circle](synthetic-homotopy-theory.connected-set-bundles-circle.mdᵉ)
formᵉ aᵉ [largeᵉ category](category-theory.large-categories.md).ᵉ Thisᵉ largeᵉ
categoryᵉ isᵉ theᵉ categorificationᵉ ofᵉ theᵉ [poset](order-theory.posets.mdᵉ) ofᵉ theᵉ
[naturalᵉ numbersᵉ orderedᵉ byᵉ divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).ᵉ

## Definitions

### The category of connected set bundles over the circle

```agda
connected-set-bundle-𝕊¹-Large-Categoryᵉ : Large-Categoryᵉ (lsucᵉ) (_⊔ᵉ_)
connected-set-bundle-𝕊¹-Large-Categoryᵉ =
  large-category-Full-Large-Subcategoryᵉ
    ( Family-Of-Sets-Large-Categoryᵉ 𝕊¹ᵉ)
    ( is-connected-prop-set-bundle-𝕊¹ᵉ)
```