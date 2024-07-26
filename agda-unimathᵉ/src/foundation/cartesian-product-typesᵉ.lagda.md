# Cartesian product types

```agda
module foundation.cartesian-product-typesᵉ where

open import foundation-core.cartesian-product-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Properties

### Transport in a family of cartesian products

```agda
tr-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {a0ᵉ a1ᵉ : Aᵉ}
  (Bᵉ Cᵉ : Aᵉ → UUᵉ l2ᵉ) (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) (uᵉ : Bᵉ a0ᵉ ×ᵉ Cᵉ a0ᵉ) →
  (trᵉ (λ aᵉ → Bᵉ aᵉ ×ᵉ Cᵉ aᵉ) pᵉ uᵉ) ＝ᵉ (pairᵉ (trᵉ Bᵉ pᵉ (pr1ᵉ uᵉ)) (trᵉ Cᵉ pᵉ (pr2ᵉ uᵉ)))
tr-productᵉ Bᵉ Cᵉ reflᵉ uᵉ = reflᵉ
```

### Subuniverses closed under cartesian product types

```agda
is-closed-under-products-subuniversesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Rᵉ : subuniverseᵉ (l1ᵉ ⊔ l3ᵉ) l5ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
is-closed-under-products-subuniversesᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Pᵉ Qᵉ Rᵉ =
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l3ᵉ} →
  is-in-subuniverseᵉ Pᵉ Xᵉ → is-in-subuniverseᵉ Qᵉ Yᵉ → is-in-subuniverseᵉ Rᵉ (Xᵉ ×ᵉ Yᵉ)

is-closed-under-products-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-closed-under-products-subuniverseᵉ Pᵉ =
  is-closed-under-products-subuniversesᵉ Pᵉ Pᵉ Pᵉ
```