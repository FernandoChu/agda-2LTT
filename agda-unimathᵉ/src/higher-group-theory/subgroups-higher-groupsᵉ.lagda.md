# Subgroups of higher groups

```agda
module higher-group-theory.subgroups-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ subgroupᵉ ofᵉ aᵉ higherᵉ groupᵉ isᵉ aᵉ pointedᵉ setᵉ bundleᵉ overᵉ itsᵉ classifyingᵉ typeᵉ
with connectedᵉ totalᵉ space.ᵉ

## Definition

```agda
subgroup-action-∞-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ) →
  classifying-type-∞-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subgroup-action-∞-Groupᵉ l2ᵉ Gᵉ uᵉ =
  Σᵉ ( classifying-type-∞-Groupᵉ Gᵉ → Setᵉ l2ᵉ)
    ( λ Xᵉ →
      ( type-Setᵉ (Xᵉ uᵉ)) ×ᵉ
      ( is-0-connectedᵉ (Σᵉ (classifying-type-∞-Groupᵉ Gᵉ) (type-Setᵉ ∘ᵉ Xᵉ))))

subgroup-∞-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subgroup-∞-Groupᵉ l2ᵉ Gᵉ = subgroup-action-∞-Groupᵉ l2ᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : subgroup-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  set-action-subgroup-∞-Groupᵉ :
    classifying-type-∞-Groupᵉ Gᵉ → Setᵉ l2ᵉ
  set-action-subgroup-∞-Groupᵉ = pr1ᵉ Hᵉ

  action-subgroup-∞-Groupᵉ : classifying-type-∞-Groupᵉ Gᵉ → UUᵉ l2ᵉ
  action-subgroup-∞-Groupᵉ = type-Setᵉ ∘ᵉ set-action-subgroup-∞-Groupᵉ

  classifying-type-subgroup-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-type-subgroup-∞-Groupᵉ =
    Σᵉ (classifying-type-∞-Groupᵉ Gᵉ) action-subgroup-∞-Groupᵉ

  shape-subgroup-∞-Groupᵉ : classifying-type-subgroup-∞-Groupᵉ
  pr1ᵉ shape-subgroup-∞-Groupᵉ = shape-∞-Groupᵉ Gᵉ
  pr2ᵉ shape-subgroup-∞-Groupᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

  classifying-pointed-type-subgroup-∞-Groupᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ classifying-pointed-type-subgroup-∞-Groupᵉ =
    classifying-type-subgroup-∞-Groupᵉ
  pr2ᵉ classifying-pointed-type-subgroup-∞-Groupᵉ =
    shape-subgroup-∞-Groupᵉ

  is-connected-classifying-type-subgroup-∞-Groupᵉ :
    is-0-connectedᵉ classifying-type-subgroup-∞-Groupᵉ
  is-connected-classifying-type-subgroup-∞-Groupᵉ = pr2ᵉ (pr2ᵉ Hᵉ)

  ∞-group-subgroup-∞-Groupᵉ : ∞-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ ∞-group-subgroup-∞-Groupᵉ = classifying-pointed-type-subgroup-∞-Groupᵉ
  pr2ᵉ ∞-group-subgroup-∞-Groupᵉ = is-connected-classifying-type-subgroup-∞-Groupᵉ
```