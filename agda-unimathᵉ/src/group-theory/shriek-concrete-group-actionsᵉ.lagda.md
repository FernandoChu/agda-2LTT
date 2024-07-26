# Shriek of concrete group homomorphisms

```agda
module group-theory.shriek-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
```

</details>

## Definition

### Operations on group actions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

  left-adjoint-subst-action-Concrete-Groupᵉ :
    {lᵉ : Level} → (action-Concrete-Groupᵉ lᵉ Gᵉ) →
    (action-Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ) Hᵉ)
  left-adjoint-subst-action-Concrete-Groupᵉ Xᵉ yᵉ =
    trunc-Setᵉ
      ( Σᵉ ( classifying-type-Concrete-Groupᵉ Gᵉ)
          ( λ xᵉ →
            type-Setᵉ (Xᵉ xᵉ) ×ᵉ Idᵉ (classifying-map-hom-Concrete-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) yᵉ))
```