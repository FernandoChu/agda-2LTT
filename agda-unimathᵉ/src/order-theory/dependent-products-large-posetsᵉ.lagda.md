# Dependent products of large posets

```agda
module order-theory.dependent-products-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionalityᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-preordersᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ `Pᵉ : Iᵉ → Large-Posetᵉ αᵉ β`ᵉ indexedᵉ byᵉ aᵉ typeᵉ `Iᵉ : UUᵉ l`,ᵉ theᵉ
dependentᵉ productᵉ ofᵉ theᵉ largeᵉ posetsᵉ `Pᵉ i`ᵉ isᵉ againᵉ aᵉ largeᵉ poset.ᵉ

## Definitions

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  where

  large-preorder-Π-Large-Posetᵉ :
    Large-Preorderᵉ (λ l1ᵉ → αᵉ l1ᵉ ⊔ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
  large-preorder-Π-Large-Posetᵉ =
    Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  type-Π-Large-Posetᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ lᵉ)
  type-Π-Large-Posetᵉ =
    type-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  leq-prop-Π-Large-Posetᵉ :
    Large-Relation-Propᵉ
      ( λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
      ( type-Π-Large-Posetᵉ)
  leq-prop-Π-Large-Posetᵉ =
    leq-prop-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  leq-Π-Large-Posetᵉ :
    Large-Relationᵉ
      ( λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
      ( type-Π-Large-Posetᵉ)
  leq-Π-Large-Posetᵉ =
    leq-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  is-prop-leq-Π-Large-Posetᵉ :
    is-prop-Large-Relationᵉ type-Π-Large-Posetᵉ leq-Π-Large-Posetᵉ
  is-prop-leq-Π-Large-Posetᵉ =
    is-prop-leq-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  refl-leq-Π-Large-Posetᵉ :
    is-reflexive-Large-Relationᵉ type-Π-Large-Posetᵉ leq-Π-Large-Posetᵉ
  refl-leq-Π-Large-Posetᵉ =
    refl-leq-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  transitive-leq-Π-Large-Posetᵉ :
    is-transitive-Large-Relationᵉ type-Π-Large-Posetᵉ leq-Π-Large-Posetᵉ
  transitive-leq-Π-Large-Posetᵉ =
    transitive-leq-Π-Large-Preorderᵉ (λ iᵉ → large-preorder-Large-Posetᵉ (Pᵉ iᵉ))

  antisymmetric-leq-Π-Large-Posetᵉ :
    is-antisymmetric-Large-Relationᵉ type-Π-Large-Posetᵉ leq-Π-Large-Posetᵉ
  antisymmetric-leq-Π-Large-Posetᵉ xᵉ yᵉ Hᵉ Kᵉ =
    eq-htpyᵉ (λ iᵉ → antisymmetric-leq-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (Hᵉ iᵉ) (Kᵉ iᵉ))

  Π-Large-Posetᵉ : Large-Posetᵉ (λ l1ᵉ → αᵉ l1ᵉ ⊔ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
  large-preorder-Large-Posetᵉ Π-Large-Posetᵉ =
    large-preorder-Π-Large-Posetᵉ
  antisymmetric-leq-Large-Posetᵉ Π-Large-Posetᵉ =
    antisymmetric-leq-Π-Large-Posetᵉ
```