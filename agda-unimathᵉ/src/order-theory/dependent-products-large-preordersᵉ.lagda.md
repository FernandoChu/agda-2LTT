# Dependent products large preorders

```agda
module order-theory.dependent-products-large-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ `Pᵉ : Iᵉ → Large-Preorderᵉ αᵉ β`ᵉ ofᵉ largeᵉ preordersᵉ indexedᵉ byᵉ aᵉ typeᵉ
`Iᵉ : UUᵉ l`,ᵉ theᵉ dependentᵉ prodcutᵉ ofᵉ theᵉ largeᵉ preordersᵉ `Pᵉ i`ᵉ isᵉ againᵉ aᵉ largeᵉ
preorder.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Pᵉ : Iᵉ → Large-Preorderᵉ αᵉ βᵉ)
  where

  type-Π-Large-Preorderᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ lᵉ)
  type-Π-Large-Preorderᵉ l1ᵉ = (iᵉ : Iᵉ) → type-Large-Preorderᵉ (Pᵉ iᵉ) l1ᵉ

  leq-prop-Π-Large-Preorderᵉ :
    Large-Relation-Propᵉ
      ( λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
      ( type-Π-Large-Preorderᵉ)
  leq-prop-Π-Large-Preorderᵉ xᵉ yᵉ =
    Π-Propᵉ Iᵉ (λ iᵉ → leq-prop-Large-Preorderᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))

  leq-Π-Large-Preorderᵉ :
    Large-Relationᵉ
      ( λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
      ( type-Π-Large-Preorderᵉ)
  leq-Π-Large-Preorderᵉ xᵉ yᵉ =
    type-Propᵉ (leq-prop-Π-Large-Preorderᵉ xᵉ yᵉ)

  is-prop-leq-Π-Large-Preorderᵉ :
    is-prop-Large-Relationᵉ type-Π-Large-Preorderᵉ leq-Π-Large-Preorderᵉ
  is-prop-leq-Π-Large-Preorderᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-prop-Π-Large-Preorderᵉ xᵉ yᵉ)

  refl-leq-Π-Large-Preorderᵉ :
    is-reflexive-Large-Relationᵉ type-Π-Large-Preorderᵉ leq-Π-Large-Preorderᵉ
  refl-leq-Π-Large-Preorderᵉ xᵉ iᵉ = refl-leq-Large-Preorderᵉ (Pᵉ iᵉ) (xᵉ iᵉ)

  transitive-leq-Π-Large-Preorderᵉ :
    is-transitive-Large-Relationᵉ type-Π-Large-Preorderᵉ leq-Π-Large-Preorderᵉ
  transitive-leq-Π-Large-Preorderᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ iᵉ =
    transitive-leq-Large-Preorderᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (zᵉ iᵉ) (Hᵉ iᵉ) (Kᵉ iᵉ)

  Π-Large-Preorderᵉ : Large-Preorderᵉ (λ l1ᵉ → αᵉ l1ᵉ ⊔ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
  type-Large-Preorderᵉ Π-Large-Preorderᵉ =
    type-Π-Large-Preorderᵉ
  leq-prop-Large-Preorderᵉ Π-Large-Preorderᵉ =
    leq-prop-Π-Large-Preorderᵉ
  refl-leq-Large-Preorderᵉ Π-Large-Preorderᵉ =
    refl-leq-Π-Large-Preorderᵉ
  transitive-leq-Large-Preorderᵉ Π-Large-Preorderᵉ =
    transitive-leq-Π-Large-Preorderᵉ
```