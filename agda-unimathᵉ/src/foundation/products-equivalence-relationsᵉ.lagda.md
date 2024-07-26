# Products of equivalence relataions

```agda
module foundation.products-equivalence-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.products-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalence-relationsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ equivalenceᵉ relationsᵉ `R`ᵉ andᵉ `S`,ᵉ theirᵉ productᵉ isᵉ anᵉ equivalenceᵉ
relation.ᵉ

## Definition

### The product of two equivalence relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  reflexive-product-Relation-Propᵉ :
    is-reflexive-Relation-Propᵉ
      ( product-Relation-Propᵉ
        ( prop-equivalence-relationᵉ Rᵉ)
        ( prop-equivalence-relationᵉ Sᵉ))
  pr1ᵉ (reflexive-product-Relation-Propᵉ xᵉ) = refl-equivalence-relationᵉ Rᵉ (pr1ᵉ xᵉ)
  pr2ᵉ (reflexive-product-Relation-Propᵉ xᵉ) = refl-equivalence-relationᵉ Sᵉ (pr2ᵉ xᵉ)

  symmetric-product-Relation-Propᵉ :
    is-symmetric-Relation-Propᵉ
      ( product-Relation-Propᵉ
        ( prop-equivalence-relationᵉ Rᵉ)
        ( prop-equivalence-relationᵉ Sᵉ))
  pr1ᵉ (symmetric-product-Relation-Propᵉ xᵉ yᵉ (pᵉ ,ᵉ qᵉ)) =
    symmetric-equivalence-relationᵉ Rᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) pᵉ
  pr2ᵉ (symmetric-product-Relation-Propᵉ xᵉ yᵉ (pᵉ ,ᵉ qᵉ)) =
    symmetric-equivalence-relationᵉ Sᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ) qᵉ

  transitive-product-Relation-Propᵉ :
    is-transitive-Relation-Propᵉ
      ( product-Relation-Propᵉ
        ( prop-equivalence-relationᵉ Rᵉ)
        ( prop-equivalence-relationᵉ Sᵉ))
  pr1ᵉ (transitive-product-Relation-Propᵉ xᵉ yᵉ zᵉ (pᵉ ,ᵉ qᵉ) (p'ᵉ ,ᵉ q'ᵉ)) =
    transitive-equivalence-relationᵉ Rᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) (pr1ᵉ zᵉ) pᵉ p'ᵉ
  pr2ᵉ (transitive-product-Relation-Propᵉ xᵉ yᵉ zᵉ (pᵉ ,ᵉ qᵉ) (p'ᵉ ,ᵉ q'ᵉ)) =
    transitive-equivalence-relationᵉ Sᵉ (pr2ᵉ xᵉ) (pr2ᵉ yᵉ) (pr2ᵉ zᵉ) qᵉ q'ᵉ

  product-equivalence-relationᵉ : equivalence-relationᵉ (l2ᵉ ⊔ l4ᵉ) (Aᵉ ×ᵉ Bᵉ)
  pr1ᵉ product-equivalence-relationᵉ =
    product-Relation-Propᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( prop-equivalence-relationᵉ Sᵉ)
  pr1ᵉ (pr2ᵉ product-equivalence-relationᵉ) = reflexive-product-Relation-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ product-equivalence-relationᵉ)) = symmetric-product-Relation-Propᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ product-equivalence-relationᵉ)) =
    transitive-product-Relation-Propᵉ
```