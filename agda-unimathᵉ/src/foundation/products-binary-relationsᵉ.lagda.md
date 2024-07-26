# Products of binary relations

```agda
module foundation.products-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ relationsᵉ `R`ᵉ andᵉ `S`,ᵉ theirᵉ productᵉ isᵉ givenᵉ byᵉ
`(Rᵉ ×ᵉ Sᵉ) (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b')`ᵉ iffᵉ `Rᵉ aᵉ a'`ᵉ andᵉ `Sᵉ bᵉ b'`.ᵉ

## Definition

### The product of two relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relation-Propᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : Relation-Propᵉ l4ᵉ Bᵉ)
  where

  product-Relation-Propᵉ :
    Relation-Propᵉ (l2ᵉ ⊔ l4ᵉ) (Aᵉ ×ᵉ Bᵉ)
  product-Relation-Propᵉ (aᵉ ,ᵉ bᵉ) (a'ᵉ ,ᵉ b'ᵉ) =
    product-Propᵉ
      ( Rᵉ aᵉ a'ᵉ)
      ( Sᵉ bᵉ b'ᵉ)
```