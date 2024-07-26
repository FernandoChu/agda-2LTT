# Products of elements in a monoid

```agda
module group-theory.products-of-elements-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ
```

</details>

## Idea

Givenᵉ aᵉ listᵉ ofᵉ elementsᵉ in aᵉ monoid,ᵉ theᵉ elementsᵉ in thatᵉ listᵉ canᵉ beᵉ
multiplied.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  mul-list-Monoidᵉ : listᵉ (type-Monoidᵉ Mᵉ) → type-Monoidᵉ Mᵉ
  mul-list-Monoidᵉ nilᵉ = unit-Monoidᵉ Mᵉ
  mul-list-Monoidᵉ (consᵉ xᵉ lᵉ) = mul-Monoidᵉ Mᵉ xᵉ (mul-list-Monoidᵉ lᵉ)
```

## Properties

### Distributivity of multiplication over concatenation

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  distributive-mul-concat-list-Monoidᵉ :
    (l1ᵉ l2ᵉ : listᵉ (type-Monoidᵉ Mᵉ)) →
    Idᵉ
      ( mul-list-Monoidᵉ Mᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( mul-Monoidᵉ Mᵉ (mul-list-Monoidᵉ Mᵉ l1ᵉ) (mul-list-Monoidᵉ Mᵉ l2ᵉ))
  distributive-mul-concat-list-Monoidᵉ nilᵉ l2ᵉ =
    invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ (mul-list-Monoidᵉ Mᵉ l2ᵉ))
  distributive-mul-concat-list-Monoidᵉ (consᵉ xᵉ l1ᵉ) l2ᵉ =
    ( apᵉ (mul-Monoidᵉ Mᵉ xᵉ) (distributive-mul-concat-list-Monoidᵉ l1ᵉ l2ᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-mul-Monoidᵉ Mᵉ xᵉ
        ( mul-list-Monoidᵉ Mᵉ l1ᵉ)
        ( mul-list-Monoidᵉ Mᵉ l2ᵉ)))
```