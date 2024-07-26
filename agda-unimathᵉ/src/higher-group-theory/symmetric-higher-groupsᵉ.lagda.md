# Symmetric higher groups

```agda
module higher-group-theory.symmetric-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.connected-components-universesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ symmetricᵉ higherᵉ groupᵉ ofᵉ aᵉ typeᵉ `X`ᵉ isᵉ theᵉ connectedᵉ componentᵉ ofᵉ theᵉ
universeᵉ atᵉ `X`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ)
  where

  classifying-type-symmetric-∞-Groupᵉ : UUᵉ (lsuc lᵉ)
  classifying-type-symmetric-∞-Groupᵉ = component-UUᵉ Xᵉ

  shape-symmetric-∞-Groupᵉ : classifying-type-symmetric-∞-Groupᵉ
  shape-symmetric-∞-Groupᵉ =
    pairᵉ Xᵉ (refl-mere-equivᵉ Xᵉ)

  classifying-pointed-type-symmetric-∞-Groupᵉ : Pointed-Typeᵉ (lsuc lᵉ)
  classifying-pointed-type-symmetric-∞-Groupᵉ =
    pairᵉ
      classifying-type-symmetric-∞-Groupᵉ
      shape-symmetric-∞-Groupᵉ

  is-0-connected-classifying-type-symmetric-∞-Groupᵉ :
    is-0-connectedᵉ classifying-type-symmetric-∞-Groupᵉ
  is-0-connected-classifying-type-symmetric-∞-Groupᵉ =
    is-0-connected-component-UUᵉ Xᵉ

  symmetric-∞-Groupᵉ : ∞-Groupᵉ (lsuc lᵉ)
  symmetric-∞-Groupᵉ =
    pairᵉ
      classifying-pointed-type-symmetric-∞-Groupᵉ
      is-0-connected-classifying-type-symmetric-∞-Groupᵉ
```