# Additive orders of elements of rings

```agda
module ring-theory.additive-orders-of-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.normal-subgroupsᵉ
open import group-theory.orders-of-elements-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import ring-theory.integer-multiples-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **additiveᵉ order**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ
isᵉ theᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) ofᵉ theᵉ
[groupᵉ `ℤ`ᵉ ofᵉ integers](elementary-number-theory.group-of-integers.mdᵉ)
consistingᵉ ofᵉ allᵉ [integers](elementary-number-theory.integers.mdᵉ) `k`ᵉ suchᵉ thatᵉ
`kxᵉ ＝ᵉ 0`.ᵉ

## Definitions

### Additive orders of elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  where

  additive-order-element-Ringᵉ : Normal-Subgroupᵉ lᵉ ℤ-Groupᵉ
  additive-order-element-Ringᵉ = order-element-Groupᵉ (group-Ringᵉ Rᵉ) xᵉ

  subgroup-additive-order-element-Ringᵉ : Subgroupᵉ lᵉ ℤ-Groupᵉ
  subgroup-additive-order-element-Ringᵉ =
    subgroup-order-element-Groupᵉ (group-Ringᵉ Rᵉ) xᵉ

  subset-additive-order-element-Ringᵉ : subset-Groupᵉ lᵉ ℤ-Groupᵉ
  subset-additive-order-element-Ringᵉ =
    subset-order-element-Groupᵉ (group-Ringᵉ Rᵉ) xᵉ

  is-in-additive-order-element-Ringᵉ : ℤᵉ → UUᵉ lᵉ
  is-in-additive-order-element-Ringᵉ =
    is-in-order-element-Groupᵉ (group-Ringᵉ Rᵉ) xᵉ
```

### Divisibility of additive orders of elements of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  div-additive-order-element-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  div-additive-order-element-Ringᵉ =
    div-order-element-Groupᵉ (group-Ringᵉ Rᵉ)
```

## Properties

### The order of any element divides the order of `1`

Supposeᵉ thatᵉ `k·1ᵉ ＝ᵉ 0`ᵉ forᵉ someᵉ integerᵉ `k`.ᵉ Thenᵉ weᵉ haveᵉ

```text
  k·xᵉ ＝ᵉ k·(1xᵉ) ＝ᵉ (k·1)xᵉ ＝ᵉ 0xᵉ ＝ᵉ 0.ᵉ
```

Thisᵉ showsᵉ thatᵉ ifᵉ theᵉ integerᵉ `k`ᵉ isᵉ in theᵉ orderᵉ ofᵉ `1`,ᵉ thenᵉ itᵉ isᵉ in theᵉ
orderᵉ ofᵉ `x`.ᵉ Thereforeᵉ weᵉ concludeᵉ thatᵉ theᵉ orderᵉ ofᵉ `x`ᵉ alwaysᵉ dividesᵉ theᵉ
orderᵉ ofᵉ `1`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  div-additive-order-element-additive-order-one-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    div-order-element-Groupᵉ (group-Ringᵉ Rᵉ) xᵉ (one-Ringᵉ Rᵉ)
  div-additive-order-element-additive-order-one-Ringᵉ xᵉ kᵉ Hᵉ =
    ( invᵉ (left-zero-law-mul-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
    ( apᵉ (mul-Ring'ᵉ Rᵉ xᵉ) Hᵉ) ∙ᵉ
    ( left-integer-multiple-law-mul-Ringᵉ Rᵉ kᵉ _ _) ∙ᵉ
    ( apᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ) (left-unit-law-mul-Ringᵉ Rᵉ xᵉ))
```

### If there exists an integer `k` such that `k·x ＝ y` then the order of `y` divides the order of `x`

**Proof:**ᵉ Supposeᵉ thatᵉ `k·xᵉ ＝ᵉ y`ᵉ andᵉ `l·xᵉ ＝ᵉ 0`,ᵉ thenᵉ itᵉ followsᵉ thatᵉ

```text
  l·yᵉ ＝ᵉ l·(k·xᵉ) ＝ᵉ k·(l·xᵉ) ＝ᵉ k·0ᵉ ＝ᵉ 0.ᵉ
```

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  div-additive-order-element-is-integer-multiple-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-integer-multiple-of-element-Ringᵉ Rᵉ xᵉ yᵉ →
    div-additive-order-element-Ringᵉ Rᵉ yᵉ xᵉ
  div-additive-order-element-is-integer-multiple-Ringᵉ xᵉ yᵉ Hᵉ lᵉ pᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-additive-order-element-Ringᵉ Rᵉ yᵉ lᵉ)
      ( λ (kᵉ ,ᵉ qᵉ) →
        ( invᵉ (right-zero-law-integer-multiple-Ringᵉ Rᵉ kᵉ)) ∙ᵉ
        ( apᵉ (integer-multiple-Ringᵉ Rᵉ kᵉ) pᵉ) ∙ᵉ
        ( swap-integer-multiple-Ringᵉ Rᵉ kᵉ lᵉ xᵉ ∙ᵉ
        ( apᵉ (integer-multiple-Ringᵉ Rᵉ lᵉ) qᵉ)))
```

### If there exists an integer `k` such that `k·x ＝ 1` then the order of `x` is the order of `1`

Inᵉ otherᵉ words,ᵉ ifᵉ thereᵉ existsᵉ anᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ `k·xᵉ ＝ᵉ 1`,ᵉ thenᵉ theᵉ
additiveᵉ orderᵉ ofᵉ `x`ᵉ isᵉ theᵉ
[characteristic](ring-theory.characteristics-rings.mdᵉ) ofᵉ theᵉ ringᵉ `R`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  has-same-elements-additive-order-element-additive-order-one-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) →
    is-integer-multiple-of-element-Ringᵉ Rᵉ xᵉ (one-Ringᵉ Rᵉ) →
    has-same-elements-Normal-Subgroupᵉ
      ( ℤ-Groupᵉ)
      ( additive-order-element-Ringᵉ Rᵉ xᵉ)
      ( additive-order-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ))
  pr1ᵉ (has-same-elements-additive-order-element-additive-order-one-Ringᵉ xᵉ Hᵉ yᵉ) =
    div-additive-order-element-is-integer-multiple-Ringᵉ Rᵉ xᵉ (one-Ringᵉ Rᵉ) Hᵉ yᵉ
  pr2ᵉ (has-same-elements-additive-order-element-additive-order-one-Ringᵉ xᵉ Hᵉ yᵉ) =
    div-additive-order-element-additive-order-one-Ringᵉ Rᵉ xᵉ yᵉ

  eq-additive-order-element-additive-order-one-Ringᵉ :
    (xᵉ : type-Ringᵉ Rᵉ) → is-integer-multiple-of-element-Ringᵉ Rᵉ xᵉ (one-Ringᵉ Rᵉ) →
    additive-order-element-Ringᵉ Rᵉ xᵉ ＝ᵉ
    additive-order-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ)
  eq-additive-order-element-additive-order-one-Ringᵉ xᵉ Hᵉ =
    eq-has-same-elements-Normal-Subgroupᵉ
      ( ℤ-Groupᵉ)
      ( additive-order-element-Ringᵉ Rᵉ xᵉ)
      ( additive-order-element-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ))
      ( has-same-elements-additive-order-element-additive-order-one-Ringᵉ xᵉ Hᵉ)
```