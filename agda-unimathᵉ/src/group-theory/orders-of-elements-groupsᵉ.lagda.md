# The order of an element in a group

```agda
module group-theory.orders-of-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.universe-levelsᵉ

open import group-theory.free-groups-with-one-generatorᵉ
open import group-theory.groupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Forᵉ eachᵉ elementᵉ `gᵉ : G`ᵉ ofᵉ aᵉ groupᵉ `G`ᵉ weᵉ haveᵉ aᵉ uniqueᵉ groupᵉ homomorphismᵉ
`fᵉ : ℤᵉ → G`ᵉ suchᵉ thatᵉ `fᵉ 1 = g`.ᵉ Theᵉ orderᵉ ofᵉ `g`ᵉ isᵉ definedᵉ to beᵉ theᵉ kernelᵉ ofᵉ
thisᵉ groupᵉ homomorphismᵉ `f`.ᵉ Sinceᵉ kernelsᵉ areᵉ orderedᵉ byᵉ inclusion,ᵉ itᵉ followsᵉ
thatᵉ theᵉ ordersᵉ ofᵉ elementsᵉ ofᵉ aᵉ groupᵉ areᵉ orderedᵉ byᵉ reversedᵉ inclusion.ᵉ

Ifᵉ theᵉ groupᵉ `G`ᵉ hasᵉ decidableᵉ equality,ᵉ thenᵉ weᵉ canᵉ reduceᵉ theᵉ orderᵉ ofᵉ `g`ᵉ to
aᵉ naturalᵉ number.ᵉ Inᵉ thisᵉ case,ᵉ theᵉ ordersᵉ ofᵉ elementsᵉ ofᵉ `G`ᵉ areᵉ orderedᵉ byᵉ
divisibility.ᵉ

Ifᵉ theᵉ uniqueᵉ groupᵉ homomorphismᵉ `fᵉ : ℤᵉ → G`ᵉ suchᵉ thatᵉ `fᵉ 1 = g`ᵉ isᵉ injective,ᵉ
andᵉ `G`ᵉ hasᵉ decidableᵉ equality,ᵉ thenᵉ theᵉ orderᵉ ofᵉ `g`ᵉ isᵉ setᵉ to beᵉ `0`,ᵉ whichᵉ isᵉ
aᵉ consequenceᵉ ofᵉ theᵉ pointᵉ ofᵉ viewᵉ thatᵉ ordersᵉ areᵉ normalᵉ subgroupsᵉ ofᵉ `ℤ`.ᵉ

## Definitions

### The order of an element in a group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) (gᵉ : type-Groupᵉ Gᵉ)
  where

  order-element-Groupᵉ : Normal-Subgroupᵉ lᵉ ℤ-Groupᵉ
  order-element-Groupᵉ =
    kernel-hom-Groupᵉ ℤ-Groupᵉ Gᵉ (hom-element-Groupᵉ Gᵉ gᵉ)

  subgroup-order-element-Groupᵉ : Subgroupᵉ lᵉ ℤ-Groupᵉ
  subgroup-order-element-Groupᵉ =
    subgroup-kernel-hom-Groupᵉ ℤ-Groupᵉ Gᵉ (hom-element-Groupᵉ Gᵉ gᵉ)

  subset-order-element-Groupᵉ : subset-Groupᵉ lᵉ ℤ-Groupᵉ
  subset-order-element-Groupᵉ =
    subset-kernel-hom-Groupᵉ ℤ-Groupᵉ Gᵉ (hom-element-Groupᵉ Gᵉ gᵉ)

  is-in-order-element-Groupᵉ : ℤᵉ → UUᵉ lᵉ
  is-in-order-element-Groupᵉ =
    is-in-kernel-hom-Groupᵉ ℤ-Groupᵉ Gᵉ (hom-element-Groupᵉ Gᵉ gᵉ)
```

### Divisibility of orders of elements of a group

Weᵉ sayᵉ thatᵉ theᵉ orderᵉ ofᵉ `x`ᵉ dividesᵉ theᵉ orderᵉ ofᵉ `y`ᵉ ifᵉ theᵉ normalᵉ subgroupᵉ
`order-element-Groupᵉ Gᵉ y`ᵉ isᵉ containedᵉ in theᵉ normalᵉ subgroupᵉ
`order-elemetn-Groupᵉ Gᵉ x`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ orderᵉ ofᵉ `x`ᵉ dividesᵉ theᵉ orderᵉ ofᵉ
`y`ᵉ ifᵉ forᵉ everyᵉ integerᵉ `k`ᵉ suchᵉ thatᵉ `yᵏᵉ ＝ᵉ e`ᵉ weᵉ haveᵉ `xᵏᵉ ＝ᵉ e`.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  div-order-element-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ lᵉ
  div-order-element-Groupᵉ xᵉ yᵉ =
    leq-Normal-Subgroupᵉ
      ( ℤ-Groupᵉ)
      ( order-element-Groupᵉ Gᵉ yᵉ)
      ( order-element-Groupᵉ Gᵉ xᵉ)
```