# Elements of finite order

```agda
module group-theory.elements-of-finite-order-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ

open import foundation.existential-quantificationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.orders-of-elements-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subgroups-generated-by-elements-groupsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ ofᵉ
**finiteᵉ order**ᵉ ifᵉ theᵉ [subgroup](group-theory.subgroups.mdᵉ) `orderᵉ x`ᵉ ofᵉ
[`ℤ`](elementary-number-theory.group-of-integers.mdᵉ) isᵉ
[generatedᵉ by](group-theory.subgroups-generated-by-elements-groups.mdᵉ) aᵉ
[nonzeroᵉ integer](elementary-number-theory.nonzero-integers.md).ᵉ

Noteᵉ thatᵉ theᵉ conditionᵉ ofᵉ beingᵉ ofᵉ finiteᵉ orderᵉ isᵉ slightlyᵉ strongerᵉ thanᵉ theᵉ
conditionᵉ ofᵉ beingᵉ aᵉ [torsionᵉ element](group-theory.torsion-elements-groups.md).ᵉ
Theᵉ latterᵉ conditionᵉ merelyᵉ assertsᵉ thatᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ nonzeroᵉ integerᵉ in theᵉ
subgroupᵉ `orderᵉ x`ᵉ ofᵉ `ℤ`.ᵉ

## Definitions

### The predicate of being an element of finite order

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (xᵉ : type-Groupᵉ Gᵉ)
  where

  has-finite-order-element-prop-Groupᵉ : Propᵉ l1ᵉ
  has-finite-order-element-prop-Groupᵉ =
    ∃ᵉ ( nonzero-ℤᵉ)
      ( λ kᵉ →
        has-same-elements-prop-Subgroupᵉ ℤ-Groupᵉ
          ( subgroup-element-Groupᵉ ℤ-Groupᵉ (int-nonzero-ℤᵉ kᵉ))
          ( subgroup-order-element-Groupᵉ Gᵉ xᵉ))
```

## See also

-ᵉ [Torsionᵉ elements](group-theory.torsion-elements-groups.mdᵉ) ofᵉ groups.ᵉ