# Torsion elements of groups

```agda
module group-theory.torsion-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.nonzero-integersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ aᵉ
**torsionᵉ element**ᵉ ifᵉ

```text
  ∃ᵉ (kᵉ : nonzero-ℤ),ᵉ xᵏᵉ ＝ᵉ 1.ᵉ
```

Noteᵉ thatᵉ theᵉ conditionᵉ ofᵉ beingᵉ aᵉ torsionᵉ elementᵉ isᵉ slightlyᵉ weakerᵉ thanᵉ theᵉ
conditionᵉ ofᵉ beingᵉ ofᵉ
[finiteᵉ order](group-theory.elements-of-finite-order-groups.md).ᵉ Theᵉ conditionᵉ
ofᵉ beingᵉ aᵉ torsionᵉ elementᵉ holdsᵉ
[ifᵉ andᵉ onlyᵉ if](foundation.logical-equivalences.mdᵉ) theᵉ
[subgroup](group-theory.subgroups.mdᵉ) `orderᵉ x`ᵉ ofᵉ `ℤ`ᵉ containsᵉ aᵉ
[nonzero](elementary-number-theory.nonzero-integers.mdᵉ)
[integer](elementary-number-theory.integers.md),ᵉ whileᵉ theᵉ conditionᵉ ofᵉ beingᵉ ofᵉ
finiteᵉ [order](group-theory.orders-of-elements-groups.mdᵉ) statesᵉ thatᵉ theᵉ
subgroupᵉ `orderᵉ x`ᵉ isᵉ generatedᵉ byᵉ `k`ᵉ forᵉ someᵉ nonzeroᵉ integerᵉ `k`.ᵉ

## Definition

### The predicate of being a torsion element

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (xᵉ : type-Groupᵉ Gᵉ)
  where

  is-torsion-element-prop-Groupᵉ : Propᵉ l1ᵉ
  is-torsion-element-prop-Groupᵉ =
    exists-structure-Propᵉ
      ( nonzero-ℤᵉ)
      ( λ kᵉ → integer-power-Groupᵉ Gᵉ (int-nonzero-ℤᵉ kᵉ) xᵉ ＝ᵉ unit-Groupᵉ Gᵉ)

  is-torsion-element-Groupᵉ : UUᵉ l1ᵉ
  is-torsion-element-Groupᵉ = type-Propᵉ is-torsion-element-prop-Groupᵉ

  is-prop-is-torsion-element-Groupᵉ : is-propᵉ is-torsion-element-Groupᵉ
  is-prop-is-torsion-element-Groupᵉ =
    is-prop-type-Propᵉ is-torsion-element-prop-Groupᵉ
```

### The type of torsion elements of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  torsion-element-Groupᵉ : UUᵉ l1ᵉ
  torsion-element-Groupᵉ = type-subtypeᵉ (is-torsion-element-prop-Groupᵉ Gᵉ)
```

## Properties

### The unit element is a torsion element

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-torsion-element-unit-Groupᵉ : is-torsion-element-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ)
  is-torsion-element-unit-Groupᵉ =
    intro-existsᵉ
      ( one-nonzero-ℤᵉ)
      ( integer-power-unit-Groupᵉ Gᵉ one-ℤᵉ)

  unit-torsion-element-Groupᵉ : torsion-element-Groupᵉ Gᵉ
  pr1ᵉ unit-torsion-element-Groupᵉ = unit-Groupᵉ Gᵉ
  pr2ᵉ unit-torsion-element-Groupᵉ = is-torsion-element-unit-Groupᵉ
```

## See also

-ᵉ [Torsion-freeᵉ groups](group-theory.torsion-free-groups.mdᵉ) areᵉ definedᵉ to beᵉ
  groupsᵉ ofᵉ whichᵉ theᵉ onlyᵉ torsionᵉ elementᵉ isᵉ theᵉ identityᵉ element.ᵉ
-ᵉ Elementsᵉ ofᵉ [finiteᵉ order](group-theory.elements-of-finite-order-groups.mdᵉ) ofᵉ
  groups.ᵉ