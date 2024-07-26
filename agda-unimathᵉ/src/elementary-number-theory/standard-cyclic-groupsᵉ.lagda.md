# The standard cyclic groups

```agda
module elementary-number-theory.standard-cyclic-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ **standardᵉ cyclicᵉ groups**ᵉ areᵉ theᵉ [groups](group-theory.groups.mdᵉ) ofᵉ
[integers](elementary-number-theory.integers.mdᵉ)
[moduloᵉ `k`](elementary-number-theory.modular-arithmetic.md).ᵉ Theᵉ standardᵉ
cyclicᵉ groupsᵉ areᵉ [abelianᵉ groups](group-theory.abelian-groups.md).ᵉ

Theᵉ factᵉ thatᵉ theᵉ standardᵉ cyclicᵉ groupsᵉ areᵉ
[cyclicᵉ groups](group-theory.cyclic-groups.mdᵉ) isᵉ shownᵉ in
[`elementary-number-theory.standard-cyclic-rings`](elementary-number-theory.standard-cyclic-rings.md).ᵉ

## Definitions

### The semigroup `ℤ/k`

```agda
ℤ-Mod-Semigroupᵉ : (kᵉ : ℕᵉ) → Semigroupᵉ lzero
pr1ᵉ (ℤ-Mod-Semigroupᵉ kᵉ) = ℤ-Mod-Setᵉ kᵉ
pr1ᵉ (pr2ᵉ (ℤ-Mod-Semigroupᵉ kᵉ)) = add-ℤ-Modᵉ kᵉ
pr2ᵉ (pr2ᵉ (ℤ-Mod-Semigroupᵉ kᵉ)) = associative-add-ℤ-Modᵉ kᵉ
```

### The group `ℤ/k`

```agda
ℤ-Mod-Groupᵉ : (kᵉ : ℕᵉ) → Groupᵉ lzero
pr1ᵉ (ℤ-Mod-Groupᵉ kᵉ) = ℤ-Mod-Semigroupᵉ kᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ))) = zero-ℤ-Modᵉ kᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ)))) = left-unit-law-add-ℤ-Modᵉ kᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ)))) = right-unit-law-add-ℤ-Modᵉ kᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ))) = neg-ℤ-Modᵉ kᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ)))) = left-inverse-law-add-ℤ-Modᵉ kᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (ℤ-Mod-Groupᵉ kᵉ)))) = right-inverse-law-add-ℤ-Modᵉ kᵉ
```

### The abelian group `ℤ/k`

```agda
ℤ-Mod-Abᵉ : (kᵉ : ℕᵉ) → Abᵉ lzero
pr1ᵉ (ℤ-Mod-Abᵉ kᵉ) = ℤ-Mod-Groupᵉ kᵉ
pr2ᵉ (ℤ-Mod-Abᵉ kᵉ) = commutative-add-ℤ-Modᵉ kᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}