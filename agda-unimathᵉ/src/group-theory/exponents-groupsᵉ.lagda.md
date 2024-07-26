# Exponents of groups

```agda
module group-theory.exponents-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ

open import foundation.universe-levelsᵉ

open import group-theory.free-groups-with-one-generatorᵉ
open import group-theory.groupsᵉ
open import group-theory.intersections-subgroups-groupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

Theᵉ **exponent**ᵉ `expᵉ G`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ theᵉ
intersectionᵉ ofᵉ theᵉ kernelsᵉ ofᵉ theᵉ
[groupᵉ homomorphisms](group-theory.homomorphisms-groups.mdᵉ)

```text
  hom-element-Groupᵉ Gᵉ gᵉ : ℤᵉ → Gᵉ
```

indexedᵉ byᵉ allᵉ elementsᵉ `gᵉ : G`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ exponentᵉ ofᵉ `G`ᵉ isᵉ theᵉ
[subgroup](group-theory.subgroups.mdᵉ) `K`ᵉ ofᵉ `ℤ`ᵉ consistingᵉ ofᵉ allᵉ
[integers](elementary-number-theory.integers.mdᵉ) `k`ᵉ suchᵉ thatᵉ theᵉ
[integerᵉ power](group-theory.integer-powers-of-elements-groups.mdᵉ) `gᵏᵉ ＝ᵉ 1`ᵉ forᵉ
everyᵉ groupᵉ elementᵉ `g`.ᵉ

Noteᵉ thatᵉ ourᵉ conventionsᵉ areᵉ slightlyᵉ differentᵉ fromᵉ theᵉ conventionsᵉ in
classicalᵉ mathematics,ᵉ where theᵉ exponentᵉ isᵉ takenᵉ to beᵉ theᵉ positiveᵉ integerᵉ
`k`ᵉ thatᵉ
[generatesᵉ theᵉ subgroup](group-theory.subgroups-generated-by-elements-groups.mdᵉ)
ofᵉ `ℤ`ᵉ thatᵉ weᵉ callᵉ theᵉ exponentᵉ ofᵉ `G`.ᵉ Inᵉ constructiveᵉ mathematics,ᵉ however,ᵉ
suchᵉ anᵉ integerᵉ isᵉ notᵉ alwaysᵉ well-defined.ᵉ

## Definitions

### The exponent of a group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  exponent-Groupᵉ : Subgroupᵉ lᵉ ℤ-Groupᵉ
  exponent-Groupᵉ =
    intersection-family-of-subgroups-Groupᵉ ℤ-Groupᵉ
      ( λ (gᵉ : type-Groupᵉ Gᵉ) →
        subgroup-kernel-hom-Groupᵉ ℤ-Groupᵉ Gᵉ (hom-element-Groupᵉ Gᵉ gᵉ))
```