# Exponents of abelian groups

```agda
module group-theory.exponents-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ

open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.exponents-groupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ
```

</details>

Theᵉ **exponent**ᵉ `expᵉ A`ᵉ ofᵉ anᵉ [abelianᵉ group](group-theory.abelian-groups.mdᵉ)
`A`ᵉ isᵉ theᵉ intersectionᵉ ofᵉ theᵉ kernelsᵉ ofᵉ theᵉ
[groupᵉ homomorphisms](group-theory.homomorphisms-groups.mdᵉ)

```text
  hom-element-Groupᵉ (group-Abᵉ Aᵉ) aᵉ : ℤᵉ → Aᵉ
```

indexedᵉ byᵉ allᵉ elementsᵉ `aᵉ : A`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ exponentᵉ ofᵉ `A`ᵉ isᵉ theᵉ
[subgroup](group-theory.subgroups.mdᵉ) `K`ᵉ ofᵉ `ℤ`ᵉ consistingᵉ ofᵉ allᵉ
[integers](elementary-number-theory.integers.mdᵉ) `k`ᵉ suchᵉ thatᵉ theᵉ
[integerᵉ multiple](group-theory.integer-multiples-of-elements-abelian-groups.mdᵉ)
`kxᵉ ＝ᵉ 1`ᵉ forᵉ everyᵉ groupᵉ elementᵉ `x`.ᵉ

Noteᵉ thatᵉ ourᵉ conventionsᵉ areᵉ slightlyᵉ differentᵉ fromᵉ theᵉ conventionsᵉ in
classicalᵉ mathematics,ᵉ where theᵉ exponentᵉ isᵉ takenᵉ to beᵉ theᵉ positiveᵉ integerᵉ
`k`ᵉ thatᵉ
[generatesᵉ theᵉ subgroup](group-theory.subgroups-generated-by-elements-groups.mdᵉ)
ofᵉ `ℤ`ᵉ thatᵉ weᵉ callᵉ theᵉ exponentᵉ ofᵉ `A`.ᵉ Inᵉ constructiveᵉ mathematics,ᵉ however,ᵉ
suchᵉ anᵉ integerᵉ isᵉ notᵉ alwaysᵉ well-defined.ᵉ

## Definitions

### The exponent of an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  exponent-Abᵉ : Subgroup-Abᵉ lᵉ ℤ-Abᵉ
  exponent-Abᵉ = exponent-Groupᵉ (group-Abᵉ Aᵉ)
```