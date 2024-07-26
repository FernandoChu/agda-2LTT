# The dihedral groups

```agda
module group-theory.dihedral-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.standard-cyclic-groupsᵉ

open import foundation.universe-levelsᵉ

open import group-theory.dihedral-group-constructionᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Theᵉ dihedralᵉ groupᵉ `D_k`ᵉ isᵉ definedᵉ byᵉ theᵉ dihedralᵉ groupᵉ constructionᵉ appliedᵉ
to theᵉ cyclicᵉ groupᵉ `ℤ-Modᵉ k`.ᵉ

## Definition

```agda
dihedral-groupᵉ : ℕᵉ → Groupᵉ lzero
dihedral-groupᵉ kᵉ = dihedral-group-Abᵉ (ℤ-Mod-Abᵉ kᵉ)
```