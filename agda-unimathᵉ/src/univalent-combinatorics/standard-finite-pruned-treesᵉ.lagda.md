# Standard finite pruned trees

```agda
module univalent-combinatorics.standard-finite-pruned-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ standardᵉ finiteᵉ prunedᵉ treeᵉ ofᵉ heightᵉ `n`ᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ aᵉ standardᵉ
finiteᵉ treeᵉ in whichᵉ eachᵉ pathᵉ fromᵉ theᵉ rootᵉ to aᵉ leafᵉ hasᵉ lengthᵉ `nᵉ +ᵉ 1`.ᵉ

## Definition

```agda
data Pruned-Tree-Finᵉ : ℕᵉ → UUᵉ lzero where
  root-Pruned-Tree-Finᵉ : Pruned-Tree-Finᵉ zero-ℕᵉ
  tree-Pruned-Tree-Finᵉ :
    (nᵉ kᵉ : ℕᵉ) → (Finᵉ kᵉ → Pruned-Tree-Finᵉ nᵉ) → Pruned-Tree-Finᵉ (succ-ℕᵉ nᵉ)

width-Pruned-Tree-Finᵉ : (nᵉ : ℕᵉ) → Pruned-Tree-Finᵉ (succ-ℕᵉ nᵉ) → ℕᵉ
width-Pruned-Tree-Finᵉ nᵉ (tree-Pruned-Tree-Finᵉ .nᵉ kᵉ xᵉ) = kᵉ
```