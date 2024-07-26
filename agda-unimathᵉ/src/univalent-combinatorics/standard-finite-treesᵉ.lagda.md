# Standard finite trees

```agda
module univalent-combinatorics.standard-finite-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.maximum-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.sums-of-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ standardᵉ finiteᵉ treeᵉ isᵉ aᵉ finiteᵉ treeᵉ thatᵉ branchesᵉ byᵉ standardᵉ finiteᵉ sets.ᵉ
Inᵉ contextsᵉ where oneᵉ wouldn'tᵉ beᵉ interestedᵉ in consideringᵉ finiteᵉ treesᵉ to beᵉ
theᵉ sameᵉ ifᵉ theyᵉ differᵉ upᵉ to aᵉ permutationᵉ ofᵉ trees,ᵉ peopleᵉ simplyᵉ callᵉ ourᵉ
standardᵉ finiteᵉ treesᵉ finiteᵉ trees.ᵉ Fromᵉ aᵉ univalentᵉ perspective,ᵉ however,ᵉ aᵉ
finiteᵉ treeᵉ isᵉ aᵉ treeᵉ builtᵉ outᵉ ofᵉ finiteᵉ types,ᵉ notᵉ justᵉ theᵉ standardᵉ finiteᵉ
types.ᵉ Sometimes,ᵉ standardᵉ finiteᵉ treesᵉ areᵉ calledᵉ planarᵉ finiteᵉ trees,ᵉ to
emphasizeᵉ thatᵉ theᵉ branchingᵉ typesᵉ `Finᵉ n`ᵉ record theᵉ orderᵉ in whichᵉ theᵉ
branchesᵉ occur.ᵉ

## Definition

```agda
data Tree-Finᵉ : UUᵉ lzero where
  tree-Finᵉ : (nᵉ : ℕᵉ) → (Finᵉ nᵉ → Tree-Finᵉ) → Tree-Finᵉ

root-Tree-Finᵉ : Tree-Finᵉ
root-Tree-Finᵉ = tree-Finᵉ zero-ℕᵉ ex-falsoᵉ

number-nodes-Tree-Finᵉ : Tree-Finᵉ → ℕᵉ
number-nodes-Tree-Finᵉ (tree-Finᵉ zero-ℕᵉ _) = zero-ℕᵉ
number-nodes-Tree-Finᵉ (tree-Finᵉ (succ-ℕᵉ nᵉ) fᵉ) =
  succ-ℕᵉ (sum-Fin-ℕᵉ (succ-ℕᵉ nᵉ) (λ kᵉ → number-nodes-Tree-Finᵉ (fᵉ kᵉ)))

height-Tree-Finᵉ : Tree-Finᵉ → ℕᵉ
height-Tree-Finᵉ (tree-Finᵉ zero-ℕᵉ fᵉ) = zero-ℕᵉ
height-Tree-Finᵉ (tree-Finᵉ (succ-ℕᵉ nᵉ) fᵉ) =
  succ-ℕᵉ (max-Fin-ℕᵉ (succ-ℕᵉ nᵉ) (λ kᵉ → height-Tree-Finᵉ (fᵉ kᵉ)))

is-leaf-Tree-Finᵉ : Tree-Finᵉ → UUᵉ lzero
is-leaf-Tree-Finᵉ (tree-Finᵉ zero-ℕᵉ _) = unitᵉ
is-leaf-Tree-Finᵉ (tree-Finᵉ (succ-ℕᵉ nᵉ) _) = emptyᵉ

is-full-binary-Tree-Finᵉ : Tree-Finᵉ → UUᵉ lzero
is-full-binary-Tree-Finᵉ (tree-Finᵉ zero-ℕᵉ fᵉ) = unitᵉ
is-full-binary-Tree-Finᵉ (tree-Finᵉ (succ-ℕᵉ nᵉ) fᵉ) =
  (Idᵉ 2 nᵉ) ×ᵉ ((kᵉ : Finᵉ (succ-ℕᵉ nᵉ)) → is-full-binary-Tree-Finᵉ (fᵉ kᵉ))
```