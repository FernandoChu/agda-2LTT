# The coalgebra of directed trees

```agda
module trees.coalgebra-of-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.bases-directed-treesᵉ
open import trees.coalgebras-polynomial-endofunctorsᵉ
open import trees.directed-treesᵉ
open import trees.fibers-directed-treesᵉ
```

</details>

## Idea

Usingᵉ theᵉ fibersᵉ ofᵉ baseᵉ elements,ᵉ theᵉ typeᵉ ofᵉ directedᵉ trees,ᵉ ofᵉ whichᵉ theᵉ typeᵉ
ofᵉ nodesᵉ andᵉ theᵉ typesᵉ ofᵉ edgesᵉ areᵉ ofᵉ theᵉ sameᵉ universeᵉ level,ᵉ hasᵉ theᵉ
structureᵉ ofᵉ aᵉ coalgebraᵉ forᵉ theᵉ polynomialᵉ endofunctorᵉ

```text
  Aᵉ ↦ᵉ Σᵉ (Xᵉ : UU),ᵉ Xᵉ → Aᵉ
```

## Definition

```agda
coalgebra-Directed-Treeᵉ :
  (lᵉ : Level) → coalgebra-polynomial-endofunctorᵉ (lsuc lᵉ) (UUᵉ lᵉ) (λ Xᵉ → Xᵉ)
pr1ᵉ (coalgebra-Directed-Treeᵉ lᵉ) = Directed-Treeᵉ lᵉ lᵉ
pr1ᵉ (pr2ᵉ (coalgebra-Directed-Treeᵉ lᵉ) Tᵉ) = base-Directed-Treeᵉ Tᵉ
pr2ᵉ (pr2ᵉ (coalgebra-Directed-Treeᵉ lᵉ) Tᵉ) = fiber-base-Directed-Treeᵉ Tᵉ
```