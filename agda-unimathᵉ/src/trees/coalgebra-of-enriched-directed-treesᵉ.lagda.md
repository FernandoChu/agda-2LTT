# The coalgebra of enriched directed trees

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module trees.coalgebra-of-enriched-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.coalgebras-polynomial-endofunctorsᵉ
open import trees.enriched-directed-treesᵉ
open import trees.fibers-enriched-directed-treesᵉ
open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Usingᵉ theᵉ fibersᵉ ofᵉ baseᵉ elements,ᵉ theᵉ typeᵉ ofᵉ enrichedᵉ directedᵉ treesᵉ hasᵉ theᵉ
structureᵉ ofᵉ aᵉ coalgebraᵉ forᵉ theᵉ polynomialᵉ endofunctorᵉ

```text
  Xᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ Bᵉ aᵉ → X.ᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  structure-coalgebra-Enriched-Directed-Treeᵉ :
    Enriched-Directed-Treeᵉ l3ᵉ l3ᵉ Aᵉ Bᵉ →
    type-polynomial-endofunctorᵉ Aᵉ Bᵉ (Enriched-Directed-Treeᵉ l3ᵉ l3ᵉ Aᵉ Bᵉ)
  pr1ᵉ (structure-coalgebra-Enriched-Directed-Treeᵉ Tᵉ) =
    shape-root-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ
  pr2ᵉ (structure-coalgebra-Enriched-Directed-Treeᵉ Tᵉ) =
    fiber-base-Enriched-Directed-Treeᵉ Aᵉ Bᵉ Tᵉ

  coalgebra-Enriched-Directed-Treeᵉ :
    coalgebra-polynomial-endofunctorᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ) Aᵉ Bᵉ
  pr1ᵉ coalgebra-Enriched-Directed-Treeᵉ = Enriched-Directed-Treeᵉ l3ᵉ l3ᵉ Aᵉ Bᵉ
  pr2ᵉ coalgebra-Enriched-Directed-Treeᵉ =
    structure-coalgebra-Enriched-Directed-Treeᵉ
```