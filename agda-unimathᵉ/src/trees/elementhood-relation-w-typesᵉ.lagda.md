# The elementhood relation on W-types

```agda
module trees.elementhood-relation-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-coalgebras-polynomial-endofunctorsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ treeᵉ `S`ᵉ isᵉ anᵉ **element**ᵉ ofᵉ aᵉ treeᵉ `tree-𝕎ᵉ xᵉ α`ᵉ ifᵉ `S`ᵉ canᵉ beᵉ
equippedᵉ with anᵉ elementᵉ `yᵉ : Bᵉ x`ᵉ suchᵉ thatᵉ `αᵉ yᵉ = S`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  infix 6 _∈-𝕎ᵉ_ _∉-𝕎ᵉ_

  _∈-𝕎ᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ∈-𝕎ᵉ yᵉ = xᵉ ∈ᵉ yᵉ in-coalgebraᵉ 𝕎-Coalgᵉ Aᵉ Bᵉ

  _∉-𝕎ᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ∉-𝕎ᵉ yᵉ = is-emptyᵉ (xᵉ ∈-𝕎ᵉ yᵉ)
```

## Properties

```agda
irreflexive-∈-𝕎ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → xᵉ ∉-𝕎ᵉ xᵉ
irreflexive-∈-𝕎ᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} (tree-𝕎ᵉ xᵉ αᵉ) (pairᵉ yᵉ pᵉ) =
  irreflexive-∈-𝕎ᵉ (αᵉ yᵉ) (trᵉ (λ zᵉ → (αᵉ yᵉ) ∈-𝕎ᵉ zᵉ) (invᵉ pᵉ) (pairᵉ yᵉ reflᵉ))
```