# Lower types of elements in W-types

```agda
module trees.lower-types-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantificationᵉ
open import foundation.universe-levelsᵉ

open import trees.ranks-of-elements-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ byᵉ inductionᵉ aᵉ typeᵉ familyᵉ overᵉ `Wᵉ Aᵉ B`ᵉ in aᵉ wayᵉ thatᵉ generalizesᵉ theᵉ
constructionᵉ ofᵉ theᵉ standardᵉ finiteᵉ typesᵉ overᵉ ℕᵉ to arbitraryᵉ W-types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  data
    lower-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    lower-tree-𝕎ᵉ :
      {xᵉ : Aᵉ} {fᵉ : Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ} →
      ((yᵉ : Bᵉ xᵉ) → lower-𝕎ᵉ (fᵉ yᵉ)) → lower-𝕎ᵉ (tree-𝕎ᵉ xᵉ fᵉ)

  inclusion-lower-𝕎ᵉ : {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} → lower-𝕎ᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ
  inclusion-lower-𝕎ᵉ (lower-tree-𝕎ᵉ {aᵉ} {fᵉ} gᵉ) =
    tree-𝕎ᵉ aᵉ (λ yᵉ → inclusion-lower-𝕎ᵉ (gᵉ yᵉ))

  upper-bound-rank-inclusion-lower-𝕎ᵉ :
    {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} (yᵉ : lower-𝕎ᵉ xᵉ) → inclusion-lower-𝕎ᵉ yᵉ ≼-𝕎ᵉ xᵉ
  upper-bound-rank-inclusion-lower-𝕎ᵉ (lower-tree-𝕎ᵉ gᵉ) yᵉ =
    intro-existsᵉ yᵉ (upper-bound-rank-inclusion-lower-𝕎ᵉ (gᵉ yᵉ))
```