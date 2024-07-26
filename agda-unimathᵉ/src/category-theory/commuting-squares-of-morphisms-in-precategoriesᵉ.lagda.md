# Commuting squares of morphisms in precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-set-magmoidsᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ morphismsᵉ

```text
  xᵉ ------>ᵉ yᵉ
  |         |
  |         |
  ∨ᵉ         ∨ᵉ
  zᵉ ------>ᵉ wᵉ
```

in aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ isᵉ saidᵉ to **commute**ᵉ
ifᵉ thereᵉ isᵉ anᵉ [identification](foundation-core.identity-types.mdᵉ) betweenᵉ bothᵉ
compositesᵉ:

```text
  bottomᵉ ∘ᵉ leftᵉ ＝ᵉ rightᵉ ∘ᵉ top.ᵉ
```

## Definitions

```agda
coherence-square-hom-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ zᵉ wᵉ : obj-Precategoryᵉ Cᵉ}
  (topᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (leftᵉ : hom-Precategoryᵉ Cᵉ xᵉ zᵉ)
  (rightᵉ : hom-Precategoryᵉ Cᵉ yᵉ wᵉ)
  (bottomᵉ : hom-Precategoryᵉ Cᵉ zᵉ wᵉ) →
  UUᵉ l2ᵉ
coherence-square-hom-Precategoryᵉ Cᵉ =
  coherence-square-hom-Set-Magmoidᵉ (set-magmoid-Precategoryᵉ Cᵉ)
```