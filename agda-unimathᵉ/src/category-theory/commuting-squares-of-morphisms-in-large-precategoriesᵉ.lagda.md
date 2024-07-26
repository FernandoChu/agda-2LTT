# Commuting squares of morphisms in large precategories

```agda
module category-theory.commuting-squares-of-morphisms-in-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.identity-typesᵉ
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

in aᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`ᵉ isᵉ saidᵉ to
**commute**ᵉ ifᵉ thereᵉ isᵉ anᵉ [identification](foundation-core.identity-types.mdᵉ)
betweenᵉ bothᵉ composites.ᵉ

## Definitions

```agda
coherence-square-hom-Large-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {αᵉ : Level → Level}
  {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ}
  {yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  {zᵉ : obj-Large-Precategoryᵉ Cᵉ l3ᵉ}
  {wᵉ : obj-Large-Precategoryᵉ Cᵉ l4ᵉ}
  (topᵉ : hom-Large-Precategoryᵉ Cᵉ xᵉ yᵉ)
  (leftᵉ : hom-Large-Precategoryᵉ Cᵉ xᵉ zᵉ)
  (rightᵉ : hom-Large-Precategoryᵉ Cᵉ yᵉ wᵉ)
  (bottomᵉ : hom-Large-Precategoryᵉ Cᵉ zᵉ wᵉ) →
  UUᵉ (βᵉ l1ᵉ l4ᵉ)
coherence-square-hom-Large-Precategoryᵉ Cᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
  ( comp-hom-Large-Precategoryᵉ Cᵉ bottomᵉ leftᵉ) ＝ᵉ
  ( comp-hom-Large-Precategoryᵉ Cᵉ rightᵉ topᵉ)
```