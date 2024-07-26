# Commuting squares of morphisms in set-magmoids

```agda
module category-theory.commuting-squares-of-morphisms-in-set-magmoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.set-magmoidsᵉ

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

in aᵉ [set-magmoid](category-theory.set-magmoids.mdᵉ) `C`ᵉ isᵉ saidᵉ to **commute**ᵉ
ifᵉ thereᵉ isᵉ anᵉ [identification](foundation-core.identity-types.mdᵉ) betweenᵉ bothᵉ
compositesᵉ:

```text
  bottomᵉ ∘ᵉ leftᵉ ＝ᵉ rightᵉ ∘ᵉ top.ᵉ
```

## Definitions

```agda
coherence-square-hom-Set-Magmoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  {xᵉ yᵉ zᵉ wᵉ : obj-Set-Magmoidᵉ Cᵉ}
  (topᵉ : hom-Set-Magmoidᵉ Cᵉ xᵉ yᵉ)
  (leftᵉ : hom-Set-Magmoidᵉ Cᵉ xᵉ zᵉ)
  (rightᵉ : hom-Set-Magmoidᵉ Cᵉ yᵉ wᵉ)
  (bottomᵉ : hom-Set-Magmoidᵉ Cᵉ zᵉ wᵉ) →
  UUᵉ l2ᵉ
coherence-square-hom-Set-Magmoidᵉ Cᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
  ( comp-hom-Set-Magmoidᵉ Cᵉ bottomᵉ leftᵉ) ＝ᵉ
  ( comp-hom-Set-Magmoidᵉ Cᵉ rightᵉ topᵉ)
```