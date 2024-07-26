# Initial objects of large precategories

```agda
module category-theory.initial-objects-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **initialᵉ object**ᵉ in aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
`C`ᵉ isᵉ anᵉ objectᵉ `X`ᵉ suchᵉ thatᵉ `homᵉ Xᵉ Y`ᵉ isᵉ
[contractible](foundation.contractible-types.mdᵉ) forᵉ anyᵉ objectᵉ `Y`.ᵉ

## Definitions

### Initial objects in large categories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ)
  where

  is-initial-obj-Large-Precategoryᵉ : UUωᵉ
  is-initial-obj-Large-Precategoryᵉ =
    {l2ᵉ : Level} (Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ) →
    is-contrᵉ (hom-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ)
```