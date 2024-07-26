# Initial rings

```agda
module ring-theory.initial-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.initial-objects-large-categoriesᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.category-of-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **initialᵉ ring**ᵉ isᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ thatᵉ satisfiesᵉ theᵉ
universalᵉ propertyᵉ thatᵉ forᵉ anyᵉ ringᵉ `S`,ᵉ theᵉ typeᵉ

```text
  hom-Ringᵉ Rᵉ Sᵉ
```

ofᵉ [ringᵉ homomorphisms](ring-theory.homomorphisms-rings.mdᵉ) fromᵉ `R`ᵉ to `S`ᵉ isᵉ
contractible.ᵉ

Inᵉ
[`elementary-number-theory.ring-of-integers`](elementary-number-theory.ring-of-integers.mdᵉ)
weᵉ willᵉ showᵉ thatᵉ `ℤ`ᵉ isᵉ theᵉ initialᵉ ring.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-initial-Ringᵉ : UUωᵉ
  is-initial-Ringᵉ = is-initial-obj-Large-Categoryᵉ Ring-Large-Categoryᵉ Rᵉ
```