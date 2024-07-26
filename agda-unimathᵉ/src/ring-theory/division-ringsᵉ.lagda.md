# Division rings

```agda
module ring-theory.division-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.trivial-ringsᵉ
```

</details>

## Idea

Divisionᵉ ringsᵉ areᵉ nontrivialᵉ ringsᵉ in whichᵉ allᵉ nonzeroᵉ elementsᵉ areᵉ
invertible.ᵉ

## Definition

```agda
is-division-Ringᵉ :
  { lᵉ : Level} → Ringᵉ lᵉ → UUᵉ lᵉ
is-division-Ringᵉ Rᵉ =
  (is-nontrivial-Ringᵉ Rᵉ) ×ᵉ
  ((xᵉ : type-Ringᵉ Rᵉ) → zero-Ringᵉ Rᵉ ≠ᵉ xᵉ → is-invertible-element-Ringᵉ Rᵉ xᵉ)
```