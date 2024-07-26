# Small universes

```agda
module foundation.small-universesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.small-typesᵉ
```

</details>

## Idea

Aᵉ universeᵉ `UUᵉ l1`ᵉ isᵉ saidᵉ to beᵉ smallᵉ with respectᵉ to `UUᵉ l2`ᵉ ifᵉ `UUᵉ l1`ᵉ isᵉ aᵉ
`UUᵉ l2`-smallᵉ typeᵉ andᵉ eachᵉ `Xᵉ : UUᵉ l1`ᵉ isᵉ aᵉ `UUᵉ l2`-smallᵉ typeᵉ

```agda
is-small-universeᵉ :
  (lᵉ l1ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc lᵉ)
is-small-universeᵉ lᵉ l1ᵉ = is-smallᵉ lᵉ (UUᵉ l1ᵉ) ×ᵉ ((Xᵉ : UUᵉ l1ᵉ) → is-smallᵉ lᵉ Xᵉ)
```