# The infinite complex projective space

```agda
module synthetic-homotopy-theory.infinite-complex-projective-spaceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.set-truncationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.circleᵉ
```

</details>

## Definitions

### `ℂP∞` as the `1`-connected component of the universe at the circle

```agda
ℂP∞ᵉ : UUᵉ (lsuc lzero)
ℂP∞ᵉ = Σᵉ (UUᵉ lzero) (λ Xᵉ → type-trunc-Setᵉ (𝕊¹ᵉ ≃ᵉ Xᵉ))

point-ℂP∞ᵉ : ℂP∞ᵉ
pr1ᵉ point-ℂP∞ᵉ = 𝕊¹ᵉ
pr2ᵉ point-ℂP∞ᵉ = unit-trunc-Setᵉ id-equivᵉ
```

### `ℂP∞` as the `2`-truncation of the `2`-sphere

Thisᵉ remainsᵉ to beᵉ defined.ᵉ
[#742](https://github.com/UniMath/agda-unimath/issues/742ᵉ)