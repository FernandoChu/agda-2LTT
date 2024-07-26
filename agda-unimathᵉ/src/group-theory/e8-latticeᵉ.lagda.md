# The `E₈`-lattice

```agda
module group-theory.e8-latticeᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ

open import foundation.equality-coproduct-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

### The ambient set of the E₈ lattice

Theᵉ E₈ᵉ latticeᵉ itselfᵉ isᵉ aᵉ subsetᵉ ofᵉ theᵉ followingᵉ set.ᵉ

```agda
ambient-set-E8-latticeᵉ : Setᵉ lzero
ambient-set-E8-latticeᵉ =
  coproduct-Setᵉ (hom-set-Setᵉ (Fin-Setᵉ 8ᵉ) ℤ-Setᵉ) (hom-set-Setᵉ (Fin-Setᵉ 8ᵉ) ℤ-Setᵉ)
```