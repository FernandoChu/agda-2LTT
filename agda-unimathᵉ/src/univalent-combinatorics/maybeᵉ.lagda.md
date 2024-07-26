# The maybe modality on finite types

```agda
module univalent-combinatorics.maybeᵉ where

open import foundation.maybeᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

```agda
add-free-point-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ kᵉ → UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)
add-free-point-UU-Finᵉ kᵉ Xᵉ = coproduct-UU-Finᵉ kᵉ 1 Xᵉ unit-UU-Finᵉ
```