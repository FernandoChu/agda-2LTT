# Steiner triple systems

```agda
module univalent-combinatorics.steiner-triple-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import univalent-combinatorics.steiner-systemsᵉ
```

</details>

## Definition

```agda
Steiner-Triple-Systemᵉ : ℕᵉ → UUᵉ (lsuc lzero)
Steiner-Triple-Systemᵉ nᵉ = Steiner-Systemᵉ 2 3 nᵉ
```