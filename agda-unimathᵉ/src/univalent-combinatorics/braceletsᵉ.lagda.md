# Bracelets

```agda
module univalent-combinatorics.braceletsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.polygonsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

### Bracelets

```agda
braceletᵉ : ℕᵉ → ℕᵉ → UUᵉ (lsuc lzero)
braceletᵉ mᵉ nᵉ = Σᵉ (Polygonᵉ mᵉ) (λ Xᵉ → vertex-Polygonᵉ mᵉ Xᵉ → Finᵉ nᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}