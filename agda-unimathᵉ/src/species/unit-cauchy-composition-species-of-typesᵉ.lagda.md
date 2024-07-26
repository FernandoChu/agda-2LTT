# The unit of Cauchy composition of types

```agda
module species.unit-cauchy-composition-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ **unit**ᵉ ofᵉ Cauchyᵉ compositionᵉ ofᵉ speciesᵉ ofᵉ typesᵉ isᵉ theᵉ speciesᵉ

```text
  Xᵉ ↦ᵉ is-contrᵉ X.ᵉ
```

## Definition

```agda
unit-species-typesᵉ : {l1ᵉ : Level} → species-typesᵉ l1ᵉ l1ᵉ
unit-species-typesᵉ = is-contrᵉ
```