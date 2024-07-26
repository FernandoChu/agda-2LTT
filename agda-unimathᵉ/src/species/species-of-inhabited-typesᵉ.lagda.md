# Species of inhabited types

```agda
module species.species-of-inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Aᵉ **speciesᵉ ofᵉ inhabitedᵉ types**ᵉ isᵉ aᵉ mapᵉ fromᵉ theᵉ subuniverseᵉ ofᵉ inhabitedᵉ
typesᵉ to aᵉ universe.ᵉ

## Definition

```agda
species-inhabited-typesᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
species-inhabited-typesᵉ l1ᵉ l2ᵉ =
  species-subuniverseᵉ (is-inhabited-Propᵉ {l1ᵉ}) λ (Xᵉ : UUᵉ l2ᵉ) → unit-Propᵉ
```