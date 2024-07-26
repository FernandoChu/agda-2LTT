# Species of finite types

```agda
module species.species-of-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import species.species-of-types-in-subuniversesᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **speciesᵉ ofᵉ finiteᵉ types**ᵉ isᵉ aᵉ mapᵉ fromᵉ `𝔽`ᵉ to aᵉ `𝔽`.ᵉ

## Definition

```agda
species-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
species-𝔽ᵉ l1ᵉ l2ᵉ =
  species-subuniverseᵉ (is-finite-Propᵉ {l1ᵉ}) (is-finite-Propᵉ {l2ᵉ})
```