# Species of finite inhabited types

```agda
module species.species-of-finite-inhabited-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import species.species-of-types-in-subuniversesᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.inhabited-finite-typesᵉ
```

</details>

## Idea

Aᵉ **speciesᵉ ofᵉ finiteᵉ inhabitedᵉ types**ᵉ isᵉ aᵉ mapᵉ fromᵉ theᵉ subuniverseᵉ ofᵉ finiteᵉ
inhabitedᵉ typesᵉ to aᵉ universeᵉ ofᵉ finiteᵉ types.ᵉ

## Definition

```agda
species-Inhabited-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
species-Inhabited-𝔽ᵉ l1ᵉ l2ᵉ =
  species-subuniverseᵉ (is-finite-and-inhabited-Propᵉ {l1ᵉ}) (is-finite-Propᵉ {l2ᵉ})
```