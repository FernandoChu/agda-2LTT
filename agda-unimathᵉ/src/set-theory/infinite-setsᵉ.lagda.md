# Infinite sets

```agda
module set-theory.infinite-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.mere-embeddingsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ setᵉ `A`ᵉ isᵉ saidᵉ to beᵉ infiniteᵉ ifᵉ itᵉ containsᵉ arbitrarilyᵉ largeᵉ finiteᵉ
subsets.ᵉ

## Definition

```agda
is-infinite-Set-Propᵉ : {lᵉ : Level} → Setᵉ lᵉ → Propᵉ lᵉ
is-infinite-Set-Propᵉ Xᵉ = Π-Propᵉ ℕᵉ (λ nᵉ → mere-emb-Propᵉ (Finᵉ nᵉ) (type-Setᵉ Xᵉ))

is-infinite-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → UUᵉ lᵉ
is-infinite-Setᵉ Xᵉ = type-Propᵉ (is-infinite-Set-Propᵉ Xᵉ)
```