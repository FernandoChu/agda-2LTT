# The plus-principle

```agda
module synthetic-homotopy-theory.plus-principleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.acyclic-typesᵉ
```

</details>

## Idea

Theᵉ **plus-principle**ᵉ assertsᵉ thatᵉ anyᵉ
[acyclic](synthetic-homotopy-theory.acyclic-types.mdᵉ)
[1-connectedᵉ type](foundation.connected-types.mdᵉ) isᵉ
[contractible](foundation.contractible-types.md).ᵉ

## Definition

```agda
plus-principleᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
plus-principleᵉ lᵉ =
  (Aᵉ : UUᵉ lᵉ) → is-acyclicᵉ Aᵉ → is-connectedᵉ one-𝕋ᵉ Aᵉ → is-contrᵉ Aᵉ
```