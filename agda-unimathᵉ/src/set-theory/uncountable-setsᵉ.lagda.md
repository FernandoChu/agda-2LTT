# Uncountable sets

```agda
module set-theory.uncountable-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import set-theory.countable-setsᵉ
```

</details>

## Definition

```agda
is-uncountable-Propᵉ : {lᵉ : Level} → Setᵉ lᵉ → Propᵉ lᵉ
is-uncountable-Propᵉ Xᵉ = neg-Propᵉ (is-countable-Propᵉ Xᵉ)

is-uncountableᵉ : {lᵉ : Level} → Setᵉ lᵉ → UUᵉ lᵉ
is-uncountableᵉ Xᵉ = type-Propᵉ (is-uncountable-Propᵉ Xᵉ)

is-prop-is-uncountableᵉ : {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → is-propᵉ (is-uncountableᵉ Xᵉ)
is-prop-is-uncountableᵉ Xᵉ = is-prop-type-Propᵉ (is-uncountable-Propᵉ Xᵉ)
```