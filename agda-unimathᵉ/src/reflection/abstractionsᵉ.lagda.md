# Abstractions

```agda
module reflection.abstractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import primitives.stringsᵉ
```

</details>

## Idea

Theᵉ `Abstraction-Agda`ᵉ typeᵉ representsᵉ aᵉ lambdaᵉ abstraction.ᵉ

## Definition

```agda
data Abstraction-Agdaᵉ {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) : UUᵉ lᵉ where
  cons-Abstraction-Agdaᵉ : Stringᵉ → Aᵉ → Abstraction-Agdaᵉ Aᵉ



```