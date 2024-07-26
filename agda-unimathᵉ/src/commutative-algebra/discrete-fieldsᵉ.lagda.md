# Discrete fields

```agda
module commutative-algebra.discrete-fieldsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.division-ringsᵉ
```

</details>

## Idea

Aᵉ **discreteᵉ field**ᵉ isᵉ aᵉ commutativeᵉ divisionᵉ ring.ᵉ Theyᵉ areᵉ calledᵉ discrete,ᵉ
becauseᵉ onlyᵉ nonzeroᵉ elementsᵉ areᵉ assumedᵉ to beᵉ invertible.ᵉ

## Definition

```agda
is-discrete-field-Commutative-Ringᵉ : {lᵉ : Level} → Commutative-Ringᵉ lᵉ → UUᵉ lᵉ
is-discrete-field-Commutative-Ringᵉ Aᵉ =
  is-division-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```