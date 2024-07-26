# Factorization operations

```agda
module orthogonal-factorization-systems.factorization-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.factorizations-of-mapsᵉ
```

</details>

## Idea

Aᵉ **factorizationᵉ operation**ᵉ onᵉ aᵉ functionᵉ typeᵉ `Aᵉ → B`ᵉ isᵉ aᵉ choiceᵉ ofᵉ
[factorization](orthogonal-factorization-systems.factorizations-of-maps.mdᵉ) forᵉ
everyᵉ mapᵉ `f`ᵉ in `Aᵉ → B`.ᵉ

```text
      Imᵉ fᵉ
      ∧ᵉ  \ᵉ
     /ᵉ    \ᵉ
    /ᵉ      ∨ᵉ
  Aᵉ ------>ᵉ Bᵉ
       fᵉ
```

## Definition

### Factorization operations

```agda
instance-factorization-operationᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
instance-factorization-operationᵉ l3ᵉ Aᵉ Bᵉ = (fᵉ : Aᵉ → Bᵉ) → factorizationᵉ l3ᵉ fᵉ

factorization-operationᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
factorization-operationᵉ l1ᵉ l2ᵉ l3ᵉ =
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → instance-factorization-operationᵉ l3ᵉ Aᵉ Bᵉ
```