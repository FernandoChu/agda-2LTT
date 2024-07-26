# The Zariski topology on the set of prime ideals of a commutative ring

```agda
module commutative-algebra.zariski-topologyᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.prime-ideals-commutative-ringsᵉ

open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **Zariskiᵉ topology**ᵉ onᵉ theᵉ setᵉ ofᵉ primeᵉ idealsᵉ in aᵉ commutativeᵉ ringᵉ isᵉ
describedᵉ byᵉ whatᵉ theᵉ closedᵉ setsᵉ areᵉ: Aᵉ subsetᵉ `I`ᵉ ofᵉ primeᵉ idealsᵉ isᵉ closedᵉ ifᵉ
itᵉ isᵉ theᵉ intersectionᵉ ofᵉ allᵉ theᵉ primeᵉ idealsᵉ thatᵉ

## Definitions

### Closed subsets in the Zariski topology

```agda
standard-closed-subset-zariski-topology-Commutative-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) →
  subtypeᵉ l3ᵉ (type-Commutative-Ringᵉ Aᵉ) →
  subtypeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) (prime-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
standard-closed-subset-zariski-topology-Commutative-Ringᵉ Aᵉ Uᵉ Pᵉ =
  leq-prop-subtypeᵉ Uᵉ (subset-prime-ideal-Commutative-Ringᵉ Aᵉ Pᵉ)

is-closed-subset-zariski-topology-Commutative-Ringᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Uᵉ : subtypeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) (prime-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)) →
  Propᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
is-closed-subset-zariski-topology-Commutative-Ringᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ Uᵉ =
  exists-structure-Propᵉ
    ( subtypeᵉ l3ᵉ (type-Commutative-Ringᵉ Aᵉ))
    ( λ Vᵉ → standard-closed-subset-zariski-topology-Commutative-Ringᵉ Aᵉ Vᵉ ＝ᵉ Uᵉ)

closed-subset-zariski-topology-Commutative-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : Commutative-Ringᵉ l1ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
closed-subset-zariski-topology-Commutative-Ringᵉ {l1ᵉ} {l2ᵉ} l3ᵉ Aᵉ =
  type-subtypeᵉ
    ( is-closed-subset-zariski-topology-Commutative-Ringᵉ {l1ᵉ} {l2ᵉ} {l3ᵉ} Aᵉ)
```