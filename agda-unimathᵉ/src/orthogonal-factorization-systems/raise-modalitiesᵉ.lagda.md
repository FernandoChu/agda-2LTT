# The raise modalities

```agda
module orthogonal-factorization-systems.raise-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Theᵉ operationsᵉ ofᵉ
[raisingᵉ universeᵉ levels](foundation.raising-universe-levels.mdᵉ) areᵉ triviallyᵉ
[higherᵉ modalities](orthogonal-factorization-systems.higher-modalities.md),ᵉ andᵉ
in theᵉ caseᵉ thatᵉ `l1ᵉ ⊔ l2ᵉ = l1`,ᵉ weᵉ recoverᵉ theᵉ
[identityᵉ modality](orthogonal-factorization-systems.identity-modality.md).ᵉ

## Definition

```agda
operator-raise-modalityᵉ :
  (l1ᵉ l2ᵉ : Level) → operator-modalityᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
operator-raise-modalityᵉ l1ᵉ l2ᵉ = raiseᵉ l2ᵉ

unit-raise-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} → unit-modalityᵉ (operator-raise-modalityᵉ l1ᵉ l2ᵉ)
unit-raise-modalityᵉ = map-raiseᵉ
```

## Properties

### The raise modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-raise-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} →
  is-uniquely-eliminating-modalityᵉ (unit-raise-modalityᵉ {l1ᵉ} {l2ᵉ})
is-uniquely-eliminating-modality-raise-modalityᵉ {l1ᵉ} {l2ᵉ} Pᵉ =
  is-local-dependent-type-is-equivᵉ
    ( unit-raise-modalityᵉ)
    ( is-equiv-map-raiseᵉ)
    ( operator-raise-modalityᵉ l1ᵉ l2ᵉ ∘ᵉ Pᵉ)
```

### In the case that `l1 ⊔ l2 = l1` we recover the identity modality

Thisᵉ remainsᵉ to beᵉ madeᵉ formal.ᵉ
[#739](https://github.com/UniMath/agda-unimath/issues/739ᵉ)