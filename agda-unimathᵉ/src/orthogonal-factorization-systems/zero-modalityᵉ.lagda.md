# The zero modality

```agda
module orthogonal-factorization-systems.zero-modalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.local-typesᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Theᵉ **zeroᵉ modality**ᵉ isᵉ theᵉ
[modality](orthogonal-factorization-systems.higher-modalities.mdᵉ) thatᵉ mapsᵉ
everyᵉ typeᵉ to theᵉ [unitᵉ type](foundation.unit-type.md).ᵉ

## Definition

```agda
operator-zero-modalityᵉ :
  (l1ᵉ l2ᵉ : Level) → operator-modalityᵉ l1ᵉ l2ᵉ
operator-zero-modalityᵉ l1ᵉ l2ᵉ _ = raise-unitᵉ l2ᵉ

unit-zero-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} → unit-modalityᵉ (operator-zero-modalityᵉ l1ᵉ l2ᵉ)
unit-zero-modalityᵉ _ = raise-starᵉ
```

## Properties

### The zero modality is a uniquely eliminating modality

```agda
is-uniquely-eliminating-modality-zero-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} →
  is-uniquely-eliminating-modalityᵉ (unit-zero-modalityᵉ {l1ᵉ} {l2ᵉ})
is-uniquely-eliminating-modality-zero-modalityᵉ {l2ᵉ = l2ᵉ} Pᵉ =
  is-local-is-contrᵉ
    ( unit-zero-modalityᵉ)
    ( raise-unitᵉ l2ᵉ)
    ( is-contr-raise-unitᵉ)
```

### The zero modality is equivalent to `-2`-truncation

Thisᵉ remainsᵉ to beᵉ madeᵉ formal.ᵉ
[#739](https://github.com/UniMath/agda-unimath/issues/739ᵉ)