# Locally small modal-operators

```agda
module orthogonal-factorization-systems.locally-small-modal-operatorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
```

</details>

## Idea

Aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ) isᵉ
**locallyᵉ small**ᵉ ifᵉ itᵉ mapsᵉ [smallᵉ types](foundation.small-types.mdᵉ) to
[locallyᵉ smallᵉ types](foundation.locally-small-types.md).ᵉ

## Definitions

### Locally small modal operators

```agda
is-locally-small-operator-modalityᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
is-locally-small-operator-modalityᵉ {l1ᵉ} l3ᵉ ○ᵉ =
  (Xᵉ : UUᵉ l1ᵉ) → is-locally-smallᵉ l3ᵉ (○ᵉ Xᵉ)

locally-small-operator-modalityᵉ :
  (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l3ᵉ =
  Σᵉ ( operator-modalityᵉ l1ᵉ l2ᵉ)
    ( is-locally-small-operator-modalityᵉ l3ᵉ)

operator-modality-locally-small-operator-modalityᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} →
  locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l3ᵉ → operator-modalityᵉ l1ᵉ l2ᵉ
operator-modality-locally-small-operator-modalityᵉ = pr1ᵉ

is-locally-small-locally-small-operator-modalityᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (○ᵉ : locally-small-operator-modalityᵉ l1ᵉ l2ᵉ l3ᵉ) →
  is-locally-small-operator-modalityᵉ l3ᵉ
    ( operator-modality-locally-small-operator-modalityᵉ ○ᵉ)
is-locally-small-locally-small-operator-modalityᵉ = pr2ᵉ
```