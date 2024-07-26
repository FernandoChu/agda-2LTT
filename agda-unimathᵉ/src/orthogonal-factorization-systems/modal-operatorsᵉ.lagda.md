# Modal operators

```agda
module orthogonal-factorization-systems.modal-operatorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.small-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Underlyingᵉ everyᵉ modalityᵉ isᵉ aᵉ **modalᵉ operator**,ᵉ whichᵉ isᵉ anᵉ operationᵉ onᵉ
typesᵉ thatᵉ constructᵉ newᵉ types.ᵉ Forᵉ aᵉ _monadicᵉ_ modalityᵉ `○`,ᵉ thereᵉ isᵉ moreoverᵉ
aᵉ **modalᵉ unit**ᵉ thatᵉ comparesᵉ everyᵉ typeᵉ `X`ᵉ to itsᵉ modalᵉ typeᵉ `○ᵉ X`ᵉ
(`Xᵉ → ○ᵉ X`).ᵉ

## Definitions

### Modal operators

```agda
operator-modalityᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
operator-modalityᵉ l1ᵉ l2ᵉ = UUᵉ l1ᵉ → UUᵉ l2ᵉ
```

### Modal units

```agda
unit-modalityᵉ : {l1ᵉ l2ᵉ : Level} → operator-modalityᵉ l1ᵉ l2ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
unit-modalityᵉ {l1ᵉ} ○ᵉ = {Xᵉ : UUᵉ l1ᵉ} → Xᵉ → ○ᵉ Xᵉ
```

### The subuniverse of modal types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  is-modalᵉ : (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-modalᵉ Xᵉ = is-equivᵉ (unit-○ᵉ {Xᵉ})

  is-modal-familyᵉ : {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} (Pᵉ : Xᵉ → UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-modal-familyᵉ {Xᵉ = Xᵉ} Pᵉ = (xᵉ : Xᵉ) → is-modalᵉ (Pᵉ xᵉ)

  modal-typeᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  modal-typeᵉ = Σᵉ (UUᵉ l1ᵉ) (is-modalᵉ)

  is-modal-Propᵉ : (Xᵉ : UUᵉ l1ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-modal-Propᵉ Xᵉ = is-equiv-Propᵉ (unit-○ᵉ {Xᵉ})

  is-property-is-modalᵉ : (Xᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-modalᵉ Xᵉ)
  is-property-is-modalᵉ Xᵉ = is-prop-type-Propᵉ (is-modal-Propᵉ Xᵉ)

  is-subuniverse-is-modalᵉ : is-subuniverseᵉ is-modalᵉ
  is-subuniverse-is-modalᵉ = is-property-is-modalᵉ

  modal-type-subuniverseᵉ : subuniverseᵉ l1ᵉ (l1ᵉ ⊔ l2ᵉ)
  modal-type-subuniverseᵉ = is-modal-Propᵉ
```

### Modal small types

Aᵉ smallᵉ typeᵉ isᵉ saidᵉ to beᵉ modalᵉ ifᵉ itsᵉ smallᵉ equivalentᵉ isᵉ modal.ᵉ

```agda
is-modal-type-is-smallᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (Xᵉ : UUᵉ l3ᵉ) (is-small-Xᵉ : is-smallᵉ l1ᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-modal-type-is-smallᵉ unit-○ᵉ Xᵉ is-small-Xᵉ =
  is-modalᵉ unit-○ᵉ (type-is-smallᵉ is-small-Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (Xᵉ : UUᵉ l3ᵉ) (is-small-Xᵉ : is-smallᵉ l1ᵉ Xᵉ)
  where

  is-equiv-unit-is-modal-type-is-smallᵉ :
    is-modal-type-is-smallᵉ unit-○ᵉ Xᵉ is-small-Xᵉ →
    is-equivᵉ (unit-○ᵉ ∘ᵉ map-equiv-is-smallᵉ is-small-Xᵉ)
  is-equiv-unit-is-modal-type-is-smallᵉ =
    is-equiv-compᵉ
      ( unit-○ᵉ)
      ( map-equiv-is-smallᵉ is-small-Xᵉ)
      ( is-equiv-map-equivᵉ (equiv-is-smallᵉ is-small-Xᵉ))

  equiv-unit-is-modal-type-is-smallᵉ :
    is-modal-type-is-smallᵉ unit-○ᵉ Xᵉ is-small-Xᵉ →
    Xᵉ ≃ᵉ ○ᵉ (type-is-smallᵉ is-small-Xᵉ)
  pr1ᵉ (equiv-unit-is-modal-type-is-smallᵉ mᵉ) =
    unit-○ᵉ ∘ᵉ map-equiv-is-smallᵉ is-small-Xᵉ
  pr2ᵉ (equiv-unit-is-modal-type-is-smallᵉ mᵉ) =
    is-equiv-unit-is-modal-type-is-smallᵉ mᵉ

  map-inv-unit-is-modal-type-is-smallᵉ :
    is-modal-type-is-smallᵉ unit-○ᵉ Xᵉ is-small-Xᵉ →
    ○ᵉ (type-is-smallᵉ is-small-Xᵉ) → Xᵉ
  map-inv-unit-is-modal-type-is-smallᵉ =
    map-inv-equivᵉ ∘ᵉ equiv-unit-is-modal-type-is-smallᵉ

module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ} (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (Xᵉ : Small-Typeᵉ l1ᵉ l3ᵉ)
  where

  is-modal-Small-Typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-modal-Small-Typeᵉ =
    is-modal-type-is-smallᵉ unit-○ᵉ
      ( type-Small-Typeᵉ Xᵉ)
      ( is-small-type-Small-Typeᵉ Xᵉ)

  is-equiv-unit-is-modal-Small-Typeᵉ :
    is-modal-Small-Typeᵉ →
    is-equivᵉ (unit-○ᵉ ∘ᵉ map-equivᵉ (equiv-is-small-type-Small-Typeᵉ Xᵉ))
  is-equiv-unit-is-modal-Small-Typeᵉ =
    is-equiv-unit-is-modal-type-is-smallᵉ unit-○ᵉ
      ( type-Small-Typeᵉ Xᵉ)
      ( is-small-type-Small-Typeᵉ Xᵉ)

  equiv-unit-is-modal-Small-Typeᵉ :
    is-modal-Small-Typeᵉ → type-Small-Typeᵉ Xᵉ ≃ᵉ ○ᵉ (small-type-Small-Typeᵉ Xᵉ)
  equiv-unit-is-modal-Small-Typeᵉ =
    equiv-unit-is-modal-type-is-smallᵉ unit-○ᵉ
      ( type-Small-Typeᵉ Xᵉ)
      ( is-small-type-Small-Typeᵉ Xᵉ)

  map-inv-unit-is-modal-Small-Typeᵉ :
    is-modal-Small-Typeᵉ → ○ᵉ (small-type-Small-Typeᵉ Xᵉ) → type-Small-Typeᵉ Xᵉ
  map-inv-unit-is-modal-Small-Typeᵉ =
    map-inv-equivᵉ ∘ᵉ equiv-unit-is-modal-Small-Typeᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}