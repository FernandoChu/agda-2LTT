# Small pointed types

```agda
module structured-types.small-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.small-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) isᵉ saidᵉ to beᵉ
{{#conceptᵉ "small"ᵉ Disambiguation="pointedᵉ type"ᵉ Agda=is-small-Pointed-Typeᵉ}} isᵉ
itsᵉ underlyingᵉ typeᵉ isᵉ [small](foundation.small-types.md).ᵉ Equivalently,ᵉ weᵉ sayᵉ
thatᵉ aᵉ pointedᵉ typeᵉ isᵉ
{{#conceptᵉ "pointedᵉ small"ᵉ Agda=is-pointed-small-Pointed-Typeᵉ}} ifᵉ itᵉ comesᵉ
equippedᵉ with anᵉ elementᵉ ofᵉ typeᵉ

```text
  Σᵉ (Yᵉ : Pointed-Typeᵉ l),ᵉ Xᵉ ≃∗ᵉ Yᵉ
```

Theᵉ differenceᵉ betweenᵉ smallᵉ pointedᵉ typesᵉ andᵉ pointedᵉ smallᵉ pointedᵉ typesᵉ isᵉ
thatᵉ theᵉ notionᵉ ofᵉ smallᵉ pointedᵉ typeᵉ isᵉ unpointed,ᵉ andᵉ thereforeᵉ potentiallyᵉ
easierᵉ to establish.ᵉ Itᵉ isᵉ immediateᵉ thatᵉ aᵉ pointedᵉ smallᵉ typeᵉ isᵉ small.ᵉ Forᵉ theᵉ
converse,ᵉ noteᵉ thatᵉ ifᵉ `X`ᵉ isᵉ small,ᵉ andᵉ `Yᵉ : 𝒰`ᵉ comesᵉ equippedᵉ with anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) `eᵉ : type-Pointed-Typeᵉ Xᵉ ≃ᵉ Y`,ᵉ
thenᵉ weᵉ takeᵉ `eᵉ *ᵉ : Y`ᵉ to beᵉ theᵉ baseᵉ point,ᵉ andᵉ itᵉ isᵉ immediateᵉ thatᵉ `e`ᵉ isᵉ aᵉ
[pointedᵉ equivalence](structured-types.pointed-equivalences.md).ᵉ

## Definitions

### Small pointed types

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-small-prop-Pointed-Typeᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-small-prop-Pointed-Typeᵉ = is-small-Propᵉ l2ᵉ (type-Pointed-Typeᵉ Xᵉ)

  is-small-Pointed-Typeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-small-Pointed-Typeᵉ = is-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Xᵉ)

  is-prop-is-small-Pointed-Typeᵉ : is-propᵉ is-small-Pointed-Typeᵉ
  is-prop-is-small-Pointed-Typeᵉ = is-prop-is-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Xᵉ)
```

### Pointedly small types

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-pointed-small-Pointed-Typeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-pointed-small-Pointed-Typeᵉ =
    Σᵉ (Pointed-Typeᵉ l2ᵉ) (λ Yᵉ → Xᵉ ≃∗ᵉ Yᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  (Hᵉ : is-pointed-small-Pointed-Typeᵉ l2ᵉ Xᵉ)
  where

  pointed-type-is-pointed-small-Pointed-Typeᵉ : Pointed-Typeᵉ l2ᵉ
  pointed-type-is-pointed-small-Pointed-Typeᵉ = pr1ᵉ Hᵉ

  type-is-pointed-small-Pointed-Typeᵉ : UUᵉ l2ᵉ
  type-is-pointed-small-Pointed-Typeᵉ =
    type-Pointed-Typeᵉ pointed-type-is-pointed-small-Pointed-Typeᵉ

  point-is-pointed-small-Pointed-Typeᵉ :
    type-is-pointed-small-Pointed-Typeᵉ
  point-is-pointed-small-Pointed-Typeᵉ =
    point-Pointed-Typeᵉ pointed-type-is-pointed-small-Pointed-Typeᵉ

  pointed-equiv-is-pointed-small-Pointed-Typeᵉ :
    Xᵉ ≃∗ᵉ pointed-type-is-pointed-small-Pointed-Typeᵉ
  pointed-equiv-is-pointed-small-Pointed-Typeᵉ = pr2ᵉ Hᵉ

  equiv-is-pointed-small-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Xᵉ ≃ᵉ type-is-pointed-small-Pointed-Typeᵉ
  equiv-is-pointed-small-Pointed-Typeᵉ =
    equiv-pointed-equivᵉ pointed-equiv-is-pointed-small-Pointed-Typeᵉ
```

## Properties

### Being pointed small is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-prop-is-pointed-small-Pointed-Typeᵉ :
    is-propᵉ (is-pointed-small-Pointed-Typeᵉ l2ᵉ Xᵉ)
  is-prop-is-pointed-small-Pointed-Typeᵉ =
    is-prop-has-elementᵉ
      ( λ (Yᵉ ,ᵉ eᵉ) →
        is-prop-equiv'ᵉ
          ( equiv-totᵉ (λ Zᵉ → equiv-comp-pointed-equiv'ᵉ eᵉ))
          ( is-prop-is-contrᵉ (is-torsorial-pointed-equivᵉ Yᵉ)))

module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-pointed-small-prop-Pointed-Typeᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ is-pointed-small-prop-Pointed-Typeᵉ =
    is-pointed-small-Pointed-Typeᵉ l2ᵉ Xᵉ
  pr2ᵉ is-pointed-small-prop-Pointed-Typeᵉ =
    is-prop-is-pointed-small-Pointed-Typeᵉ Xᵉ
```

### A pointed type is small if and only if it is pointed small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-pointed-small-is-small-Pointed-Typeᵉ :
    is-small-Pointed-Typeᵉ l2ᵉ Xᵉ → is-pointed-small-Pointed-Typeᵉ l2ᵉ Xᵉ
  pr1ᵉ (pr1ᵉ (is-pointed-small-is-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ))) =
    Yᵉ
  pr2ᵉ (pr1ᵉ (is-pointed-small-is-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ))) =
    map-equivᵉ eᵉ (point-Pointed-Typeᵉ Xᵉ)
  pr1ᵉ (pr2ᵉ (is-pointed-small-is-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ))) =
    eᵉ
  pr2ᵉ (pr2ᵉ (is-pointed-small-is-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ))) =
    reflᵉ

  is-small-is-pointed-small-Pointed-Typeᵉ :
    is-pointed-small-Pointed-Typeᵉ l2ᵉ Xᵉ → is-small-Pointed-Typeᵉ l2ᵉ Xᵉ
  pr1ᵉ (is-small-is-pointed-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ)) =
    type-Pointed-Typeᵉ Yᵉ
  pr2ᵉ (is-small-is-pointed-small-Pointed-Typeᵉ (Yᵉ ,ᵉ eᵉ)) =
    equiv-pointed-equivᵉ eᵉ
```