# Pointed torsorial type families

```agda
module foundation.pointed-torsorial-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.sorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `E`ᵉ overᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `B`ᵉ
isᵉ saidᵉ to beᵉ **pointedᵉ torsorial**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ with aᵉ familyᵉ ofᵉ
equivalencesᵉ

```text
  Eᵉ xᵉ ≃ᵉ (ptᵉ ＝ᵉ xᵉ)
```

indexedᵉ byᵉ `xᵉ : B`.ᵉ Noteᵉ thatᵉ theᵉ typeᵉ ofᵉ suchᵉ aᵉ **torsorialᵉ structure**ᵉ onᵉ theᵉ
typeᵉ familyᵉ `E`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ

```text
  Eᵉ ptᵉ ×ᵉ is-torsorialᵉ Eᵉ
```

Indeed,ᵉ ifᵉ `E`ᵉ isᵉ pointedᵉ torsorial,ᵉ thenᵉ `reflᵉ : ptᵉ ＝ᵉ pt`ᵉ inducesᵉ anᵉ elementᵉ
in `Eᵉ pt`,ᵉ andᵉ theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ) ofᵉ `E`ᵉ isᵉ
[contractible](foundation.contractible-types.mdᵉ) byᵉ theᵉ
[fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.md).ᵉ
Conversely,ᵉ ifᵉ weᵉ areᵉ givenᵉ anᵉ elementᵉ `yᵉ : Eᵉ pt`ᵉ andᵉ theᵉ totalᵉ spaceᵉ ofᵉ `E`ᵉ isᵉ
contractible,ᵉ thenᵉ theᵉ uniqueᵉ familyᵉ ofᵉ mapsᵉ `(ptᵉ ＝ᵉ xᵉ) → Eᵉ x`ᵉ mappingᵉ `refl`ᵉ to
`y`ᵉ isᵉ aᵉ familyᵉ ofᵉ equivalences.ᵉ

## Definitions

### The predicate of being a pointed torsorial type family

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) (Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ)
  where

  is-pointed-torsorial-family-of-typesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pointed-torsorial-family-of-typesᵉ =
    (xᵉ : type-Pointed-Typeᵉ Bᵉ) → Eᵉ xᵉ ≃ᵉ (point-Pointed-Typeᵉ Bᵉ ＝ᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) {Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ}
  (Tᵉ : is-pointed-torsorial-family-of-typesᵉ Bᵉ Eᵉ)
  where

  point-is-pointed-torsorial-family-of-typesᵉ : Eᵉ (point-Pointed-Typeᵉ Bᵉ)
  point-is-pointed-torsorial-family-of-typesᵉ =
    map-inv-equivᵉ (Tᵉ (point-Pointed-Typeᵉ Bᵉ)) reflᵉ

  is-torsorial-space-is-pointed-torsorial-family-of-typesᵉ :
    is-torsorialᵉ Eᵉ
  is-torsorial-space-is-pointed-torsorial-family-of-typesᵉ =
    fundamental-theorem-id'ᵉ
      ( λ xᵉ → map-inv-equivᵉ (Tᵉ xᵉ))
      ( λ xᵉ → is-equiv-map-inv-equivᵉ (Tᵉ xᵉ))
```

### Torsorial families of types

```agda
pointed-torsorial-family-of-typesᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Bᵉ : Pointed-Typeᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ =
  Σᵉ (type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ) (is-pointed-torsorial-family-of-typesᵉ Bᵉ)
```

## Properties

### Any torsorial type family is sorial

```agda
is-sorial-is-pointed-torsorial-family-of-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) {Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ} →
  is-pointed-torsorial-family-of-typesᵉ Bᵉ Eᵉ → is-sorial-family-of-typesᵉ Bᵉ Eᵉ
is-sorial-is-pointed-torsorial-family-of-typesᵉ Bᵉ {Eᵉ} Hᵉ xᵉ yᵉ =
  equiv-trᵉ Eᵉ (map-equivᵉ (Hᵉ xᵉ) yᵉ)
```

### Being pointed torsorial is equivalent to being pointed and having contractible total space

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) {Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ}
  where

  point-and-contractible-total-space-is-pointed-torsorial-family-of-typesᵉ :
    is-pointed-torsorial-family-of-typesᵉ Bᵉ Eᵉ →
    Eᵉ (point-Pointed-Typeᵉ Bᵉ) ×ᵉ is-contrᵉ (Σᵉ (type-Pointed-Typeᵉ Bᵉ) Eᵉ)
  pr1ᵉ
    ( point-and-contractible-total-space-is-pointed-torsorial-family-of-typesᵉ Hᵉ)
    =
    point-is-pointed-torsorial-family-of-typesᵉ Bᵉ Hᵉ
  pr2ᵉ
    ( point-and-contractible-total-space-is-pointed-torsorial-family-of-typesᵉ Hᵉ)
    =
    is-torsorial-space-is-pointed-torsorial-family-of-typesᵉ Bᵉ Hᵉ
```

### Pointed connected types equipped with a pointed torsorial family of types of universe level `l` are locally `l`-small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ) {Eᵉ : type-Pointed-Typeᵉ Bᵉ → UUᵉ l2ᵉ}
  (Tᵉ : is-pointed-torsorial-family-of-typesᵉ Bᵉ Eᵉ)
  where

  abstract
    is-locally-small-is-pointed-torsorial-family-of-typesᵉ :
      is-0-connectedᵉ (type-Pointed-Typeᵉ Bᵉ) →
      is-locally-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ)
    is-locally-small-is-pointed-torsorial-family-of-typesᵉ Hᵉ xᵉ yᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-is-0-connectedᵉ Hᵉ (point-Pointed-Typeᵉ Bᵉ) xᵉ)
        ( is-small-Propᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ))
        ( λ where reflᵉ → (Eᵉ yᵉ ,ᵉ inv-equivᵉ (Tᵉ yᵉ)))
```

### The type of pointed torsorial type families of universe level `l` over a pointed connected type is equivalent to the proposition that `B` is locally `l`-small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-locally-small-pointed-torsorial-family-of-typesᵉ :
    is-0-connectedᵉ (type-Pointed-Typeᵉ Bᵉ) →
    pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ →
    is-locally-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ)
  is-locally-small-pointed-torsorial-family-of-typesᵉ Hᵉ (Eᵉ ,ᵉ Tᵉ) =
    is-locally-small-is-pointed-torsorial-family-of-typesᵉ Bᵉ Tᵉ Hᵉ

  pointed-torsorial-family-of-types-is-locally-smallᵉ :
    is-locally-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ) →
    pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ
  pr1ᵉ (pointed-torsorial-family-of-types-is-locally-smallᵉ Hᵉ) xᵉ =
    type-is-smallᵉ (Hᵉ (point-Pointed-Typeᵉ Bᵉ) xᵉ)
  pr2ᵉ (pointed-torsorial-family-of-types-is-locally-smallᵉ Hᵉ) xᵉ =
    inv-equiv-is-smallᵉ (Hᵉ (point-Pointed-Typeᵉ Bᵉ) xᵉ)

  is-prop-pointed-torsorial-family-of-typesᵉ :
    is-propᵉ (pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ)
  is-prop-pointed-torsorial-family-of-typesᵉ =
    is-prop-equiv'ᵉ
      ( distributive-Π-Σᵉ)
      ( is-prop-Πᵉ
        ( λ xᵉ →
          is-prop-equivᵉ
            ( equiv-totᵉ (λ Xᵉ → equiv-inv-equivᵉ))
            ( is-prop-is-smallᵉ l2ᵉ (point-Pointed-Typeᵉ Bᵉ ＝ᵉ xᵉ))))

  compute-pointed-torsorial-family-of-types-is-0-connectedᵉ :
    is-0-connectedᵉ (type-Pointed-Typeᵉ Bᵉ) →
    is-locally-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ) ≃ᵉ
    pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ
  compute-pointed-torsorial-family-of-types-is-0-connectedᵉ Hᵉ =
    equiv-iffᵉ
      ( is-locally-small-Propᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ))
      ( pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ ,ᵉ
        is-prop-pointed-torsorial-family-of-typesᵉ)
      ( pointed-torsorial-family-of-types-is-locally-smallᵉ)
      ( is-locally-small-pointed-torsorial-family-of-typesᵉ Hᵉ)

  is-contr-pointed-torsorial-family-of-typesᵉ :
    is-locally-smallᵉ l2ᵉ (type-Pointed-Typeᵉ Bᵉ) →
    is-contrᵉ (pointed-torsorial-family-of-typesᵉ l2ᵉ Bᵉ)
  is-contr-pointed-torsorial-family-of-typesᵉ Hᵉ =
    is-proof-irrelevant-is-propᵉ
      ( is-prop-pointed-torsorial-family-of-typesᵉ)
      ( pointed-torsorial-family-of-types-is-locally-smallᵉ Hᵉ)
```