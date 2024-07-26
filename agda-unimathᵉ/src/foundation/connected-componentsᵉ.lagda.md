# Connected components of types

```agda
module foundation.connected-componentsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ **connectedᵉ component**ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ atᵉ anᵉ elementᵉ `aᵉ : A`ᵉ isᵉ theᵉ typeᵉ ofᵉ
allᵉ `xᵉ : A`ᵉ thatᵉ areᵉ [merelyᵉ equal](foundation.mere-equality.mdᵉ) to `a`.ᵉ

Theᵉ [subtype](foundation-core.subtypes.mdᵉ) ofᵉ elementsᵉ merelyᵉ equalᵉ to `a`ᵉ isᵉ
alsoᵉ theᵉ leastᵉ subtypeᵉ ofᵉ `A`ᵉ containingᵉ `a`.ᵉ Inᵉ otherᵉ words,ᵉ ifᵉ aᵉ subtypeᵉ
satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ beingᵉ theᵉ leastᵉ subtypeᵉ ofᵉ `A`ᵉ containingᵉ
`a`,ᵉ thenᵉ itsᵉ underlyingᵉ typeᵉ isᵉ theᵉ connectedᵉ componentᵉ ofᵉ `A`ᵉ atᵉ `a`.ᵉ

## Definitions

### The predicate of being the least subtype containing a given element

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ : Xᵉ) (Pᵉ : subtypeᵉ l2ᵉ Xᵉ)
  where

  is-least-subtype-containing-elementᵉ : UUωᵉ
  is-least-subtype-containing-elementᵉ =
    {lᵉ : Level} (Qᵉ : subtypeᵉ lᵉ Xᵉ) → (Pᵉ ⊆ᵉ Qᵉ) ↔ᵉ is-in-subtypeᵉ Qᵉ xᵉ
```

### Connected components of types

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) (aᵉ : Aᵉ)
  where

  connected-componentᵉ : UUᵉ lᵉ
  connected-componentᵉ =
    Σᵉ Aᵉ (λ xᵉ → type-trunc-Propᵉ (xᵉ ＝ᵉ aᵉ))

  point-connected-componentᵉ : connected-componentᵉ
  pr1ᵉ point-connected-componentᵉ = aᵉ
  pr2ᵉ point-connected-componentᵉ = unit-trunc-Propᵉ reflᵉ

  connected-component-Pointed-Typeᵉ : Pointed-Typeᵉ lᵉ
  pr1ᵉ connected-component-Pointed-Typeᵉ = connected-componentᵉ
  pr2ᵉ connected-component-Pointed-Typeᵉ = point-connected-componentᵉ

  value-connected-componentᵉ :
    connected-componentᵉ → Aᵉ
  value-connected-componentᵉ Xᵉ = pr1ᵉ Xᵉ

  abstract
    mere-equality-connected-componentᵉ :
      (Xᵉ : connected-componentᵉ) →
      type-trunc-Propᵉ (value-connected-componentᵉ Xᵉ ＝ᵉ aᵉ)
    mere-equality-connected-componentᵉ Xᵉ = pr2ᵉ Xᵉ
```

## Properties

### Connected components are 0-connected

```agda
abstract
  is-0-connected-connected-componentᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) (aᵉ : Aᵉ) →
    is-0-connectedᵉ (connected-componentᵉ Aᵉ aᵉ)
  is-0-connected-connected-componentᵉ Aᵉ aᵉ =
    is-0-connected-mere-eqᵉ
      ( aᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ)
      ( λ (xᵉ ,ᵉ pᵉ) →
        apply-universal-property-trunc-Propᵉ
          ( pᵉ)
          ( trunc-Propᵉ ((aᵉ ,ᵉ unit-trunc-Propᵉ reflᵉ) ＝ᵉ (xᵉ ,ᵉ pᵉ)))
          ( λ p'ᵉ →
            unit-trunc-Propᵉ
              ( eq-pair-Σᵉ
                ( invᵉ p'ᵉ)
                ( all-elements-equal-type-trunc-Propᵉ _ pᵉ))))

connected-component-∞-Groupᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) (aᵉ : Aᵉ) → ∞-Groupᵉ lᵉ
pr1ᵉ (connected-component-∞-Groupᵉ Aᵉ aᵉ) = connected-component-Pointed-Typeᵉ Aᵉ aᵉ
pr2ᵉ (connected-component-∞-Groupᵉ Aᵉ aᵉ) = is-0-connected-connected-componentᵉ Aᵉ aᵉ
```

### If `A` is `k+1`-truncated, then the connected component of `a` in `A` is `k+1`-truncated

```agda
is-trunc-connected-componentᵉ :
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ lᵉ) (aᵉ : Aᵉ) →
  is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-truncᵉ (succ-𝕋ᵉ kᵉ) (connected-componentᵉ Aᵉ aᵉ)
is-trunc-connected-componentᵉ {lᵉ} {kᵉ} Aᵉ aᵉ Hᵉ =
  is-trunc-Σᵉ Hᵉ (λ xᵉ → is-trunc-is-propᵉ kᵉ is-prop-type-trunc-Propᵉ)
```