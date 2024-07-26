# The universal property of identity systems

```agda
module foundation.universal-property-identity-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-systemsᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ **(unaryᵉ) identityᵉ system**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ pointᵉ `aᵉ : A`ᵉ
consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ equippedᵉ with aᵉ pointᵉ `bᵉ : Bᵉ a`ᵉ thatᵉ
satisfiesᵉ anᵉ inductionᵉ principleᵉ analogousᵉ to theᵉ inductionᵉ principleᵉ ofᵉ theᵉ
[identityᵉ type](foundation.identity-types.mdᵉ) atᵉ `a`.ᵉ Theᵉ
[dependentᵉ universalᵉ propertyᵉ ofᵉ identityᵉ types](foundation.universal-property-identity-types.mdᵉ)
alsoᵉ followsᵉ forᵉ identityᵉ systems.ᵉ

## Definition

### The universal property of identity systems

```agda
dependent-universal-property-identity-systemᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) {aᵉ : Aᵉ} (bᵉ : Bᵉ aᵉ) → UUωᵉ
dependent-universal-property-identity-systemᵉ {Aᵉ = Aᵉ} Bᵉ bᵉ =
  {l3ᵉ : Level} (Pᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l3ᵉ) →
  is-equivᵉ (ev-refl-identity-systemᵉ bᵉ {Pᵉ})
```

## Properties

### A type family satisfies the dependent universal property of identity systems if and only if it is torsorial

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ : Aᵉ} (bᵉ : Bᵉ aᵉ)
  where

  dependent-universal-property-identity-system-is-torsorialᵉ :
    is-torsorialᵉ Bᵉ →
    dependent-universal-property-identity-systemᵉ Bᵉ bᵉ
  dependent-universal-property-identity-system-is-torsorialᵉ
    Hᵉ Pᵉ =
    is-equiv-left-factorᵉ
      ( ev-refl-identity-systemᵉ bᵉ)
      ( ev-pairᵉ)
      ( dependent-universal-property-contr-is-contrᵉ
        ( aᵉ ,ᵉ bᵉ)
        ( Hᵉ)
        ( λ uᵉ → Pᵉ (pr1ᵉ uᵉ) (pr2ᵉ uᵉ)))
      ( is-equiv-ev-pairᵉ)

  equiv-dependent-universal-property-identity-system-is-torsorialᵉ :
    is-torsorialᵉ Bᵉ →
    {lᵉ : Level} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ lᵉ} →
    ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) ≃ᵉ Cᵉ aᵉ bᵉ
  pr1ᵉ (equiv-dependent-universal-property-identity-system-is-torsorialᵉ Hᵉ) =
    ev-refl-identity-systemᵉ bᵉ
  pr2ᵉ (equiv-dependent-universal-property-identity-system-is-torsorialᵉ Hᵉ) =
    dependent-universal-property-identity-system-is-torsorialᵉ Hᵉ _

  is-torsorial-dependent-universal-property-identity-systemᵉ :
    dependent-universal-property-identity-systemᵉ Bᵉ bᵉ →
    is-torsorialᵉ Bᵉ
  pr1ᵉ (is-torsorial-dependent-universal-property-identity-systemᵉ Hᵉ) = (aᵉ ,ᵉ bᵉ)
  pr2ᵉ (is-torsorial-dependent-universal-property-identity-systemᵉ Hᵉ) uᵉ =
    map-inv-is-equivᵉ
      ( Hᵉ (λ xᵉ yᵉ → (aᵉ ,ᵉ bᵉ) ＝ᵉ (xᵉ ,ᵉ yᵉ)))
      ( reflᵉ)
      ( pr1ᵉ uᵉ)
      ( pr2ᵉ uᵉ)
```

### A type family satisfies the dependent universal property of identity systems if and only if it is an identity system

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ : Aᵉ} (bᵉ : Bᵉ aᵉ)
  where

  dependent-universal-property-identity-system-is-identity-systemᵉ :
    is-identity-systemᵉ Bᵉ aᵉ bᵉ →
    dependent-universal-property-identity-systemᵉ Bᵉ bᵉ
  dependent-universal-property-identity-system-is-identity-systemᵉ Hᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ bᵉ
      ( is-torsorial-is-identity-systemᵉ aᵉ bᵉ Hᵉ)

  is-identity-system-dependent-universal-property-identity-systemᵉ :
    dependent-universal-property-identity-systemᵉ Bᵉ bᵉ →
    is-identity-systemᵉ Bᵉ aᵉ bᵉ
  is-identity-system-dependent-universal-property-identity-systemᵉ Hᵉ Pᵉ =
    section-is-equivᵉ (Hᵉ Pᵉ)
```