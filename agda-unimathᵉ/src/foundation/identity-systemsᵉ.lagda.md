# Identity systems

```agda
module foundation.identity-systemsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Aᵉ **(unaryᵉ) identityᵉ system**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ pointᵉ `aᵉ : A`ᵉ
consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ equippedᵉ with aᵉ pointᵉ `bᵉ : Bᵉ a`ᵉ thatᵉ
satisfiesᵉ anᵉ inductionᵉ principleᵉ analogousᵉ to theᵉ inductionᵉ principleᵉ ofᵉ theᵉ
[identityᵉ type](foundation.identity-types.mdᵉ) atᵉ `a`.ᵉ Theᵉ
[dependentᵉ universalᵉ propertyᵉ ofᵉ identityᵉ types](foundation.universal-property-identity-types.mdᵉ)
alsoᵉ followsᵉ forᵉ identityᵉ systems.ᵉ

## Definitions

### Evaluating at the base point

```agda
ev-refl-identity-systemᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ : Aᵉ} (bᵉ : Bᵉ aᵉ)
  {Pᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l3ᵉ} →
  ((xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Pᵉ xᵉ yᵉ) → Pᵉ aᵉ bᵉ
ev-refl-identity-systemᵉ {aᵉ = aᵉ} bᵉ fᵉ = fᵉ aᵉ bᵉ
```

### The predicate of being an identity system with respect to a universe level

```agda
module _
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ)
  where

  is-identity-system-Levelᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
  is-identity-system-Levelᵉ =
    (Pᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ lᵉ) → sectionᵉ (ev-refl-identity-systemᵉ bᵉ {Pᵉ})
```

### The predicate of being an identity system

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ)
  where

  is-identity-systemᵉ : UUωᵉ
  is-identity-systemᵉ = {lᵉ : Level} → is-identity-system-Levelᵉ lᵉ Bᵉ aᵉ bᵉ
```

## Properties

### A type family over `A` is an identity system if and only if its total space is contractible

Inᵉ [`foundation.torsorial-type-families`](foundation.torsorial-type-families.mdᵉ)
weᵉ willᵉ startᵉ callingᵉ typeᵉ familiesᵉ with contractibleᵉ totalᵉ spaceᵉ torsorial.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ)
  where

  map-section-is-identity-system-is-torsorialᵉ :
    is-torsorialᵉ Bᵉ →
    {l3ᵉ : Level} (Pᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l3ᵉ) →
    Pᵉ aᵉ bᵉ → (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Pᵉ xᵉ yᵉ
  map-section-is-identity-system-is-torsorialᵉ Hᵉ Pᵉ pᵉ xᵉ yᵉ =
    trᵉ (fam-Σᵉ Pᵉ) (eq-is-contrᵉ Hᵉ) pᵉ

  is-section-map-section-is-identity-system-is-torsorialᵉ :
    (Hᵉ : is-torsorialᵉ Bᵉ) →
    {l3ᵉ : Level} (Pᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → UUᵉ l3ᵉ) →
    is-sectionᵉ
      ( ev-refl-identity-systemᵉ bᵉ)
      ( map-section-is-identity-system-is-torsorialᵉ Hᵉ Pᵉ)
  is-section-map-section-is-identity-system-is-torsorialᵉ Hᵉ Pᵉ pᵉ =
    apᵉ
      ( λ tᵉ → trᵉ (fam-Σᵉ Pᵉ) tᵉ pᵉ)
      ( eq-is-contr'ᵉ
        ( is-prop-is-contrᵉ Hᵉ (aᵉ ,ᵉ bᵉ) (aᵉ ,ᵉ bᵉ))
        ( eq-is-contrᵉ Hᵉ)
        ( reflᵉ))

  abstract
    is-identity-system-is-torsorialᵉ :
      is-torsorialᵉ Bᵉ → is-identity-systemᵉ Bᵉ aᵉ bᵉ
    is-identity-system-is-torsorialᵉ Hᵉ Pᵉ =
      ( map-section-is-identity-system-is-torsorialᵉ Hᵉ Pᵉ ,ᵉ
        is-section-map-section-is-identity-system-is-torsorialᵉ Hᵉ Pᵉ)

  abstract
    is-torsorial-is-identity-systemᵉ :
      is-identity-systemᵉ Bᵉ aᵉ bᵉ → is-torsorialᵉ Bᵉ
    pr1ᵉ (is-torsorial-is-identity-systemᵉ Hᵉ) = (aᵉ ,ᵉ bᵉ)
    pr2ᵉ (is-torsorial-is-identity-systemᵉ Hᵉ) (xᵉ ,ᵉ yᵉ) =
      pr1ᵉ (Hᵉ (λ x'ᵉ y'ᵉ → (aᵉ ,ᵉ bᵉ) ＝ᵉ (x'ᵉ ,ᵉ y'ᵉ))) reflᵉ xᵉ yᵉ

  abstract
    fundamental-theorem-id-is-identity-systemᵉ :
      is-identity-systemᵉ Bᵉ aᵉ bᵉ →
      (fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Bᵉ xᵉ) → is-fiberwise-equivᵉ fᵉ
    fundamental-theorem-id-is-identity-systemᵉ Hᵉ =
      fundamental-theorem-idᵉ (is-torsorial-is-identity-systemᵉ Hᵉ)
```

## External links

-ᵉ [Identityᵉ systems](https://1lab.dev/1Lab.Path.IdentitySystem.htmlᵉ) atᵉ 1labᵉ
-ᵉ [identityᵉ system](https://ncatlab.org/nlab/show/identity+systemᵉ) atᵉ $n$Labᵉ