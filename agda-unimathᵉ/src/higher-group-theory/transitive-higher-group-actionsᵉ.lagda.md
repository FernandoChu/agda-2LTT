# Transitive higher group actions

```agda
module higher-group-theory.transitive-higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.regensburg-extension-fundamental-theorem-of-identity-typesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.orbits-higher-group-actionsᵉ
```

</details>

## Idea

Considerᵉ anᵉ [∞-group](higher-group-theory.higher-groups.mdᵉ) `G`ᵉ andᵉ anᵉ
[∞-groupᵉ action](higher-group-theory.higher-group-actions.mdᵉ) ofᵉ `G`ᵉ onᵉ `X`.ᵉ Weᵉ
sayᵉ thatᵉ `X`ᵉ isᵉ **transitive**ᵉ ifᵉ itsᵉ typeᵉ ofᵉ
[orbits](higher-group-theory.orbits-higher-group-actions.mdᵉ) isᵉ
[connected](foundation.connected-types.md).ᵉ

[Equivalently](foundation.logical-equivalences.md),ᵉ weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ
**abstractlyᵉ transitive**ᵉ ifᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `X`ᵉ isᵉ
[inhabited](foundation.inhabited-types.mdᵉ) andᵉ forᵉ anyᵉ elementᵉ `xᵉ : Xᵉ (shᵉ G)`ᵉ ofᵉ
theᵉ underlyingᵉ typeᵉ ofᵉ `X`ᵉ theᵉ actionᵉ mapᵉ

```text
  gᵉ ↦ᵉ mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ
```

isᵉ [surjective](foundation.surjective-maps.md).ᵉ Theᵉ equivalenceᵉ ofᵉ theseᵉ twoᵉ
conditionsᵉ isᵉ establishedᵉ viaᵉ theᵉ
[Regensburgᵉ extensionᵉ ofᵉ theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.regensburg-extension-fundamental-theorem-of-identity-types.md).ᵉ

Noteᵉ thatᵉ itᵉ isᵉ necessaryᵉ to includeᵉ theᵉ conditionᵉ thatᵉ `X`ᵉ isᵉ inhabitedᵉ in theᵉ
conditionᵉ thatᵉ `G`ᵉ actsᵉ transitivelyᵉ onᵉ `X`.ᵉ Aᵉ firstᵉ reasonᵉ isᵉ thatᵉ thisᵉ makesᵉ
theᵉ conditionᵉ ofᵉ beingᵉ abstractlyᵉ transitiveᵉ equivalentᵉ to theᵉ conditionᵉ ofᵉ
beingᵉ transitive.ᵉ Aᵉ secondᵉ reasonᵉ isᵉ thatᵉ thisᵉ wayᵉ weᵉ willᵉ beᵉ ableᵉ to recoverᵉ
theᵉ familiarᵉ propertyᵉ thatᵉ aᵉ `G`-actionᵉ `X`ᵉ isᵉ aᵉ `G`-torsorᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ
bothᵉ [free](higher-group-theory.free-higher-group-actions.mdᵉ) andᵉ transitive.ᵉ

## Definitions

### The predicate of being a transitive higher group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-transitive-prop-action-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-prop-action-∞-Groupᵉ =
    is-0-connected-Propᵉ (orbit-action-∞-Groupᵉ Gᵉ Xᵉ)

  is-transitive-action-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-action-∞-Groupᵉ = type-Propᵉ is-transitive-prop-action-∞-Groupᵉ

  is-prop-is-transitive-action-∞-Groupᵉ : is-propᵉ is-transitive-action-∞-Groupᵉ
  is-prop-is-transitive-action-∞-Groupᵉ =
    is-prop-type-Propᵉ is-transitive-prop-action-∞-Groupᵉ
```

### The predicate of being an abstractly transitive higher group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-abstractly-transitive-prop-action-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-transitive-prop-action-∞-Groupᵉ =
    product-Propᵉ
      ( is-inhabited-Propᵉ (type-action-∞-Groupᵉ Gᵉ Xᵉ))
      ( Π-Propᵉ
        ( type-action-∞-Groupᵉ Gᵉ Xᵉ)
        ( λ xᵉ → is-surjective-Propᵉ (λ gᵉ → mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)))

  is-abstractly-transitive-action-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-transitive-action-∞-Groupᵉ =
    type-Propᵉ is-abstractly-transitive-prop-action-∞-Groupᵉ

  is-prop-is-abstractly-transitive-action-∞-Groupᵉ :
    is-propᵉ is-abstractly-transitive-action-∞-Groupᵉ
  is-prop-is-abstractly-transitive-action-∞-Groupᵉ =
    is-prop-type-Propᵉ is-abstractly-transitive-prop-action-∞-Groupᵉ
```

### Transitive higher group actions

```agda
transitive-action-∞-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
transitive-action-∞-Groupᵉ l2ᵉ Gᵉ =
  Σᵉ (action-∞-Groupᵉ l2ᵉ Gᵉ) (is-transitive-action-∞-Groupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : transitive-action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  action-transitive-action-∞-Groupᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ
  action-transitive-action-∞-Groupᵉ = pr1ᵉ Xᵉ

  is-transitive-transitive-action-∞-Groupᵉ :
    is-transitive-action-∞-Groupᵉ Gᵉ action-transitive-action-∞-Groupᵉ
  is-transitive-transitive-action-∞-Groupᵉ = pr2ᵉ Xᵉ

  type-transitive-action-∞-Groupᵉ : UUᵉ l2ᵉ
  type-transitive-action-∞-Groupᵉ =
    type-action-∞-Groupᵉ Gᵉ action-transitive-action-∞-Groupᵉ

  mul-transitive-action-∞-Groupᵉ :
    type-∞-Groupᵉ Gᵉ →
    type-transitive-action-∞-Groupᵉ → type-transitive-action-∞-Groupᵉ
  mul-transitive-action-∞-Groupᵉ =
    mul-action-∞-Groupᵉ Gᵉ action-transitive-action-∞-Groupᵉ

  associative-mul-transitive-action-∞-Groupᵉ :
    (gᵉ hᵉ : type-∞-Groupᵉ Gᵉ) (xᵉ : type-transitive-action-∞-Groupᵉ) →
    mul-transitive-action-∞-Groupᵉ (mul-∞-Groupᵉ Gᵉ gᵉ hᵉ) xᵉ ＝ᵉ
    mul-transitive-action-∞-Groupᵉ hᵉ (mul-transitive-action-∞-Groupᵉ gᵉ xᵉ)
  associative-mul-transitive-action-∞-Groupᵉ =
    associative-mul-action-∞-Groupᵉ Gᵉ action-transitive-action-∞-Groupᵉ

  unit-law-mul-transitive-action-∞-Groupᵉ :
    (xᵉ : type-transitive-action-∞-Groupᵉ) →
    mul-transitive-action-∞-Groupᵉ (unit-∞-Groupᵉ Gᵉ) xᵉ ＝ᵉ xᵉ
  unit-law-mul-transitive-action-∞-Groupᵉ =
    unit-law-mul-action-∞-Groupᵉ Gᵉ action-transitive-action-∞-Groupᵉ
```

## Properties

### If an action is abstractly transitive, then transport is surjective

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  abstract
    is-surjective-tr-is-abstractly-transitive-action-∞-Groupᵉ :
      is-abstractly-transitive-action-∞-Groupᵉ Gᵉ Xᵉ →
      (uᵉ : classifying-type-∞-Groupᵉ Gᵉ)
      (xᵉ : Xᵉ (shape-∞-Groupᵉ Gᵉ)) →
      is-surjectiveᵉ (λ (pᵉ : shape-∞-Groupᵉ Gᵉ ＝ᵉ uᵉ) → trᵉ Xᵉ pᵉ xᵉ)
    is-surjective-tr-is-abstractly-transitive-action-∞-Groupᵉ Hᵉ uᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-∞-Groupᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ) uᵉ)
        ( is-surjective-Propᵉ _)
        ( λ where reflᵉ → pr2ᵉ Hᵉ xᵉ)
```

### An action is transitive if and only if it is abstractly transitive

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-transitive-is-abstractly-transitive-action-∞-Groupᵉ :
    is-abstractly-transitive-action-∞-Groupᵉ Gᵉ Xᵉ →
    is-transitive-action-∞-Groupᵉ Gᵉ Xᵉ
  is-transitive-is-abstractly-transitive-action-∞-Groupᵉ (Hᵉ ,ᵉ Kᵉ) =
    forward-implication-extended-fundamental-theorem-id-surjectiveᵉ
      ( shape-∞-Groupᵉ Gᵉ)
      ( is-0-connected-classifying-type-∞-Groupᵉ Gᵉ)
      ( λ fᵉ uᵉ →
        is-surjective-htpyᵉ
          ( compute-map-out-of-identity-typeᵉ fᵉ uᵉ)
          ( is-surjective-tr-is-abstractly-transitive-action-∞-Groupᵉ Gᵉ Xᵉ
            ( Hᵉ ,ᵉ Kᵉ)
            ( uᵉ)
            ( fᵉ (shape-∞-Groupᵉ Gᵉ) reflᵉ)))
      ( Hᵉ)

  abstract
    is-inhabited-is-transitive-action-∞-Groupᵉ :
      is-transitive-action-∞-Groupᵉ Gᵉ Xᵉ → is-inhabitedᵉ (type-action-∞-Groupᵉ Gᵉ Xᵉ)
    is-inhabited-is-transitive-action-∞-Groupᵉ Hᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-inhabited-is-0-connectedᵉ Hᵉ)
        ( is-inhabited-Propᵉ _)
        ( λ (uᵉ ,ᵉ xᵉ) →
          apply-universal-property-trunc-Propᵉ
            ( mere-eq-classifying-type-∞-Groupᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ) uᵉ)
            ( is-inhabited-Propᵉ _)
            ( λ where reflᵉ → unit-trunc-Propᵉ xᵉ))

  is-surjective-mul-right-is-transitive-action-∞-Groupᵉ :
    is-transitive-action-∞-Groupᵉ Gᵉ Xᵉ →
    (xᵉ : type-action-∞-Groupᵉ Gᵉ Xᵉ) →
    is-surjectiveᵉ (λ gᵉ → mul-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)
  is-surjective-mul-right-is-transitive-action-∞-Groupᵉ Hᵉ xᵉ =
    backward-implication-extended-fundamental-theorem-id-surjectiveᵉ
      ( shape-∞-Groupᵉ Gᵉ)
      ( Hᵉ)
      ( λ uᵉ pᵉ → trᵉ Xᵉ pᵉ xᵉ)
      ( shape-∞-Groupᵉ Gᵉ)

  is-abstractly-transitive-is-transitive-action-∞-Groupᵉ :
    is-transitive-action-∞-Groupᵉ Gᵉ Xᵉ →
    is-abstractly-transitive-action-∞-Groupᵉ Gᵉ Xᵉ
  pr1ᵉ (is-abstractly-transitive-is-transitive-action-∞-Groupᵉ Hᵉ) =
    is-inhabited-is-transitive-action-∞-Groupᵉ Hᵉ
  pr2ᵉ (is-abstractly-transitive-is-transitive-action-∞-Groupᵉ Hᵉ) =
    is-surjective-mul-right-is-transitive-action-∞-Groupᵉ Hᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : transitive-action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  is-inhabited-transitive-action-∞-Groupᵉ :
    is-inhabitedᵉ (type-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)
  is-inhabited-transitive-action-∞-Groupᵉ =
    is-inhabited-is-transitive-action-∞-Groupᵉ Gᵉ
      ( action-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)
      ( is-transitive-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)

  inhabited-type-transitive-action-∞-Groupᵉ :
    Inhabited-Typeᵉ l2ᵉ
  pr1ᵉ inhabited-type-transitive-action-∞-Groupᵉ =
    type-transitive-action-∞-Groupᵉ Gᵉ Xᵉ
  pr2ᵉ inhabited-type-transitive-action-∞-Groupᵉ =
    is-inhabited-transitive-action-∞-Groupᵉ

  is-abstractly-transitive-transitive-action-∞-Groupᵉ :
    is-abstractly-transitive-action-∞-Groupᵉ Gᵉ
      ( action-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)
  is-abstractly-transitive-transitive-action-∞-Groupᵉ =
    is-abstractly-transitive-is-transitive-action-∞-Groupᵉ Gᵉ
      ( action-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)
      ( is-transitive-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)

  is-surjective-tr-transitive-action-∞-Groupᵉ :
    (uᵉ : classifying-type-∞-Groupᵉ Gᵉ) (xᵉ : type-transitive-action-∞-Groupᵉ Gᵉ Xᵉ) →
    is-surjectiveᵉ
      ( λ (pᵉ : shape-∞-Groupᵉ Gᵉ ＝ᵉ uᵉ) →
        trᵉ (action-transitive-action-∞-Groupᵉ Gᵉ Xᵉ) pᵉ xᵉ)
  is-surjective-tr-transitive-action-∞-Groupᵉ =
    is-surjective-tr-is-abstractly-transitive-action-∞-Groupᵉ Gᵉ
      ( action-transitive-action-∞-Groupᵉ Gᵉ Xᵉ)
      ( is-abstractly-transitive-transitive-action-∞-Groupᵉ)

  is-surjective-mul-right-transitive-action-∞-Groupᵉ :
    (xᵉ : type-transitive-action-∞-Groupᵉ Gᵉ Xᵉ) →
    is-surjectiveᵉ (λ gᵉ → mul-transitive-action-∞-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)
  is-surjective-mul-right-transitive-action-∞-Groupᵉ =
    is-surjective-tr-transitive-action-∞-Groupᵉ (shape-∞-Groupᵉ Gᵉ)
```