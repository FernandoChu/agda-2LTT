# Transitive concrete group actions

```agda
module group-theory.transitive-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-concrete-group-actionsᵉ

open import higher-group-theory.transitive-higher-group-actionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`ᵉ andᵉ aᵉ
[concreteᵉ groupᵉ action](group-theory.concrete-group-actions.mdᵉ) ofᵉ `G`ᵉ onᵉ `X`.ᵉ
Weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ **transitive**ᵉ ifᵉ itsᵉ typeᵉ ofᵉ
[orbits](group-theory.orbits-concrete-group-actions.mdᵉ) isᵉ
[connected](foundation.connected-types.md).ᵉ

[Equivalently](foundation.logical-equivalences.md),ᵉ weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ
**abstractlyᵉ transitive**ᵉ ifᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `X`ᵉ isᵉ
[inhabited](foundation.inhabited-types.mdᵉ) andᵉ forᵉ anyᵉ elementᵉ `xᵉ : Xᵉ (shᵉ G)`ᵉ ofᵉ
theᵉ underlyingᵉ typeᵉ ofᵉ `X`ᵉ theᵉ actionᵉ mapᵉ

```text
  gᵉ ↦ᵉ mul-action-Concrete-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ
```

isᵉ [surjective](foundation.surjective-maps.md).ᵉ

Noteᵉ thatᵉ itᵉ isᵉ necessaryᵉ to includeᵉ theᵉ conditionᵉ thatᵉ `X`ᵉ isᵉ inhabitedᵉ in theᵉ
conditionᵉ thatᵉ `G`ᵉ actsᵉ transitivelyᵉ onᵉ `X`.ᵉ Aᵉ firstᵉ reasonᵉ isᵉ thatᵉ thisᵉ makesᵉ
theᵉ conditionᵉ ofᵉ beingᵉ abstractlyᵉ transitiveᵉ equivalentᵉ to theᵉ conditionᵉ ofᵉ
beingᵉ transitive.ᵉ Aᵉ secondᵉ reasonᵉ isᵉ thatᵉ thisᵉ wayᵉ weᵉ willᵉ beᵉ ableᵉ to recoverᵉ
theᵉ familiarᵉ propertyᵉ thatᵉ aᵉ `G`-actionᵉ `X`ᵉ isᵉ aᵉ `G`-torsorᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ
bothᵉ [free](group-theory.free-concrete-group-actions.mdᵉ) andᵉ transitive.ᵉ

## Definition

### The predicate of being a transitive concrete group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  is-transitive-prop-action-Concrete-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-prop-action-Concrete-Groupᵉ =
    is-transitive-prop-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-transitive-action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-action-Concrete-Groupᵉ =
    is-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-prop-is-transitive-action-Concrete-Groupᵉ :
    is-propᵉ is-transitive-action-Concrete-Groupᵉ
  is-prop-is-transitive-action-Concrete-Groupᵉ =
    is-prop-is-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)
```

### The predicate of being an abstractly transitive concrete group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  is-abstractly-transitive-prop-action-Concrete-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-transitive-prop-action-Concrete-Groupᵉ =
    is-abstractly-transitive-prop-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-abstractly-transitive-action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-transitive-action-Concrete-Groupᵉ =
    is-abstractly-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-prop-is-abstractly-transitive-action-Concrete-Groupᵉ :
    is-propᵉ is-abstractly-transitive-action-Concrete-Groupᵉ
  is-prop-is-abstractly-transitive-action-Concrete-Groupᵉ =
    is-prop-is-abstractly-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)
```

### Transitive concrete group actions

```agda
transitive-action-Concrete-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ =
  type-subtypeᵉ (is-transitive-prop-action-Concrete-Groupᵉ {l2ᵉ = l2ᵉ} Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Xᵉ : transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  action-transitive-action-Concrete-Groupᵉ :
    action-Concrete-Groupᵉ l2ᵉ Gᵉ
  action-transitive-action-Concrete-Groupᵉ = pr1ᵉ Xᵉ

  is-transitive-transitive-action-Concrete-Groupᵉ :
    is-transitive-action-Concrete-Groupᵉ Gᵉ
      action-transitive-action-Concrete-Groupᵉ
  is-transitive-transitive-action-Concrete-Groupᵉ = pr2ᵉ Xᵉ

  transitive-action-∞-group-transitive-action-Concrete-Groupᵉ :
    transitive-action-∞-Groupᵉ l2ᵉ (∞-group-Concrete-Groupᵉ Gᵉ)
  pr1ᵉ transitive-action-∞-group-transitive-action-Concrete-Groupᵉ =
    type-Setᵉ ∘ᵉ action-transitive-action-Concrete-Groupᵉ
  pr2ᵉ transitive-action-∞-group-transitive-action-Concrete-Groupᵉ =
    is-transitive-transitive-action-Concrete-Groupᵉ

  set-transitive-action-Concrete-Groupᵉ : Setᵉ l2ᵉ
  set-transitive-action-Concrete-Groupᵉ =
    set-action-Concrete-Groupᵉ Gᵉ action-transitive-action-Concrete-Groupᵉ

  type-transitive-action-Concrete-Groupᵉ : UUᵉ l2ᵉ
  type-transitive-action-Concrete-Groupᵉ =
    type-action-Concrete-Groupᵉ Gᵉ action-transitive-action-Concrete-Groupᵉ

  is-set-type-transitive-action-Concrete-Groupᵉ :
    is-setᵉ type-transitive-action-Concrete-Groupᵉ
  is-set-type-transitive-action-Concrete-Groupᵉ =
    is-set-type-action-Concrete-Groupᵉ Gᵉ action-transitive-action-Concrete-Groupᵉ

  is-inhabited-type-transitive-action-Concrete-Groupᵉ :
    is-inhabitedᵉ type-transitive-action-Concrete-Groupᵉ
  is-inhabited-type-transitive-action-Concrete-Groupᵉ =
    is-inhabited-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( transitive-action-∞-group-transitive-action-Concrete-Groupᵉ)

  inhabited-type-transitive-action-Concrete-Groupᵉ :
    Inhabited-Typeᵉ l2ᵉ
  inhabited-type-transitive-action-Concrete-Groupᵉ =
    inhabited-type-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( transitive-action-∞-group-transitive-action-Concrete-Groupᵉ)

  mul-transitive-action-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ Gᵉ → type-transitive-action-Concrete-Groupᵉ →
    type-transitive-action-Concrete-Groupᵉ
  mul-transitive-action-Concrete-Groupᵉ =
    mul-action-Concrete-Groupᵉ Gᵉ action-transitive-action-Concrete-Groupᵉ

  is-abstractly-transitive-transitive-action-Concrete-Groupᵉ :
    is-abstractly-transitive-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ)
  is-abstractly-transitive-transitive-action-Concrete-Groupᵉ =
    is-abstractly-transitive-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( transitive-action-∞-group-transitive-action-Concrete-Groupᵉ)

  is-surjective-mul-right-transitive-action-Concrete-Groupᵉ :
    (xᵉ : type-transitive-action-Concrete-Groupᵉ) →
    is-surjectiveᵉ (λ gᵉ → mul-transitive-action-Concrete-Groupᵉ gᵉ xᵉ)
  is-surjective-mul-right-transitive-action-Concrete-Groupᵉ =
    is-surjective-mul-right-transitive-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( transitive-action-∞-group-transitive-action-Concrete-Groupᵉ)
```

## Properties

### Characterization of the identity type of transitive actions of a concrete group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Xᵉ : transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  equiv-transitive-action-Concrete-Groupᵉ :
    {l3ᵉ : Level} (Yᵉ : transitive-action-Concrete-Groupᵉ l3ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-transitive-action-Concrete-Groupᵉ Yᵉ =
    equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)

  map-equiv-transitive-action-Concrete-Groupᵉ :
    {l3ᵉ : Level} (Yᵉ : transitive-action-Concrete-Groupᵉ l3ᵉ Gᵉ) →
    equiv-transitive-action-Concrete-Groupᵉ Yᵉ →
    type-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ →
    type-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ
  map-equiv-transitive-action-Concrete-Groupᵉ Yᵉ =
    map-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)

  preserves-mul-equiv-transitive-action-Concrete-Groupᵉ :
    {l3ᵉ : Level} (Yᵉ : transitive-action-Concrete-Groupᵉ l3ᵉ Gᵉ) →
    (eᵉ : equiv-transitive-action-Concrete-Groupᵉ Yᵉ) (gᵉ : type-Concrete-Groupᵉ Gᵉ)
    (xᵉ : type-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    ( map-equiv-transitive-action-Concrete-Groupᵉ Yᵉ eᵉ
      ( mul-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ)) ＝ᵉ
    ( mul-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ gᵉ
      ( map-equiv-transitive-action-Concrete-Groupᵉ Yᵉ eᵉ xᵉ))
  preserves-mul-equiv-transitive-action-Concrete-Groupᵉ Yᵉ =
    preserves-mul-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)

  id-equiv-transitive-action-Concrete-Groupᵉ :
    equiv-transitive-action-Concrete-Groupᵉ Xᵉ
  id-equiv-transitive-action-Concrete-Groupᵉ =
    id-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)

  extensionality-transitive-action-Concrete-Groupᵉ :
    (Yᵉ : transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-transitive-action-Concrete-Groupᵉ Yᵉ
  extensionality-transitive-action-Concrete-Groupᵉ Yᵉ =
    ( extensionality-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)) ∘eᵉ
    ( extensionality-type-subtype'ᵉ
      ( is-transitive-prop-action-Concrete-Groupᵉ Gᵉ)
      ( Xᵉ)
      ( Yᵉ))
```

### Two equivalences of transitive concrete group actions are homotopic if there exists a point on which they have the same value

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Xᵉ : transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : transitive-action-Concrete-Groupᵉ l3ᵉ Gᵉ)
  (eᵉ fᵉ : equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-equiv-transitive-action-Concrete-Groupᵉ : UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-equiv-transitive-action-Concrete-Groupᵉ =
    htpy-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)
      ( fᵉ)

  htpy-prop-equiv-transitive-action-Concrete-Groupᵉ : Propᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-prop-equiv-transitive-action-Concrete-Groupᵉ =
    htpy-prop-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)
      ( fᵉ)

  htpy-exists-equiv-transitive-action-Concrete-Groupᵉ :
    exists-structureᵉ
      ( type-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( λ xᵉ →
        map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ xᵉ ＝ᵉ
        map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ xᵉ) →
    htpy-equiv-transitive-action-Concrete-Groupᵉ
  htpy-exists-equiv-transitive-action-Concrete-Groupᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( htpy-prop-equiv-transitive-action-Concrete-Groupᵉ)
      ( λ (xᵉ ,ᵉ pᵉ) yᵉ →
        apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ
            ( is-abstractly-transitive-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ)
            ( xᵉ)
            ( yᵉ))
          ( Id-Propᵉ
            ( set-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ)
            ( map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ yᵉ)
            ( map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ yᵉ))
          ( λ (gᵉ ,ᵉ qᵉ) →
            ( apᵉ (map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ) (invᵉ qᵉ)) ∙ᵉ
            ( preserves-mul-equiv-transitive-action-Concrete-Groupᵉ
              Gᵉ Xᵉ Yᵉ eᵉ gᵉ xᵉ) ∙ᵉ
            ( apᵉ
              ( mul-transitive-action-Concrete-Groupᵉ Gᵉ Yᵉ gᵉ)
              ( pᵉ)) ∙ᵉ
            ( invᵉ
              ( preserves-mul-equiv-transitive-action-Concrete-Groupᵉ
                Gᵉ Xᵉ Yᵉ fᵉ gᵉ xᵉ)) ∙ᵉ
            ( apᵉ (map-equiv-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ) qᵉ)))
```

### The type of transitive concrete group actions is a 1-type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  where

  is-1-type-transitive-action-Concrete-Groupᵉ :
    is-1-typeᵉ (transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  is-1-type-transitive-action-Concrete-Groupᵉ =
    is-1-type-type-subtypeᵉ
      ( is-transitive-prop-action-Concrete-Groupᵉ Gᵉ)
      ( is-1-type-action-Concrete-Groupᵉ Gᵉ)

  transitive-action-1-type-Concrete-Groupᵉ : 1-Typeᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ transitive-action-1-type-Concrete-Groupᵉ =
    transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ
  pr2ᵉ transitive-action-1-type-Concrete-Groupᵉ =
    is-1-type-transitive-action-Concrete-Groupᵉ
```