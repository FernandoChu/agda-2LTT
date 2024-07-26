# Quotient groups of concrete groups

```agda
module group-theory.quotient-groups-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.0-images-of-mapsᵉ
open import foundation.1-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-concrete-group-actionsᵉ
open import group-theory.mere-equivalences-concrete-group-actionsᵉ
open import group-theory.normal-subgroups-concrete-groupsᵉ
open import group-theory.transitive-concrete-group-actionsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Givenᵉ aᵉ normalᵉ subgroupᵉ `N`ᵉ ofᵉ aᵉ concreteᵉ groupᵉ `G`,ᵉ theᵉ quotientᵉ groupᵉ `G/N`ᵉ isᵉ
aᵉ concreteᵉ groupᵉ thatᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ thatᵉ forᵉ anyᵉ concreteᵉ
groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ suchᵉ thatᵉ theᵉ kernelᵉ ofᵉ `f`ᵉ isᵉ containedᵉ in `N`,ᵉ
thenᵉ `f`ᵉ extendsᵉ uniquelyᵉ to aᵉ groupᵉ homomorphismᵉ `G/Nᵉ → H`.ᵉ

Theᵉ quotientᵉ `G/N`ᵉ canᵉ beᵉ constructedᵉ in severalᵉ ways.ᵉ

1.ᵉ Weᵉ canᵉ constructᵉ `G/N`ᵉ asᵉ theᵉ typeᵉ ofᵉ `G`-setsᵉ merelyᵉ equivalentᵉ to theᵉ cosetᵉ
   actionᵉ ofᵉ `N`.ᵉ Sinceᵉ thisᵉ constructionᵉ isᵉ reminiscentᵉ ofᵉ theᵉ torsorᵉ
   constructionᵉ ofᵉ BG,ᵉ weᵉ callᵉ thisᵉ theᵉ **standardᵉ construction**ᵉ ofᵉ `G/N`.ᵉ
2.ᵉ Weᵉ canᵉ constructᵉ `G/N`ᵉ asᵉ theᵉ 0-imageᵉ ofᵉ theᵉ cosetᵉ actionᵉ `Nᵉ : BGᵉ → U`.ᵉ Weᵉ
   callᵉ thisᵉ theᵉ **0-imageᵉ construction**ᵉ ofᵉ `G/N`.ᵉ

## Definitions

### The standard construction of `G/N`

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  ( Nᵉ : normal-subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  classifying-type-quotient-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  classifying-type-quotient-Concrete-Groupᵉ =
    Σᵉ ( transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
      ( λ Xᵉ →
        mere-equiv-action-Concrete-Groupᵉ Gᵉ
        ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
        ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ))

  shape-quotient-Concrete-Groupᵉ :
    classifying-type-quotient-Concrete-Groupᵉ
  pr1ᵉ shape-quotient-Concrete-Groupᵉ =
    transitive-action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ
  pr2ᵉ shape-quotient-Concrete-Groupᵉ =
    refl-mere-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)

  classifying-pointed-type-quotient-Concrete-Groupᵉ :
    Pointed-Typeᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ classifying-pointed-type-quotient-Concrete-Groupᵉ =
    classifying-type-quotient-Concrete-Groupᵉ
  pr2ᵉ classifying-pointed-type-quotient-Concrete-Groupᵉ =
    shape-quotient-Concrete-Groupᵉ

  type-quotient-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  type-quotient-Concrete-Groupᵉ =
    type-Ωᵉ classifying-pointed-type-quotient-Concrete-Groupᵉ

  extensionality-classifying-type-quotient-Concrete-Groupᵉ :
    (uᵉ vᵉ : classifying-type-quotient-Concrete-Groupᵉ) →
    (uᵉ ＝ᵉ vᵉ) ≃ᵉ equiv-transitive-action-Concrete-Groupᵉ Gᵉ (pr1ᵉ uᵉ) (pr1ᵉ vᵉ)
  extensionality-classifying-type-quotient-Concrete-Groupᵉ uᵉ =
    extensionality-type-subtypeᵉ
      ( λ (Xᵉ : transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ) →
        mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ
          ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
          ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ))
      ( pr2ᵉ uᵉ)
      ( id-equiv-transitive-action-Concrete-Groupᵉ Gᵉ
        ( pr1ᵉ uᵉ))
      ( extensionality-transitive-action-Concrete-Groupᵉ Gᵉ (pr1ᵉ uᵉ))

  is-0-connected-classifying-type-quotient-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-quotient-Concrete-Groupᵉ
  is-0-connected-classifying-type-quotient-Concrete-Groupᵉ =
    is-0-connected-mere-eqᵉ
      ( shape-quotient-Concrete-Groupᵉ)
      ( λ (pairᵉ uᵉ pᵉ) →
        apply-universal-property-trunc-Propᵉ pᵉ
          ( mere-eq-Propᵉ
            ( shape-quotient-Concrete-Groupᵉ)
            ( pairᵉ uᵉ pᵉ))
          ( λ eᵉ →
            unit-trunc-Propᵉ
              ( eq-type-subtypeᵉ
                ( λ Xᵉ →
                  mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ
                    ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
                    ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ))
                ( eq-type-subtypeᵉ
                  ( is-transitive-prop-action-Concrete-Groupᵉ Gᵉ)
                  ( eq-equiv-action-Concrete-Groupᵉ Gᵉ
                    ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
                    ( pr1ᵉ uᵉ)
                    ( eᵉ))))))

  is-1-type-classifying-type-quotient-Concrete-Groupᵉ :
    is-1-typeᵉ classifying-type-quotient-Concrete-Groupᵉ
  is-1-type-classifying-type-quotient-Concrete-Groupᵉ =
    is-1-type-type-subtypeᵉ
      ( λ Xᵉ →
        mere-equiv-prop-action-Concrete-Groupᵉ Gᵉ
          ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
          ( action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ))
      ( is-1-type-transitive-action-Concrete-Groupᵉ Gᵉ)

  is-set-type-quotient-Concrete-Groupᵉ :
    is-setᵉ type-quotient-Concrete-Groupᵉ
  is-set-type-quotient-Concrete-Groupᵉ =
    is-1-type-classifying-type-quotient-Concrete-Groupᵉ
      shape-quotient-Concrete-Groupᵉ
      shape-quotient-Concrete-Groupᵉ

  ∞-group-quotient-Concrete-Groupᵉ : ∞-Groupᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ ∞-group-quotient-Concrete-Groupᵉ =
    classifying-pointed-type-quotient-Concrete-Groupᵉ
  pr2ᵉ ∞-group-quotient-Concrete-Groupᵉ =
    is-0-connected-classifying-type-quotient-Concrete-Groupᵉ

  concrete-group-quotient-Concrete-Groupᵉ :
    Concrete-Groupᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ concrete-group-quotient-Concrete-Groupᵉ =
    ∞-group-quotient-Concrete-Groupᵉ
  pr2ᵉ concrete-group-quotient-Concrete-Groupᵉ =
    is-set-type-quotient-Concrete-Groupᵉ
```

### The 0-image construction of `G/N`

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  ( Nᵉ : normal-subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  classifying-type-0-image-quotient-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  classifying-type-0-image-quotient-Concrete-Groupᵉ =
    0-imᵉ (action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)

  shape-0-image-quotient-Concrete-Groupᵉ :
    classifying-type-0-image-quotient-Concrete-Groupᵉ
  shape-0-image-quotient-Concrete-Groupᵉ =
    unit-0-imᵉ
      ( action-normal-subgroup-Concrete-Groupᵉ Gᵉ Nᵉ)
      ( shape-Concrete-Groupᵉ Gᵉ)

  classifying-pointed-type-0-image-quotient-Concrete-Groupᵉ :
    Pointed-Typeᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ classifying-pointed-type-0-image-quotient-Concrete-Groupᵉ =
    classifying-type-0-image-quotient-Concrete-Groupᵉ
  pr2ᵉ classifying-pointed-type-0-image-quotient-Concrete-Groupᵉ =
    shape-0-image-quotient-Concrete-Groupᵉ

  type-0-image-quotient-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  type-0-image-quotient-Concrete-Groupᵉ =
    type-Ωᵉ classifying-pointed-type-0-image-quotient-Concrete-Groupᵉ
```