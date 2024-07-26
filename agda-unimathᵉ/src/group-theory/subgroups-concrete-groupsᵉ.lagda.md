# Subgroups of concrete groups

```agda
module group-theory.subgroups-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.0-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.faithful-mapsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-concrete-group-actionsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
open import group-theory.orbits-concrete-group-actionsᵉ
open import group-theory.transitive-concrete-group-actionsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Aᵉ subgroupᵉ ofᵉ aᵉ concreteᵉ groupᵉ `G`ᵉ isᵉ aᵉ pointedᵉ transitiveᵉ `G`-set.ᵉ

## Definition

```agda
subgroup-action-Concrete-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ) →
  classifying-type-Concrete-Groupᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subgroup-action-Concrete-Groupᵉ l2ᵉ Gᵉ uᵉ =
  Σᵉ ( transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ)
    ( λ Xᵉ → type-Setᵉ (action-transitive-action-Concrete-Groupᵉ Gᵉ Xᵉ uᵉ))

subgroup-Concrete-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ =
  subgroup-action-Concrete-Groupᵉ l2ᵉ Gᵉ (shape-Concrete-Groupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  transitive-action-subgroup-Concrete-Groupᵉ :
    transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ
  transitive-action-subgroup-Concrete-Groupᵉ = pr1ᵉ Hᵉ

  action-subgroup-Concrete-Groupᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ
  action-subgroup-Concrete-Groupᵉ =
    action-transitive-action-Concrete-Groupᵉ Gᵉ
      transitive-action-subgroup-Concrete-Groupᵉ

  coset-subgroup-Concrete-Groupᵉ : Setᵉ l2ᵉ
  coset-subgroup-Concrete-Groupᵉ =
    action-subgroup-Concrete-Groupᵉ (shape-Concrete-Groupᵉ Gᵉ)

  type-coset-subgroup-Concrete-Groupᵉ : UUᵉ l2ᵉ
  type-coset-subgroup-Concrete-Groupᵉ = type-Setᵉ coset-subgroup-Concrete-Groupᵉ

  is-transitive-action-subgroup-Concrete-Groupᵉ :
    is-transitive-action-Concrete-Groupᵉ Gᵉ action-subgroup-Concrete-Groupᵉ
  is-transitive-action-subgroup-Concrete-Groupᵉ =
    is-transitive-transitive-action-Concrete-Groupᵉ Gᵉ
      transitive-action-subgroup-Concrete-Groupᵉ

  mul-transitive-action-subgroup-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ Gᵉ → type-coset-subgroup-Concrete-Groupᵉ →
    type-coset-subgroup-Concrete-Groupᵉ
  mul-transitive-action-subgroup-Concrete-Groupᵉ =
    mul-transitive-action-Concrete-Groupᵉ Gᵉ
      transitive-action-subgroup-Concrete-Groupᵉ

  is-abstractly-transitive-transitive-action-subgroup-Concrete-Groupᵉ :
    is-abstractly-transitive-action-Concrete-Groupᵉ Gᵉ
      action-subgroup-Concrete-Groupᵉ
  is-abstractly-transitive-transitive-action-subgroup-Concrete-Groupᵉ =
    is-abstractly-transitive-transitive-action-Concrete-Groupᵉ Gᵉ
      transitive-action-subgroup-Concrete-Groupᵉ

  classifying-type-subgroup-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  classifying-type-subgroup-Concrete-Groupᵉ =
    orbit-action-Concrete-Groupᵉ Gᵉ action-subgroup-Concrete-Groupᵉ

  unit-coset-subgroup-Concrete-Groupᵉ : type-coset-subgroup-Concrete-Groupᵉ
  unit-coset-subgroup-Concrete-Groupᵉ = pr2ᵉ Hᵉ

  shape-subgroup-Concrete-Groupᵉ : classifying-type-subgroup-Concrete-Groupᵉ
  pr1ᵉ shape-subgroup-Concrete-Groupᵉ = shape-Concrete-Groupᵉ Gᵉ
  pr2ᵉ shape-subgroup-Concrete-Groupᵉ = unit-coset-subgroup-Concrete-Groupᵉ

  classifying-pointed-type-subgroup-Concrete-Groupᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ classifying-pointed-type-subgroup-Concrete-Groupᵉ =
    classifying-type-subgroup-Concrete-Groupᵉ
  pr2ᵉ classifying-pointed-type-subgroup-Concrete-Groupᵉ =
    shape-subgroup-Concrete-Groupᵉ

  is-connected-classifying-type-subgroup-Concrete-Groupᵉ :
    is-0-connectedᵉ classifying-type-subgroup-Concrete-Groupᵉ
  is-connected-classifying-type-subgroup-Concrete-Groupᵉ =
    is-transitive-action-subgroup-Concrete-Groupᵉ

  classifying-inclusion-subgroup-Concrete-Groupᵉ :
    classifying-type-subgroup-Concrete-Groupᵉ →
    classifying-type-Concrete-Groupᵉ Gᵉ
  classifying-inclusion-subgroup-Concrete-Groupᵉ = pr1ᵉ

  preserves-shape-classifying-inclusion-subgroup-Concrete-Groupᵉ :
    classifying-inclusion-subgroup-Concrete-Groupᵉ
      shape-subgroup-Concrete-Groupᵉ ＝ᵉ
    shape-Concrete-Groupᵉ Gᵉ
  preserves-shape-classifying-inclusion-subgroup-Concrete-Groupᵉ = reflᵉ

  classifying-pointed-inclusion-subgroup-Concrete-Groupᵉ :
    classifying-pointed-type-subgroup-Concrete-Groupᵉ →∗ᵉ
    classifying-pointed-type-Concrete-Groupᵉ Gᵉ
  pr1ᵉ classifying-pointed-inclusion-subgroup-Concrete-Groupᵉ =
    classifying-inclusion-subgroup-Concrete-Groupᵉ
  pr2ᵉ classifying-pointed-inclusion-subgroup-Concrete-Groupᵉ =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Groupᵉ

  is-0-map-classifying-inclusion-subgroup-Concrete-Groupᵉ :
    is-0-mapᵉ classifying-inclusion-subgroup-Concrete-Groupᵉ
  is-0-map-classifying-inclusion-subgroup-Concrete-Groupᵉ =
    is-0-map-pr1ᵉ (λ uᵉ → is-set-type-Setᵉ (action-subgroup-Concrete-Groupᵉ uᵉ))

  is-faithful-classifying-inclusion-subgroup-Concrete-Groupᵉ :
    is-faithfulᵉ classifying-inclusion-subgroup-Concrete-Groupᵉ
  is-faithful-classifying-inclusion-subgroup-Concrete-Groupᵉ =
    is-faithful-is-0-mapᵉ is-0-map-classifying-inclusion-subgroup-Concrete-Groupᵉ

  type-subgroup-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subgroup-Concrete-Groupᵉ =
    type-Ωᵉ classifying-pointed-type-subgroup-Concrete-Groupᵉ

  concrete-group-subgroup-Concrete-Groupᵉ :
    Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (pr1ᵉ concrete-group-subgroup-Concrete-Groupᵉ) =
    classifying-pointed-type-subgroup-Concrete-Groupᵉ
  pr2ᵉ (pr1ᵉ concrete-group-subgroup-Concrete-Groupᵉ) =
    is-connected-classifying-type-subgroup-Concrete-Groupᵉ
  pr2ᵉ concrete-group-subgroup-Concrete-Groupᵉ =
    is-set-is-embᵉ
      ( map-Ωᵉ (classifying-pointed-inclusion-subgroup-Concrete-Groupᵉ))
      ( is-emb-map-Ωᵉ
        ( classifying-pointed-inclusion-subgroup-Concrete-Groupᵉ)
        ( is-faithful-classifying-inclusion-subgroup-Concrete-Groupᵉ))
      ( is-set-type-Concrete-Groupᵉ Gᵉ)

  hom-inclusion-subgroup-Concrete-Groupᵉ :
    hom-Concrete-Groupᵉ concrete-group-subgroup-Concrete-Groupᵉ Gᵉ
  pr1ᵉ hom-inclusion-subgroup-Concrete-Groupᵉ =
    classifying-inclusion-subgroup-Concrete-Groupᵉ
  pr2ᵉ hom-inclusion-subgroup-Concrete-Groupᵉ =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Groupᵉ
```

## Properties

### The type of subgroups of a group is a set

```agda
subtype-preserves-unit-coset-equiv-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
  (Yᵉ : subgroup-Concrete-Groupᵉ l3ᵉ Gᵉ) →
  subtypeᵉ l3ᵉ
    ( equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ))
subtype-preserves-unit-coset-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ =
  Id-Propᵉ
    ( coset-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ)
    ( map-equiv-action-Concrete-Groupᵉ Gᵉ
      ( action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
      ( action-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)
      ( unit-coset-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ))
    ( unit-coset-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ)

equiv-subgroup-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) → subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ →
  subgroup-Concrete-Groupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
equiv-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  type-subtypeᵉ
    ( subtype-preserves-unit-coset-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)

extensionality-subgroup-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ Yᵉ : subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ) →
  (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ
extensionality-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ =
  extensionality-Σᵉ
    ( λ {Yᵉ} yᵉ eᵉ →
      ( map-equivᵉ
        ( eᵉ (shape-Concrete-Groupᵉ Gᵉ))
        ( unit-coset-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)) ＝ᵉ
      ( yᵉ))
    ( id-equiv-action-Concrete-Groupᵉ Gᵉ (action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ))
    ( reflᵉ)
    ( extensionality-transitive-action-Concrete-Groupᵉ Gᵉ
      ( transitive-action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ))
    ( λ xᵉ → id-equivᵉ)

is-set-subgroup-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) →
  is-setᵉ (subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
is-set-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ =
  is-prop-equivᵉ
    ( extensionality-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
    ( λ eᵉ fᵉ →
      is-proof-irrelevant-is-propᵉ
        ( is-set-type-subtypeᵉ
          ( subtype-preserves-unit-coset-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
          ( is-set-equiv-action-Concrete-Groupᵉ Gᵉ
            ( action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
            ( action-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ))
          ( eᵉ)
          ( fᵉ))
        ( eq-type-subtypeᵉ
          ( subtype-preserves-unit-coset-equiv-action-Concrete-Groupᵉ Gᵉ Xᵉ Yᵉ)
          ( eq-htpy-equiv-action-Concrete-Groupᵉ Gᵉ
            ( action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
            ( action-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ)
            ( pr1ᵉ eᵉ)
            ( pr1ᵉ fᵉ)
            ( htpy-exists-equiv-transitive-action-Concrete-Groupᵉ Gᵉ
              ( transitive-action-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
              ( transitive-action-subgroup-Concrete-Groupᵉ Gᵉ Yᵉ)
              ( pr1ᵉ eᵉ)
              ( pr1ᵉ fᵉ)
              ( intro-existsᵉ
                ( unit-coset-subgroup-Concrete-Groupᵉ Gᵉ Xᵉ)
                ( pr2ᵉ eᵉ ∙ᵉ invᵉ (pr2ᵉ fᵉ)))))))
```