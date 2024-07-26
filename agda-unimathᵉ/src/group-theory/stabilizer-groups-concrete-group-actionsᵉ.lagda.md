# Stabilizers of concrete group actions

```agda
module group-theory.stabilizer-groups-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.subgroups-concrete-groupsᵉ
open import group-theory.transitive-concrete-group-actionsᵉ
```

</details>

## Idea

Theᵉ **stabilizer**ᵉ ofᵉ anᵉ elementᵉ `xᵉ : Xᵉ point`ᵉ ofᵉ aᵉ
[concreteᵉ `G`-set](group-theory.concrete-group-actions.mdᵉ) `Xᵉ : BGᵉ → Set`ᵉ isᵉ theᵉ
[connectedᵉ component](foundation.connected-components.mdᵉ) atᵉ theᵉ elementᵉ
`(pointᵉ ,ᵉ x)`ᵉ in theᵉ typeᵉ ofᵉ
[orbits](group-theory.orbits-concrete-group-actions.mdᵉ) ofᵉ `X`.ᵉ Thisᵉ typeᵉ isᵉ aᵉ
indeedᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ) ofᵉ whichᵉ theᵉ underlyingᵉ
typeᵉ isᵉ theᵉ typeᵉ ofᵉ elementsᵉ `gᵉ : G`ᵉ suchᵉ thatᵉ `gᵉ xᵉ = x`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  action-stabilizer-action-Concrete-Groupᵉ :
    type-action-Concrete-Groupᵉ Gᵉ Xᵉ → action-Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  action-stabilizer-action-Concrete-Groupᵉ xᵉ uᵉ =
    set-subsetᵉ
      ( Xᵉ uᵉ)
      ( λ yᵉ → mere-eq-Propᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ) (uᵉ ,ᵉ yᵉ))

  is-transitive-action-stabilizer-action-Concrete-Groupᵉ :
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) →
    is-transitive-action-Concrete-Groupᵉ Gᵉ
      ( action-stabilizer-action-Concrete-Groupᵉ xᵉ)
  is-transitive-action-stabilizer-action-Concrete-Groupᵉ xᵉ =
    is-0-connected-equiv'ᵉ
      ( associative-Σᵉ
        ( classifying-type-Concrete-Groupᵉ Gᵉ)
        ( type-Setᵉ ∘ᵉ Xᵉ)
        ( mere-eqᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ)))
      ( is-0-connected-mere-eqᵉ
        ( ( shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ) ,ᵉ
          ( refl-mere-eqᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ)))
        ( λ (uyᵉ ,ᵉ pᵉ) →
          apply-universal-property-trunc-Propᵉ pᵉ
            ( mere-eq-Propᵉ
              ( ( shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ) ,ᵉ
                ( refl-mere-eqᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ)))
              ( uyᵉ ,ᵉ pᵉ))
            ( λ qᵉ →
              unit-trunc-Propᵉ
                ( eq-type-subtypeᵉ
                  ( mere-eq-Propᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ))
                  ( qᵉ)))))

  subgroup-stabilizer-action-Concrete-Groupᵉ :
    (xᵉ : type-action-Concrete-Groupᵉ Gᵉ Xᵉ) → subgroup-Concrete-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Gᵉ
  pr1ᵉ (pr1ᵉ (subgroup-stabilizer-action-Concrete-Groupᵉ xᵉ)) =
    action-stabilizer-action-Concrete-Groupᵉ xᵉ
  pr2ᵉ (pr1ᵉ (subgroup-stabilizer-action-Concrete-Groupᵉ xᵉ)) =
    is-transitive-action-stabilizer-action-Concrete-Groupᵉ xᵉ
  pr1ᵉ (pr2ᵉ (subgroup-stabilizer-action-Concrete-Groupᵉ xᵉ)) = xᵉ
  pr2ᵉ (pr2ᵉ (subgroup-stabilizer-action-Concrete-Groupᵉ xᵉ)) =
    refl-mere-eqᵉ (shape-Concrete-Groupᵉ Gᵉ ,ᵉ xᵉ)
```

## External links

-ᵉ [stabilizerᵉ group](https://ncatlab.org/nlab/show/stabilizer+groupᵉ) atᵉ $n$Labᵉ
-ᵉ [Fixedᵉ pointsᵉ andᵉ stabilizerᵉ subgroups](https://en.wikipedia.org/wiki/Group_action#Fixed_points_and_stabilizer_subgroupsᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Isotropyᵉ Group](https://mathworld.wolfram.com/IsotropyGroup.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ
-ᵉ [Isotropyᵉ group](https://encyclopediaofmath.org/wiki/Isotropy_groupᵉ) atᵉ
  Encyclopediaᵉ ofᵉ Mathematicsᵉ