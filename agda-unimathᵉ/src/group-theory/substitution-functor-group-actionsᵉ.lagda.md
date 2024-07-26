# The substitution functor of group actions

```agda
module group-theory.substitution-functor-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.precategory-of-group-actionsᵉ
open import group-theory.symmetric-groupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ
andᵉ anᵉ [`H`-set](group-theory.group-actions.mdᵉ) `Y`,ᵉ weᵉ obtainᵉ aᵉ `G`-actionᵉ onᵉ
`Y`ᵉ byᵉ `g,xᵉ ↦ᵉ f(g)x`.ᵉ Thisᵉ operationᵉ isᵉ functorialᵉ in `Y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Gᵉ : Groupᵉ l1ᵉ} {Hᵉ : Groupᵉ l2ᵉ} (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  obj-subst-action-Groupᵉ :
    {l3ᵉ : Level} → action-Groupᵉ Hᵉ l3ᵉ → action-Groupᵉ Gᵉ l3ᵉ
  pr1ᵉ (obj-subst-action-Groupᵉ Xᵉ) = set-action-Groupᵉ Hᵉ Xᵉ
  pr2ᵉ (obj-subst-action-Groupᵉ Xᵉ) =
    comp-hom-Groupᵉ Gᵉ Hᵉ
      ( symmetric-Groupᵉ (set-action-Groupᵉ Hᵉ Xᵉ))
      ( pr2ᵉ Xᵉ)
      ( fᵉ)

  hom-subst-action-Groupᵉ :
    {l3ᵉ l4ᵉ : Level}
    (Xᵉ : action-Groupᵉ Hᵉ l3ᵉ) (Yᵉ : action-Groupᵉ Hᵉ l4ᵉ) →
    hom-action-Groupᵉ Hᵉ Xᵉ Yᵉ →
    hom-action-Groupᵉ Gᵉ
      ( obj-subst-action-Groupᵉ Xᵉ)
      ( obj-subst-action-Groupᵉ Yᵉ)
  pr1ᵉ (hom-subst-action-Groupᵉ Xᵉ Yᵉ hᵉ) = pr1ᵉ hᵉ
  pr2ᵉ (hom-subst-action-Groupᵉ Xᵉ Yᵉ hᵉ) xᵉ = pr2ᵉ hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)

  preserves-id-subst-action-Groupᵉ :
    {l3ᵉ : Level} (Xᵉ : action-Groupᵉ Hᵉ l3ᵉ) →
    Idᵉ
      ( hom-subst-action-Groupᵉ Xᵉ Xᵉ (id-hom-action-Groupᵉ Hᵉ Xᵉ))
      ( id-hom-action-Groupᵉ Gᵉ (obj-subst-action-Groupᵉ Xᵉ))
  preserves-id-subst-action-Groupᵉ Xᵉ = reflᵉ

  preserves-comp-subst-action-Groupᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level} (Xᵉ : action-Groupᵉ Hᵉ l3ᵉ)
    (Yᵉ : action-Groupᵉ Hᵉ l4ᵉ) (Zᵉ : action-Groupᵉ Hᵉ l5ᵉ)
    (gᵉ : hom-action-Groupᵉ Hᵉ Yᵉ Zᵉ)
    (fᵉ : hom-action-Groupᵉ Hᵉ Xᵉ Yᵉ) →
    Idᵉ
      ( hom-subst-action-Groupᵉ Xᵉ Zᵉ
        ( comp-hom-action-Groupᵉ Hᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ))
      ( comp-hom-action-Groupᵉ Gᵉ
        ( obj-subst-action-Groupᵉ Xᵉ)
        ( obj-subst-action-Groupᵉ Yᵉ)
        ( obj-subst-action-Groupᵉ Zᵉ)
        ( hom-subst-action-Groupᵉ Yᵉ Zᵉ gᵉ)
        ( hom-subst-action-Groupᵉ Xᵉ Yᵉ fᵉ))
  preserves-comp-subst-action-Groupᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ = reflᵉ

  subst-action-Groupᵉ :
    functor-Large-Precategoryᵉ (λ lᵉ → lᵉ)
      ( action-Group-Large-Precategoryᵉ Hᵉ)
      ( action-Group-Large-Precategoryᵉ Gᵉ)
  obj-functor-Large-Precategoryᵉ subst-action-Groupᵉ =
    obj-subst-action-Groupᵉ
  hom-functor-Large-Precategoryᵉ subst-action-Groupᵉ {Xᵉ = Xᵉ} {Yᵉ} =
    hom-subst-action-Groupᵉ Xᵉ Yᵉ
  preserves-comp-functor-Large-Precategoryᵉ subst-action-Groupᵉ
    {l1ᵉ} {l2ᵉ} {l3ᵉ} {Xᵉ} {Yᵉ} {Zᵉ} =
    preserves-comp-subst-action-Groupᵉ Xᵉ Yᵉ Zᵉ
  preserves-id-functor-Large-Precategoryᵉ
    subst-action-Groupᵉ {l1ᵉ} {Xᵉ} =
    preserves-id-subst-action-Groupᵉ Xᵉ
```

## Properties

### The substitution functor has a left adjoint

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Gᵉ : Groupᵉ l1ᵉ} {Hᵉ : Groupᵉ l2ᵉ} (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preset-obj-left-adjoint-subst-action-Groupᵉ :
    {l3ᵉ : Level} → action-Groupᵉ Gᵉ l3ᵉ → Setᵉ (l2ᵉ ⊔ l3ᵉ)
  preset-obj-left-adjoint-subst-action-Groupᵉ Xᵉ =
    product-Setᵉ (set-Groupᵉ Hᵉ) (set-action-Groupᵉ Gᵉ Xᵉ)

  pretype-obj-left-adjoint-subst-action-Groupᵉ :
    {l3ᵉ : Level} → action-Groupᵉ Gᵉ l3ᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  pretype-obj-left-adjoint-subst-action-Groupᵉ Xᵉ =
    type-Setᵉ (preset-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)

  is-set-pretype-obj-left-adjoint-subst-action-Groupᵉ :
    {l3ᵉ : Level} (Xᵉ : action-Groupᵉ Gᵉ l3ᵉ) →
    is-setᵉ (pretype-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
  is-set-pretype-obj-left-adjoint-subst-action-Groupᵉ Xᵉ =
    is-set-type-Setᵉ (preset-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)

  equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ :
    {l3ᵉ : Level} (Xᵉ : action-Groupᵉ Gᵉ l3ᵉ) →
    equivalence-relationᵉ
      ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
      ( pretype-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
  pr1ᵉ
    ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
    ( hᵉ ,ᵉ xᵉ)
    ( h'ᵉ ,ᵉ x'ᵉ) =
    exists-structure-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ gᵉ →
        ( Idᵉ (mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ) hᵉ) h'ᵉ) ×ᵉ
        ( Idᵉ (mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ) x'ᵉ))
  pr1ᵉ
    ( pr2ᵉ (equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ))
    ( hᵉ ,ᵉ xᵉ) =
    intro-existsᵉ
      ( unit-Groupᵉ Gᵉ)
      ( pairᵉ
        ( ( apᵉ (mul-Group'ᵉ Hᵉ hᵉ) (preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
          ( left-unit-law-mul-Groupᵉ Hᵉ hᵉ))
        ( preserves-unit-mul-action-Groupᵉ Gᵉ Xᵉ xᵉ))
  pr1ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)))
    ( hᵉ ,ᵉ xᵉ)
    ( h'ᵉ ,ᵉ x'ᵉ)
    ( eᵉ) =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( pr1ᵉ
        ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
        ( h'ᵉ ,ᵉ x'ᵉ)
        ( hᵉ ,ᵉ xᵉ))
      ( λ (gᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
        intro-existsᵉ
          ( inv-Groupᵉ Gᵉ gᵉ)
          ( ( ( apᵉ
                ( mul-Group'ᵉ Hᵉ h'ᵉ)
                ( preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
              ( invᵉ (transpose-eq-mul-Group'ᵉ Hᵉ pᵉ))) ,ᵉ
            ( invᵉ (transpose-eq-mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ x'ᵉ qᵉ))))
  pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ
        ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)))
    ( hᵉ ,ᵉ xᵉ)
    ( h'ᵉ ,ᵉ x'ᵉ)
    ( h''ᵉ ,ᵉ x''ᵉ)
    ( dᵉ)
    ( eᵉ) =
    apply-universal-property-trunc-Propᵉ eᵉ
      ( pr1ᵉ
        ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
        ( hᵉ ,ᵉ xᵉ)
        ( h''ᵉ ,ᵉ x''ᵉ))
      ( λ (gᵉ ,ᵉ pᵉ ,ᵉ qᵉ) →
        apply-universal-property-trunc-Propᵉ dᵉ
          ( pr1ᵉ
            ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ
              ( Xᵉ))
            ( hᵉ ,ᵉ xᵉ)
            ( h''ᵉ ,ᵉ x''ᵉ))
          ( λ (g'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) →
            intro-existsᵉ
              ( mul-Groupᵉ Gᵉ g'ᵉ gᵉ)
              ( ( ( apᵉ
                    ( mul-Group'ᵉ Hᵉ hᵉ)
                    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
                  ( associative-mul-Groupᵉ Hᵉ
                    ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ g'ᵉ)
                    ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ)
                    ( hᵉ)) ∙ᵉ
                  ( apᵉ (mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ g'ᵉ)) pᵉ) ∙ᵉ
                  ( p'ᵉ)) ,ᵉ
                ( ( preserves-mul-action-Groupᵉ Gᵉ Xᵉ g'ᵉ gᵉ xᵉ) ∙ᵉ
                  ( apᵉ (mul-action-Groupᵉ Gᵉ Xᵉ g'ᵉ) qᵉ) ∙ᵉ
                  ( q'ᵉ)))))

  set-left-adjoint-subst-action-Groupᵉ :
    {l3ᵉ : Level} → action-Groupᵉ Gᵉ l3ᵉ →
    Setᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  set-left-adjoint-subst-action-Groupᵉ Xᵉ =
    equivalence-class-Setᵉ
      ( equivalence-relation-obj-left-adjoint-subst-action-Groupᵉ Xᵉ)
```