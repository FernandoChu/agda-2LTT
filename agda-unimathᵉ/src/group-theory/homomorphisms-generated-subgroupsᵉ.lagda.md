# Homomorphisms of generated subgroups

```agda
module group-theory.homomorphisms-generated-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.epimorphisms-groupsᵉ
open import group-theory.full-subgroupsᵉ
open import group-theory.generating-sets-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subgroups-generated-by-subsets-groupsᵉ
open import group-theory.subsets-groupsᵉ

open import lists.listsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) fromᵉ aᵉ
[subgroupᵉ generatedᵉ byᵉ aᵉ subset](group-theory.subgroups-generated-by-subsets-groups.mdᵉ)
`S`ᵉ isᵉ definedᵉ byᵉ itsᵉ valuesᵉ onᵉ `S`.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Sᵉ : subset-Groupᵉ l2ᵉ Gᵉ) (G'ᵉ : Groupᵉ l3ᵉ)
  where

  distributivity-hom-group-ev-formal-combinationᵉ :
    ( fᵉ : hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ) →
    ( lᵉ : formal-combination-subset-Groupᵉ Gᵉ Sᵉ) →
    Idᵉ
      ( map-hom-Groupᵉ
        ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
        ( G'ᵉ)
        ( fᵉ)
        ( ( ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ lᵉ) ,ᵉ
          ( unit-trunc-Propᵉ (lᵉ ,ᵉ reflᵉ))))
      ( fold-listᵉ
        ( unit-Groupᵉ G'ᵉ)
        ( λ (sᵉ ,ᵉ xᵉ) →
          mul-Groupᵉ
            ( G'ᵉ)
            ( map-hom-Groupᵉ
              ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
              ( G'ᵉ)
              ( fᵉ)
              ( ( ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ (unit-listᵉ (sᵉ ,ᵉ xᵉ))) ,ᵉ
                ( unit-trunc-Propᵉ (unit-listᵉ (sᵉ ,ᵉ xᵉ) ,ᵉ reflᵉ)))))
        ( lᵉ))
  distributivity-hom-group-ev-formal-combinationᵉ fᵉ nilᵉ =
    preserves-unit-hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ fᵉ
  distributivity-hom-group-ev-formal-combinationᵉ fᵉ (consᵉ (sᵉ ,ᵉ xᵉ) lᵉ) =
    ( apᵉ
      ( map-hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ fᵉ)
      ( eq-pair-Σᵉ
        ( preserves-concat-ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ
          ( unit-listᵉ (sᵉ ,ᵉ xᵉ))
          ( lᵉ))
        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
    ( preserves-mul-hom-Groupᵉ
      ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
      ( G'ᵉ)
      ( fᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Groupᵉ G'ᵉ
        ( map-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( fᵉ)
          ( pairᵉ
            ( ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ (unit-listᵉ (sᵉ ,ᵉ xᵉ)))
            ( unit-trunc-Propᵉ (unit-listᵉ (sᵉ ,ᵉ xᵉ) ,ᵉ reflᵉ)))))
      ( distributivity-hom-group-ev-formal-combinationᵉ fᵉ lᵉ))

  map-restriction-generating-subset-Subgroupᵉ :
    hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ →
    type-subtypeᵉ Sᵉ → type-Groupᵉ G'ᵉ
  map-restriction-generating-subset-Subgroupᵉ fᵉ xᵉ =
    map-hom-Groupᵉ
      ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
      ( G'ᵉ)
      ( fᵉ)
      ( pairᵉ
        ( ev-formal-combination-subset-Groupᵉ
          ( Gᵉ)
          ( Sᵉ)
          ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ)))
        ( unit-trunc-Propᵉ
          ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ) ,ᵉ reflᵉ)))

  is-emb-map-restriction-generating-subset-Subgroupᵉ :
    is-embᵉ (map-restriction-generating-subset-Subgroupᵉ)
  is-emb-map-restriction-generating-subset-Subgroupᵉ fᵉ gᵉ =
    is-equiv-is-invertibleᵉ
      ( λ Pᵉ →
        eq-htpy-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( λ xᵉ →
            apply-universal-property-trunc-Propᵉ
              ( pr2ᵉ xᵉ)
              ( Id-Propᵉ
                ( set-Groupᵉ G'ᵉ)
                ( map-hom-Groupᵉ
                  ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
                  ( G'ᵉ)
                  ( fᵉ)
                  ( xᵉ))
                ( map-hom-Groupᵉ
                  ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
                  ( G'ᵉ)
                  ( gᵉ)
                  ( xᵉ)))
              ( λ (yᵉ ,ᵉ Qᵉ) →
                ( apᵉ
                  ( map-hom-Groupᵉ
                    ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
                    ( G'ᵉ)
                    ( fᵉ))
                  ( eq-pair-Σᵉ (invᵉ Qᵉ) (eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                ( distributivity-hom-group-ev-formal-combinationᵉ fᵉ yᵉ) ∙ᵉ
                ( apᵉ
                  ( λ Fᵉ →
                    fold-listᵉ (unit-Groupᵉ G'ᵉ) (λ Yᵉ → mul-Groupᵉ G'ᵉ (Fᵉ Yᵉ)) yᵉ)
                  ( eq-htpyᵉ (lemmaᵉ (htpy-eqᵉ Pᵉ)))) ∙ᵉ
                ( invᵉ
                  ( distributivity-hom-group-ev-formal-combinationᵉ gᵉ yᵉ)) ∙ᵉ
                ( apᵉ
                  ( map-hom-Groupᵉ
                    ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
                    ( G'ᵉ)
                    ( gᵉ))
                  ( eq-pair-Σᵉ
                    ( Qᵉ)
                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))))
      ( λ pᵉ →
        eq-is-propᵉ
          ( is-trunc-Πᵉ
            ( zero-𝕋ᵉ)
            ( λ zᵉ → is-set-type-Groupᵉ G'ᵉ)
            ( λ Sᵉ → map-restriction-generating-subset-Subgroupᵉ fᵉ Sᵉ)
            ( λ Sᵉ → map-restriction-generating-subset-Subgroupᵉ gᵉ Sᵉ)))
      ( λ pᵉ →
        eq-is-propᵉ
          ( is-set-hom-Groupᵉ
            ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
            ( G'ᵉ)
            ( fᵉ)
            ( gᵉ)))
    where
    lemmaᵉ :
      ( (xᵉ : type-subtypeᵉ Sᵉ) →
        Idᵉ
          ( map-hom-Groupᵉ
            ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
            ( G'ᵉ)
            ( fᵉ)
            ( pairᵉ
              ( ev-formal-combination-subset-Groupᵉ
                ( Gᵉ)
                ( Sᵉ)
                ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ)))
              ( unit-trunc-Propᵉ (unit-listᵉ (pairᵉ (inrᵉ starᵉ) xᵉ) ,ᵉ reflᵉ))))
          ( map-hom-Groupᵉ
            ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
            ( G'ᵉ)
            ( gᵉ)
            ( pairᵉ
              ( ev-formal-combination-subset-Groupᵉ
                ( Gᵉ)
                ( Sᵉ)
                ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ)))
              ( unit-trunc-Propᵉ
                ( unit-listᵉ (pairᵉ (inrᵉ starᵉ) xᵉ) ,ᵉ reflᵉ))))) →
      ( zᵉ : Finᵉ 2 ×ᵉ type-subtypeᵉ Sᵉ) →
      Idᵉ
        ( map-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( fᵉ)
          ( pairᵉ
            ( ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ (unit-listᵉ zᵉ))
            ( unit-trunc-Propᵉ (unit-listᵉ zᵉ ,ᵉ reflᵉ))))
        ( map-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( gᵉ)
          ( pairᵉ
            ( ev-formal-combination-subset-Groupᵉ Gᵉ Sᵉ (unit-listᵉ zᵉ))
            ( unit-trunc-Propᵉ (unit-listᵉ zᵉ ,ᵉ reflᵉ))))
    lemmaᵉ Pᵉ (inlᵉ (inrᵉ starᵉ) ,ᵉ xᵉ ,ᵉ sᵉ) =
      ( apᵉ
        ( map-hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ fᵉ)
        ( eq-pair-Σᵉ
          ( right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ))
          ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
      ( preserves-inv-hom-Groupᵉ
        ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
        ( G'ᵉ)
        ( fᵉ)) ∙ᵉ
      ( apᵉ
        ( inv-Groupᵉ G'ᵉ)
        ( ( apᵉ
          ( map-hom-Groupᵉ
            ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
            ( G'ᵉ)
            ( fᵉ))
          ( eq-pair-Σᵉ
            { sᵉ =
              pairᵉ
                ( xᵉ)
                ( unit-trunc-Propᵉ
                  ( pairᵉ
                    ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ ,ᵉ sᵉ))
                    ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)))}
            ( invᵉ (right-unit-law-mul-Groupᵉ Gᵉ xᵉ))
            ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
          ( ( Pᵉ (xᵉ ,ᵉ sᵉ)) ∙ᵉ
            ( apᵉ
              ( map-hom-Groupᵉ
                ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
                ( G'ᵉ)
                ( gᵉ))
              ( eq-pair-Σᵉ
                { sᵉ =
                  pairᵉ
                    ( mul-Groupᵉ Gᵉ xᵉ (unit-Groupᵉ Gᵉ))
                    ( unit-trunc-Propᵉ
                      ( pairᵉ
                        ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ ,ᵉ sᵉ))
                        ( reflᵉ)))}
                { tᵉ =
                  pairᵉ
                    ( xᵉ)
                    ( unit-trunc-Propᵉ
                      ( pairᵉ
                        ( unit-listᵉ (inrᵉ starᵉ ,ᵉ xᵉ ,ᵉ sᵉ))
                        ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)))}
                ( right-unit-law-mul-Groupᵉ Gᵉ xᵉ)
                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))) ∙ᵉ
      ( invᵉ
        ( preserves-inv-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( gᵉ))) ∙ᵉ
      ( apᵉ
        ( map-hom-Groupᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( G'ᵉ)
          ( gᵉ))
        ( eq-pair-Σᵉ
          ( invᵉ (right-unit-law-mul-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)))
          ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))
    lemmaᵉ Pᵉ (inrᵉ starᵉ ,ᵉ xᵉ) = Pᵉ xᵉ

  restriction-generating-subset-Subgroupᵉ :
    hom-Groupᵉ (group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)) G'ᵉ ↪ᵉ
      ( type-subtypeᵉ Sᵉ → type-Groupᵉ G'ᵉ)
  pr1ᵉ restriction-generating-subset-Subgroupᵉ =
    map-restriction-generating-subset-Subgroupᵉ
  pr2ᵉ restriction-generating-subset-Subgroupᵉ =
    is-emb-map-restriction-generating-subset-Subgroupᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Sᵉ : subset-Groupᵉ l2ᵉ Gᵉ) (Hᵉ : is-generating-set-Groupᵉ Gᵉ Sᵉ)
  (G'ᵉ : Groupᵉ l3ᵉ)
  where

  restriction-generating-subset-Groupᵉ :
    hom-Groupᵉ Gᵉ G'ᵉ ↪ᵉ (type-subtypeᵉ Sᵉ → type-Groupᵉ G'ᵉ)
  restriction-generating-subset-Groupᵉ =
    comp-embᵉ
      ( restriction-generating-subset-Subgroupᵉ Gᵉ Sᵉ G'ᵉ)
      ( pairᵉ
        ( λ fᵉ →
          comp-hom-Groupᵉ
            ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
            ( Gᵉ)
            ( G'ᵉ)
            ( fᵉ)
            ( pr1ᵉ ,ᵉ λ {xᵉ} {yᵉ} → reflᵉ))
        ( is-epi-iso-Groupᵉ l3ᵉ
          ( group-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ))
          ( Gᵉ)
          ( iso-inclusion-is-full-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ) Hᵉ)
          ( G'ᵉ)))

  eq-map-restriction-generating-subset-Groupᵉ :
    ( fᵉ : hom-Groupᵉ Gᵉ G'ᵉ) (xᵉ : type-subtypeᵉ Sᵉ) →
    Idᵉ
      ( map-embᵉ restriction-generating-subset-Groupᵉ fᵉ xᵉ)
      ( map-hom-Groupᵉ Gᵉ G'ᵉ fᵉ (pr1ᵉ xᵉ))
  eq-map-restriction-generating-subset-Groupᵉ fᵉ xᵉ =
    apᵉ
      ( map-hom-Groupᵉ Gᵉ G'ᵉ fᵉ)
      ( right-unit-law-mul-Groupᵉ Gᵉ (pr1ᵉ xᵉ))
```