# Deloopings of the sign homomorphism

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.delooping-sign-homomorphismᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.finite-type-groupsᵉ
open import finite-group-theory.permutationsᵉ
open import finite-group-theory.sign-homomorphismᵉ
open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-equivalences-type-families-over-subuniversesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.generating-sets-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
open import group-theory.homomorphisms-generated-subgroupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.loop-groups-setsᵉ
open import group-theory.symmetric-groupsᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.set-quotients-of-index-twoᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Ideas

Theᵉ deloopingᵉ ofᵉ aᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ isᵉ aᵉ pointedᵉ mapᵉ
`Bfᵉ : BGᵉ → BH`ᵉ equippedᵉ with aᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ followingᵉ squareᵉ
commutesᵉ :

```text
        fᵉ
  Gᵉ -------->ᵉ Hᵉ
  |           |
 ≅|ᵉ           |≅ᵉ
  |           |
  ∨ᵉ           ∨ᵉ
  BGᵉ ------>ᵉ BHᵉ
       ΩBfᵉ
```

Inᵉ thisᵉ file,ᵉ weᵉ studyᵉ theᵉ deloopingᵉ ofᵉ theᵉ signᵉ homomorphism,ᵉ and,ᵉ moreᵉ
precisely,ᵉ howᵉ to detectᵉ thatᵉ aᵉ pointedᵉ mapᵉ betweenᵉ `BSn`ᵉ andᵉ `BS2`ᵉ isᵉ aᵉ
deloopingᵉ ofᵉ theᵉ signᵉ homomorphism.ᵉ

## Definition

### Construction of the delooping of the sign homomorphism with quotients (Corollary 25)

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level}
  ( Dᵉ : (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) → UUᵉ l2ᵉ)
  ( Rᵉ : (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) → equivalence-relationᵉ l3ᵉ (Dᵉ nᵉ Xᵉ))
  ( is-decidable-Rᵉ :
    (nᵉ : ℕᵉ) → leq-ℕᵉ 2 nᵉ → (Xᵉ : UU-Finᵉ l1ᵉ nᵉ)
    (aᵉ bᵉ : Dᵉ nᵉ Xᵉ) → is-decidableᵉ (sim-equivalence-relationᵉ (Rᵉ nᵉ Xᵉ) aᵉ bᵉ))
  ( equiv-D/R-fin-2-equivᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) →
    leq-ℕᵉ 2 nᵉ → Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ →
    Finᵉ 2 ≃ᵉ equivalence-classᵉ (Rᵉ nᵉ Xᵉ))
  ( quotient-aut-succ-succ-Finᵉ : (nᵉ : ℕᵉ) →
    ( raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)) →
    Dᵉ ( nᵉ +ℕᵉ 2ᵉ)
      ( raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
        unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
  ( not-R-transposition-fin-succ-succᵉ : (nᵉ : ℕᵉ) →
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ l1ᵉ (raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( Rᵉ
        ( nᵉ +ℕᵉ 2ᵉ)
        ( raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))
      ( map-equivᵉ
        ( action-equiv-family-over-subuniverseᵉ
          ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( Dᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( transpositionᵉ Yᵉ))
        ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ)))))
  where

  private
    l4ᵉ : Level
    l4ᵉ = l2ᵉ ⊔ lsuc l3ᵉ

    eq-counting-equivalence-class-Rᵉ :
      (nᵉ : ℕᵉ) →
      equivalence-classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Fin-UU-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ＝ᵉ
      raiseᵉ (l2ᵉ ⊔ lsuc l3ᵉ) (Finᵉ 2ᵉ)
    eq-counting-equivalence-class-Rᵉ nᵉ =
      eq-equivᵉ
        ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ
          inv-equivᵉ
            ( equiv-D/R-fin-2-equivᵉ
              ( nᵉ +ℕᵉ 2ᵉ)
              ( Fin-UU-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( starᵉ)
              ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))

    invertible-action-D-equivᵉ :
      (nᵉ : ℕᵉ) (Xᵉ X'ᵉ : UU-Finᵉ l1ᵉ nᵉ) →
      type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ → Dᵉ nᵉ Xᵉ ≃ᵉ Dᵉ nᵉ X'ᵉ
    invertible-action-D-equivᵉ nᵉ =
      action-equiv-family-over-subuniverseᵉ (mere-equiv-Propᵉ (Finᵉ nᵉ)) (Dᵉ nᵉ)

    preserves-id-equiv-invertible-action-D-equivᵉ :
      (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) →
      Idᵉ (invertible-action-D-equivᵉ nᵉ Xᵉ Xᵉ id-equivᵉ) id-equivᵉ
    preserves-id-equiv-invertible-action-D-equivᵉ nᵉ =
      compute-id-equiv-action-equiv-family-over-subuniverseᵉ
        ( mere-equiv-Propᵉ (Finᵉ nᵉ))
        ( Dᵉ nᵉ)

    abstract
      preserves-R-invertible-action-D-equivᵉ :
        ( nᵉ : ℕᵉ) →
        ( Xᵉ X'ᵉ : UU-Finᵉ l1ᵉ nᵉ)
        ( eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
        ( aᵉ a'ᵉ : Dᵉ nᵉ Xᵉ) →
        ( sim-equivalence-relationᵉ (Rᵉ nᵉ Xᵉ) aᵉ a'ᵉ ↔ᵉ
          sim-equivalence-relationᵉ
            ( Rᵉ nᵉ X'ᵉ)
            ( map-equivᵉ (invertible-action-D-equivᵉ nᵉ Xᵉ X'ᵉ eᵉ) aᵉ)
            ( map-equivᵉ (invertible-action-D-equivᵉ nᵉ Xᵉ X'ᵉ eᵉ) a'ᵉ))
      preserves-R-invertible-action-D-equivᵉ nᵉ Xᵉ =
        ind-equiv-subuniverseᵉ
          ( mere-equiv-Propᵉ (Finᵉ nᵉ))
          ( Xᵉ)
          ( λ Yᵉ fᵉ →
            ( aᵉ a'ᵉ : Dᵉ nᵉ Xᵉ) →
            ( sim-equivalence-relationᵉ (Rᵉ nᵉ Xᵉ) aᵉ a'ᵉ ↔ᵉ
              sim-equivalence-relationᵉ
                ( Rᵉ nᵉ Yᵉ)
                ( map-equivᵉ (invertible-action-D-equivᵉ nᵉ Xᵉ Yᵉ fᵉ) aᵉ)
                ( map-equivᵉ (invertible-action-D-equivᵉ nᵉ Xᵉ Yᵉ fᵉ) a'ᵉ)))
          ( λ aᵉ a'ᵉ →
            ( binary-trᵉ
              ( sim-equivalence-relationᵉ (Rᵉ nᵉ Xᵉ))
                ( invᵉ
                  ( htpy-eq-equivᵉ
                    ( preserves-id-equiv-invertible-action-D-equivᵉ nᵉ Xᵉ)
                    ( aᵉ)))
                ( invᵉ
                  ( htpy-eq-equivᵉ
                    ( preserves-id-equiv-invertible-action-D-equivᵉ nᵉ Xᵉ)
                    ( a'ᵉ)))) ,ᵉ
            ( binary-trᵉ
              ( sim-equivalence-relationᵉ (Rᵉ nᵉ Xᵉ))
                ( htpy-eq-equivᵉ
                  ( preserves-id-equiv-invertible-action-D-equivᵉ nᵉ Xᵉ)
                  ( aᵉ))
                ( htpy-eq-equivᵉ
                  ( preserves-id-equiv-invertible-action-D-equivᵉ nᵉ Xᵉ)
                  ( a'ᵉ))))

    raise-UU-Fin-Finᵉ : (nᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ nᵉ
    pr1ᵉ (raise-UU-Fin-Finᵉ nᵉ) = raiseᵉ l1ᵉ (Finᵉ nᵉ)
    pr2ᵉ (raise-UU-Fin-Finᵉ nᵉ) = unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ nᵉ)

    that-thingᵉ :
      (nᵉ : ℕᵉ) →
      Finᵉ 2 ≃ᵉ equivalence-classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
    that-thingᵉ nᵉ =
      equiv-D/R-fin-2-equivᵉ
        ( nᵉ +ℕᵉ 2ᵉ)
        ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( starᵉ)
        ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))

    quotient-loop-Finᵉ :
      (nᵉ : ℕᵉ) → type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
      ( Dᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ≃ᵉ
        Dᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
    quotient-loop-Finᵉ nᵉ pᵉ =
      invertible-action-D-equivᵉ
        ( nᵉ +ℕᵉ 2ᵉ)
        ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( map-hom-symmetric-group-loop-group-Setᵉ
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( pᵉ))

    map-quotient-loop-Finᵉ :
      (nᵉ : ℕᵉ) → type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
      Dᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)) →
      Dᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
    map-quotient-loop-Finᵉ nᵉ pᵉ =
      map-equivᵉ (quotient-loop-Finᵉ nᵉ pᵉ)

    quotient-set-Finᵉ : (nᵉ : ℕᵉ) → Setᵉ l4ᵉ
    quotient-set-Finᵉ nᵉ = equivalence-class-Setᵉ (Rᵉ nᵉ (raise-UU-Fin-Finᵉ nᵉ))

    quotient-map-quotient-Finᵉ :
      (nᵉ : ℕᵉ) → Dᵉ nᵉ (raise-UU-Fin-Finᵉ nᵉ) → type-Setᵉ (quotient-set-Finᵉ nᵉ)
    quotient-map-quotient-Finᵉ nᵉ =
      classᵉ (Rᵉ nᵉ (raise-UU-Fin-Finᵉ nᵉ))

    quotient-reflecting-map-quotient-Finᵉ :
      (nᵉ : ℕᵉ) →
      reflecting-map-equivalence-relationᵉ
        ( Rᵉ nᵉ (raise-UU-Fin-Finᵉ nᵉ))
        ( type-Setᵉ (quotient-set-Finᵉ nᵉ))
    quotient-reflecting-map-quotient-Finᵉ nᵉ =
      quotient-reflecting-map-equivalence-classᵉ (Rᵉ nᵉ (raise-UU-Fin-Finᵉ nᵉ))

  mere-equiv-D/R-fin-2ᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) →
    leq-ℕᵉ 2 nᵉ → mere-equivᵉ (Finᵉ 2ᵉ) (equivalence-classᵉ (Rᵉ nᵉ Xᵉ))
  mere-equiv-D/R-fin-2ᵉ nᵉ Xᵉ ineqᵉ =
    map-trunc-Propᵉ
      ( equiv-D/R-fin-2-equivᵉ nᵉ Xᵉ ineqᵉ)
      ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)

  map-quotient-delooping-signᵉ :
    (nᵉ : ℕᵉ) →
    classifying-type-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ nᵉ) →
    classifying-type-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ)
  map-quotient-delooping-signᵉ 0 Xᵉ = Fin-UU-Finᵉ l4ᵉ 2
  map-quotient-delooping-signᵉ 1 Xᵉ = Fin-UU-Finᵉ l4ᵉ 2
  pr1ᵉ (map-quotient-delooping-signᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Xᵉ) =
    equivalence-classᵉ (Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Xᵉ)
  pr2ᵉ (map-quotient-delooping-signᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Xᵉ) =
    mere-equiv-D/R-fin-2ᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) Xᵉ starᵉ

  quotient-delooping-signᵉ :
    (nᵉ : ℕᵉ) → hom-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ nᵉ) (UU-Fin-Groupᵉ l4ᵉ 2ᵉ)
  pr1ᵉ (quotient-delooping-signᵉ nᵉ) = map-quotient-delooping-signᵉ nᵉ
  pr2ᵉ (quotient-delooping-signᵉ 0ᵉ) = reflᵉ
  pr2ᵉ (quotient-delooping-signᵉ 1ᵉ) = reflᵉ
  pr2ᵉ (quotient-delooping-signᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) =
    eq-pair-Σᵉ
      ( eq-counting-equivalence-class-Rᵉ nᵉ)
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)

  map-quotient-delooping-sign-loopᵉ :
    ( nᵉ : ℕᵉ)
    ( Xᵉ Yᵉ : UUᵉ l1ᵉ) →
    ( eXᵉ : mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) Xᵉ) →
    ( eYᵉ : mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) Yᵉ) →
    Idᵉ Xᵉ Yᵉ →
    Idᵉ
      ( equivalence-classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)))
      ( equivalence-classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Yᵉ ,ᵉ eYᵉ)))
  map-quotient-delooping-sign-loopᵉ nᵉ Xᵉ Yᵉ eXᵉ eYᵉ pᵉ =
    apᵉ
      ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))

  private
    map-quotient-delooping-sign-loop-Finᵉ :
      ( nᵉ : ℕᵉ) →
      type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
      type-Groupᵉ (loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
    map-quotient-delooping-sign-loop-Finᵉ nᵉ =
      map-quotient-delooping-sign-loopᵉ nᵉ
        ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))

  quotient-delooping-sign-loopᵉ :
    ( nᵉ : ℕᵉ) →
    hom-Groupᵉ
      ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
  pr1ᵉ (quotient-delooping-sign-loopᵉ nᵉ) = map-quotient-delooping-sign-loop-Finᵉ nᵉ
  pr2ᵉ (quotient-delooping-sign-loopᵉ nᵉ) {pᵉ} {qᵉ} =
    ( apᵉ
      ( apᵉ (equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( apᵉ
        ( eq-pair-Σᵉ (pᵉ ∙ᵉ qᵉ))
        ( eq-is-propᵉ
          ( is-trunc-Idᵉ
            ( is-prop-type-trunc-Propᵉ _
              ( unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))) ∙ᵉ
        ( interchange-concat-eq-pair-Σᵉ
          ( pᵉ)
          ( qᵉ)
          ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
          ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))) ∙ᵉ
      ( ap-concatᵉ
        ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))
        ( eq-pair-Σᵉ qᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))

  abstract
    coherence-square-map-quotient-delooping-sign-loop-Setᵉ :
      ( nᵉ : ℕᵉ)
      ( Xᵉ Yᵉ : UUᵉ l1ᵉ)
      ( eXᵉ : mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) Xᵉ)
      ( eYᵉ : mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) Yᵉ)
      ( pᵉ : Idᵉ Xᵉ Yᵉ) →
      ( Idᵉ (trᵉ (mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) pᵉ eXᵉ) eYᵉ) →
      ( sXᵉ : is-setᵉ Xᵉ)
      ( sYᵉ : is-setᵉ Yᵉ) →
      coherence-square-mapsᵉ
        ( map-equivᵉ
          ( invertible-action-D-equivᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Yᵉ ,ᵉ eYᵉ)
            ( Xᵉ ,ᵉ eXᵉ)
            ( map-hom-symmetric-group-loop-group-Setᵉ (Xᵉ ,ᵉ sXᵉ) (Yᵉ ,ᵉ sYᵉ) (pᵉ))))
        ( classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Yᵉ ,ᵉ eYᵉ)))
        ( classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)))
        ( map-equivᵉ
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( equivalence-class-Setᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)))
            ( equivalence-class-Setᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Yᵉ ,ᵉ eYᵉ)))
            ( map-quotient-delooping-sign-loopᵉ nᵉ Xᵉ Yᵉ eXᵉ eYᵉ pᵉ)))
    coherence-square-map-quotient-delooping-sign-loop-Setᵉ
      nᵉ Xᵉ .Xᵉ eXᵉ .eXᵉ reflᵉ reflᵉ sXᵉ sYᵉ xᵉ =
      ( apᵉ
        ( λ wᵉ →
          map-equivᵉ
            ( map-hom-symmetric-group-loop-group-Setᵉ
              ( equivalence-class-Setᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)))
              ( equivalence-class-Setᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)))
              ( wᵉ))
            ( classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ)) (xᵉ)))
        ( apᵉ
          ( λ wᵉ → apᵉ (equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ)) (eq-pair-eq-fiberᵉ wᵉ))
          { xᵉ = eq-is-propᵉ is-prop-type-trunc-Propᵉ}
          ( eq-is-propᵉ
            ( is-trunc-Idᵉ
              ( is-prop-type-trunc-Propᵉ
                ( trᵉ (mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) reflᵉ eXᵉ)
                ( eXᵉ)))))) ∙ᵉ
      ( apᵉ
        ( classᵉ (Rᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ trᵉ (mere-equivᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) reflᵉ eXᵉ)))
        ( invᵉ
          ( htpy-eq-equivᵉ
            ( preserves-id-equiv-invertible-action-D-equivᵉ (nᵉ +ℕᵉ 2ᵉ) (Xᵉ ,ᵉ eXᵉ))
            ( xᵉ))))

  coherence-square-map-quotient-delooping-sign-loop-Finᵉ :
    (nᵉ : ℕᵉ) (pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
    coherence-square-mapsᵉ
      ( map-quotient-loop-Finᵉ nᵉ pᵉ)
      ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( map-equivᵉ
        ( map-hom-symmetric-group-loop-group-Setᵉ
          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( map-quotient-delooping-sign-loop-Finᵉ nᵉ pᵉ)))
  coherence-square-map-quotient-delooping-sign-loop-Finᵉ nᵉ pᵉ =
    coherence-square-map-quotient-delooping-sign-loop-Setᵉ nᵉ
      ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( pᵉ)
      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
      ( is-set-type-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( is-set-type-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))

  private
    is-contr-equiv-quotientᵉ :
      ( nᵉ : ℕᵉ) →
      ( pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
      is-contrᵉ
        ( Σᵉ ( type-Groupᵉ (symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
            ( λ h'ᵉ →
              coherence-square-mapsᵉ
                ( map-quotient-loop-Finᵉ nᵉ pᵉ)
                ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( map-reflecting-map-equivalence-relationᵉ
                  ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( map-equivᵉ h'ᵉ)))
    is-contr-equiv-quotientᵉ nᵉ pᵉ =
      unique-equiv-is-set-quotientᵉ
        ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( is-set-quotient-equivalence-classᵉ
          ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( is-set-quotient-equivalence-classᵉ
          ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( quotient-loop-Finᵉ nᵉ pᵉ ,ᵉ
          ( λ {xᵉ} {yᵉ} →
            preserves-R-invertible-action-D-equivᵉ
              ( nᵉ +ℕᵉ 2ᵉ)
              ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( map-hom-symmetric-group-loop-group-Setᵉ
                ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( pᵉ))
              ( xᵉ)
              ( yᵉ)))

  abstract
    eq-quotient-delooping-sign-loop-equiv-is-set-quotientᵉ :
      (nᵉ : ℕᵉ) (pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
      Idᵉ
        ( map-hom-symmetric-group-loop-group-Setᵉ
          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( map-quotient-delooping-sign-loop-Finᵉ nᵉ pᵉ))
        ( pr1ᵉ (centerᵉ (is-contr-equiv-quotientᵉ nᵉ pᵉ)))
    eq-quotient-delooping-sign-loop-equiv-is-set-quotientᵉ nᵉ pᵉ =
      apᵉ pr1ᵉ
        { xᵉ =
          pairᵉ
            ( map-hom-symmetric-group-loop-group-Setᵉ
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( map-quotient-delooping-sign-loop-Finᵉ nᵉ pᵉ))
            ( coherence-square-map-quotient-delooping-sign-loop-Finᵉ nᵉ pᵉ)}
        { yᵉ = centerᵉ (is-contr-equiv-quotientᵉ nᵉ pᵉ)}
        ( eq-is-contrᵉ (is-contr-equiv-quotientᵉ nᵉ pᵉ))

  cases-map-quotient-aut-Finᵉ :
    ( nᵉ : ℕᵉ) →
    ( hᵉ : type-Groupᵉ (symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
    ( is-decidableᵉ
      ( sim-equivalence-relationᵉ
        ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( quotient-aut-succ-succ-Finᵉ nᵉ hᵉ)
        ( map-equivᵉ
          ( invertible-action-D-equivᵉ
            (nᵉ +ℕᵉ 2ᵉ)
            ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( hᵉ))
          ( quotient-aut-succ-succ-Finᵉ nᵉ hᵉ)))) →
    type-Groupᵉ (symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
  cases-map-quotient-aut-Finᵉ nᵉ hᵉ (inlᵉ Dᵉ) = id-equivᵉ
  cases-map-quotient-aut-Finᵉ nᵉ hᵉ (inrᵉ NDᵉ) =
    that-thingᵉ nᵉ ∘eᵉ (equiv-succ-Finᵉ 2 ∘eᵉ (inv-equivᵉ (that-thingᵉ nᵉ)))

  map-quotient-aut-Finᵉ :
    (nᵉ : ℕᵉ) →
    type-Groupᵉ (symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    type-Groupᵉ (symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
  map-quotient-aut-Finᵉ nᵉ hᵉ =
    cases-map-quotient-aut-Finᵉ nᵉ hᵉ
      ( is-decidable-Rᵉ
        ( nᵉ +ℕᵉ 2ᵉ)
        ( starᵉ)
        ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( quotient-aut-succ-succ-Finᵉ nᵉ hᵉ)
        ( map-equivᵉ
          ( invertible-action-D-equivᵉ
            (nᵉ +ℕᵉ 2ᵉ)
            ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( hᵉ))
          ( quotient-aut-succ-succ-Finᵉ nᵉ hᵉ)))

  eq-map-quotient-aut-fin-transpositionᵉ :
    (nᵉ : ℕᵉ) (Yᵉ : 2-Element-Decidable-Subtypeᵉ l1ᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
    Idᵉ
      ( map-quotient-aut-Finᵉ nᵉ (transpositionᵉ Yᵉ))
      ( that-thingᵉ nᵉ ∘eᵉ (equiv-succ-Finᵉ 2 ∘eᵉ (inv-equivᵉ (that-thingᵉ nᵉ))))
  eq-map-quotient-aut-fin-transpositionᵉ nᵉ Yᵉ =
    apᵉ
      ( cases-map-quotient-aut-Finᵉ nᵉ (transpositionᵉ Yᵉ))
      { xᵉ =
        is-decidable-Rᵉ
          ( nᵉ +ℕᵉ 2ᵉ)
          ( starᵉ)
          ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))
          ( map-equivᵉ
            ( invertible-action-D-equivᵉ
              ( nᵉ +ℕᵉ 2ᵉ)
              ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( transpositionᵉ Yᵉ))
            ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ)))}
      { yᵉ = inrᵉ (not-R-transposition-fin-succ-succᵉ nᵉ Yᵉ)}
      ( eq-is-propᵉ
        ( is-prop-is-decidableᵉ
          ( is-prop-sim-equivalence-relationᵉ
            ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))
            ( map-equivᵉ
              ( invertible-action-D-equivᵉ
                ( nᵉ +ℕᵉ 2ᵉ)
                ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( transpositionᵉ Yᵉ))
              ( quotient-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))))))

  private
    this-third-thingᵉ :
      (nᵉ : ℕᵉ) (pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
      Dᵉ ( nᵉ +ℕᵉ 2ᵉ)
        ( raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
    this-third-thingᵉ nᵉ pᵉ =
      quotient-aut-succ-succ-Finᵉ nᵉ
        ( map-hom-symmetric-group-loop-group-Setᵉ
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( pᵉ))

  cases-eq-map-quotient-aut-Finᵉ :
    ( nᵉ : ℕᵉ)
    ( pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
    ( Dᵉ : is-decidableᵉ
      ( sim-equivalence-relationᵉ
        ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( this-third-thingᵉ nᵉ pᵉ)
        ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))) →
    ( kᵉ k'ᵉ : Finᵉ 2ᵉ) →
    Idᵉ
      ( map-inv-equivᵉ
        ( that-thingᵉ nᵉ)
        ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ) (this-third-thingᵉ nᵉ pᵉ)))
      ( kᵉ) →
    Idᵉ
      ( map-inv-equivᵉ
        ( that-thingᵉ nᵉ)
        ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
          ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ))))
      ( k'ᵉ) →
    Idᵉ
      ( map-equivᵉ
        ( cases-map-quotient-aut-Finᵉ nᵉ
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( pᵉ))
          ( Dᵉ))
        ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ) (this-third-thingᵉ nᵉ pᵉ)))
      ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
        ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))
  cases-eq-map-quotient-aut-Finᵉ nᵉ pᵉ (inlᵉ Dᵉ) kᵉ k'ᵉ qᵉ rᵉ =
    reflects-map-reflecting-map-equivalence-relationᵉ
      ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( Dᵉ)
  cases-eq-map-quotient-aut-Finᵉ
    nᵉ pᵉ (inrᵉ NDᵉ) (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) qᵉ rᵉ =
    ex-falsoᵉ
      ( NDᵉ
        ( map-equivᵉ
          ( is-effective-is-set-quotientᵉ
            ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( is-set-quotient-equivalence-classᵉ
              ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
            ( this-third-thingᵉ nᵉ pᵉ)
            ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))
          ( is-injective-equivᵉ (inv-equivᵉ (that-thingᵉ nᵉ)) (qᵉ ∙ᵉ invᵉ rᵉ))))
  cases-eq-map-quotient-aut-Finᵉ nᵉ pᵉ (inrᵉ NDᵉ) (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) qᵉ rᵉ =
    ( apᵉ
      ( map-equivᵉ (that-thingᵉ nᵉ))
      ( apᵉ (map-equivᵉ (equiv-succ-Finᵉ 2ᵉ)) qᵉ ∙ᵉ invᵉ rᵉ)) ∙ᵉ
    ( apᵉ
      ( λ eᵉ →
        map-equivᵉ eᵉ
          ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
            ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))))
        ( right-inverse-law-equivᵉ (that-thingᵉ nᵉ))
  cases-eq-map-quotient-aut-Finᵉ nᵉ pᵉ (inrᵉ NDᵉ) (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) qᵉ rᵉ =
    ( apᵉ
      ( map-equivᵉ (that-thingᵉ nᵉ))
      ( apᵉ
        ( map-equivᵉ (equiv-succ-Finᵉ 2ᵉ))
        ( qᵉ) ∙ᵉ
        ( invᵉ rᵉ))) ∙ᵉ
    ( apᵉ
      ( λ eᵉ →
        map-equivᵉ eᵉ
          ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
            ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))))
    ( right-inverse-law-equivᵉ (that-thingᵉ nᵉ))
  cases-eq-map-quotient-aut-Finᵉ nᵉ pᵉ (inrᵉ NDᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) qᵉ rᵉ =
    ex-falsoᵉ
      ( NDᵉ
        ( map-equivᵉ
          ( is-effective-is-set-quotientᵉ
            ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( is-set-quotient-equivalence-classᵉ
              ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
            ( this-third-thingᵉ nᵉ pᵉ)
            ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))
          ( is-injective-equivᵉ (inv-equivᵉ (that-thingᵉ nᵉ)) (qᵉ ∙ᵉ invᵉ rᵉ))))

  eq-map-quotient-aut-Finᵉ :
    (nᵉ : ℕᵉ) (pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
    Idᵉ
      ( map-equivᵉ
        ( map-quotient-aut-Finᵉ nᵉ
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( pᵉ)))
        ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ) (this-third-thingᵉ nᵉ pᵉ)))
      ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
        ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))
  eq-map-quotient-aut-Finᵉ nᵉ pᵉ =
    cases-eq-map-quotient-aut-Finᵉ nᵉ pᵉ
      ( is-decidable-Rᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ
        ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( this-third-thingᵉ nᵉ pᵉ)
        ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ)))
        ( map-inv-equivᵉ
          ( that-thingᵉ nᵉ)
          ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ) (this-third-thingᵉ nᵉ pᵉ)))
        ( map-inv-equivᵉ
          ( that-thingᵉ nᵉ)
          ( quotient-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
            ( map-quotient-loop-Finᵉ nᵉ pᵉ (this-third-thingᵉ nᵉ pᵉ))))
        ( reflᵉ)
        ( reflᵉ)

  eq-map-quotient-aut-loop-equiv-is-set-quotientᵉ :
    (nᵉ : ℕᵉ) (pᵉ : type-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))) →
    Idᵉ
      ( map-quotient-aut-Finᵉ nᵉ
        ( map-hom-symmetric-group-loop-group-Setᵉ
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( pᵉ)))
      ( pr1ᵉ (centerᵉ (is-contr-equiv-quotientᵉ nᵉ pᵉ)))
  eq-map-quotient-aut-loop-equiv-is-set-quotientᵉ nᵉ pᵉ =
    eq-equiv-eq-one-value-equiv-is-set-quotientᵉ
      ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( quotient-reflecting-map-quotient-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
      ( is-set-quotient-equivalence-classᵉ
        ( Rᵉ (nᵉ +ℕᵉ 2ᵉ) (raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( inv-equivᵉ (that-thingᵉ nᵉ))
      ( map-quotient-loop-Finᵉ nᵉ pᵉ)
      ( λ {xᵉ} {yᵉ} →
        preserves-R-invertible-action-D-equivᵉ
          ( nᵉ +ℕᵉ 2ᵉ)
          ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-UU-Fin-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( pᵉ))
          ( xᵉ)
          ( yᵉ))
      ( map-equivᵉ
        ( map-quotient-aut-Finᵉ nᵉ
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( pᵉ))))
      ( this-third-thingᵉ nᵉ pᵉ)
      ( eq-map-quotient-aut-Finᵉ nᵉ pᵉ)
      ( is-equiv-map-equivᵉ (quotient-loop-Finᵉ nᵉ pᵉ))
      ( is-equiv-map-equivᵉ
        ( map-quotient-aut-Finᵉ nᵉ
          ( map-hom-symmetric-group-loop-group-Setᵉ
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( pᵉ))))

  eq-quotient-delooping-sign-loop-sign-homomorphismᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( quotient-delooping-sign-loopᵉ nᵉ)
        ( hom-inv-symmetric-group-loop-group-Setᵉ
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( comp-hom-Groupᵉ
            ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
            ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( hom-inv-symmetric-group-loop-group-Setᵉ
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( hom-symmetric-group-equiv-Setᵉ
              ( Fin-Setᵉ 2ᵉ)
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( that-thingᵉ nᵉ)))
          ( sign-homomorphismᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
        ( hom-inv-symmetric-group-equiv-Setᵉ
          ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
  eq-quotient-delooping-sign-loop-sign-homomorphismᵉ nᵉ =
    map-inv-equivᵉ
      ( equiv-ap-embᵉ
        ( restriction-generating-subset-Groupᵉ
          ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( is-transposition-permutation-Propᵉ {l2ᵉ = l1ᵉ})
          ( trᵉ
            ( λ sᵉ →
              is-generating-set-Groupᵉ
                ( symmetric-Groupᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ sᵉ))
                ( is-transposition-permutation-Propᵉ))
            ( eq-is-propᵉ (is-prop-is-setᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
            ( is-generated-transposition-symmetric-Fin-Levelᵉ
              ( nᵉ +ℕᵉ 2ᵉ)
              ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
      ( eq-htpyᵉ
        ( λ (fᵉ ,ᵉ sᵉ) →
          apply-universal-property-trunc-Propᵉ sᵉ
            ( Id-Propᵉ (set-Groupᵉ (loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( map-embᵉ
                ( restriction-generating-subset-Groupᵉ
                  ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( is-transposition-permutation-Propᵉ)
                  ( trᵉ
                    ( λ s₁ᵉ →
                      is-generating-set-Groupᵉ
                        ( symmetric-Groupᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ s₁ᵉ))
                        ( is-transposition-permutation-Propᵉ))
                    ( eq-is-propᵉ (is-prop-is-setᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                    ( is-generated-transposition-symmetric-Fin-Levelᵉ
                      ( nᵉ +ℕᵉ 2ᵉ)
                      ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                        unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                  ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
                ( comp-hom-Groupᵉ
                  ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( quotient-delooping-sign-loopᵉ nᵉ)
                  ( hom-inv-symmetric-group-loop-group-Setᵉ
                    ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                ( fᵉ ,ᵉ sᵉ))
              ( map-embᵉ
                ( restriction-generating-subset-Groupᵉ
                  ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( is-transposition-permutation-Propᵉ)
                  ( trᵉ
                    ( λ s₁ᵉ →
                      is-generating-set-Groupᵉ
                        ( symmetric-Groupᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ s₁ᵉ))
                        ( is-transposition-permutation-Propᵉ))
                    ( eq-is-propᵉ (is-prop-is-setᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                    ( is-generated-transposition-symmetric-Fin-Levelᵉ
                      ( nᵉ +ℕᵉ 2ᵉ)
                      ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                        unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                    ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
                  ( comp-hom-Groupᵉ
                    ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( comp-hom-Groupᵉ
                      ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                      ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( comp-hom-Groupᵉ
                        ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                        ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( hom-inv-symmetric-group-loop-group-Setᵉ
                          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( hom-symmetric-group-equiv-Setᵉ
                          ( Fin-Setᵉ 2ᵉ)
                          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                          ( that-thingᵉ nᵉ)))
                      ( sign-homomorphismᵉ (nᵉ +ℕᵉ 2ᵉ)
                        ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
                    ( hom-inv-symmetric-group-equiv-Setᵉ
                      ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
                      ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                      ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                ( fᵉ ,ᵉ sᵉ)))
            λ (Yᵉ ,ᵉ qᵉ) →
            ( eq-map-restriction-generating-subset-Groupᵉ
              ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( is-transposition-permutation-Propᵉ)
              ( trᵉ
                ( λ s₁ᵉ →
                  is-generating-set-Groupᵉ
                    ( symmetric-Groupᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ s₁ᵉ))
                    ( is-transposition-permutation-Propᵉ))
                ( eq-is-propᵉ (is-prop-is-setᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                ( is-generated-transposition-symmetric-Fin-Levelᵉ
                  ( nᵉ +ℕᵉ 2ᵉ)
                  ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                    unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
              ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( comp-hom-Groupᵉ
                ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( quotient-delooping-sign-loopᵉ nᵉ)
                ( hom-inv-symmetric-group-loop-group-Setᵉ
                  ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( fᵉ ,ᵉ sᵉ)) ∙ᵉ
            ( htpy-eq-hom-Groupᵉ
              ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( id-hom-Groupᵉ (loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( comp-hom-Groupᵉ
                ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( hom-inv-symmetric-group-loop-group-Setᵉ
                  ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( hom-symmetric-group-loop-group-Setᵉ
                  ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( invᵉ
                ( is-retraction-hom-inv-symmetric-group-loop-group-Setᵉ
                  ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( apᵉ
                ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( eq-pair-Σᵉ
                  ( invᵉ (eq-equivᵉ fᵉ))
                  ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
              ( apᵉ
                ( map-hom-Groupᵉ
                  ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( hom-inv-symmetric-group-loop-group-Setᵉ
                    ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
                ( eq-quotient-delooping-sign-loop-equiv-is-set-quotientᵉ nᵉ
                  ( invᵉ (eq-equivᵉ fᵉ)) ∙ᵉ
                  ( invᵉ
                    ( eq-map-quotient-aut-loop-equiv-is-set-quotientᵉ nᵉ
                      ( invᵉ (eq-equivᵉ fᵉ))))) ∙ᵉ
                ( apᵉ
                  ( λ gᵉ →
                    map-hom-Groupᵉ
                      ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( hom-inv-symmetric-group-loop-group-Setᵉ
                        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( map-quotient-aut-Finᵉ nᵉ gᵉ))
                  ( commutative-inv-map-hom-symmetric-group-loop-group-Setᵉ
                    ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( eq-equivᵉ fᵉ)
                    ( pr2ᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( pr2ᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∙ᵉ
                    ( apᵉ inv-equivᵉ
                      ( apᵉ
                        ( map-hom-symmetric-group-loop-group-Setᵉ
                          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( apᵉ
                          ( eq-equivᵉ)
                          ( invᵉ (inv-inv-equivᵉ fᵉ)) ∙ᵉ
                          ( invᵉ
                            ( commutativity-inv-eq-equivᵉ (inv-equivᵉ fᵉ)))) ∙ᵉ
                        ( htpy-eq-hom-Groupᵉ
                          ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( comp-hom-Groupᵉ
                            ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( hom-symmetric-group-loop-group-Setᵉ
                              ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( hom-inv-symmetric-group-loop-group-Setᵉ
                              ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                          ( id-hom-Groupᵉ
                            ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                          ( is-section-hom-inv-symmetric-group-loop-group-Setᵉ
                            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( inv-equivᵉ fᵉ) ∙ᵉ
                          ( apᵉ inv-equivᵉ (invᵉ qᵉ) ∙ᵉ
                            ( own-inverse-is-involutionᵉ
                              ( is-involution-map-transpositionᵉ Yᵉ))))))) ∙ᵉ
                  ( apᵉ
                    ( map-hom-Groupᵉ
                      ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( hom-inv-symmetric-group-loop-group-Setᵉ
                        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
                    ( apᵉ
                      ( map-quotient-aut-Finᵉ nᵉ)
                      ( own-inverse-is-involutionᵉ
                        ( is-involution-map-transpositionᵉ Yᵉ)) ∙ᵉ
                      ( eq-map-quotient-aut-fin-transpositionᵉ nᵉ Yᵉ ∙ᵉ
                        ( apᵉ
                          ( λ eᵉ →
                            (that-thingᵉ nᵉ) ∘eᵉ (eᵉ ∘eᵉ inv-equivᵉ ( that-thingᵉ nᵉ)))
                          ( invᵉ
                            ( eq-sign-homomorphism-transpositionᵉ
                              ( nᵉ +ℕᵉ 2ᵉ)
                              ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)
                              ( map-equivᵉ
                                ( equiv-universes-2-Element-Decidable-Subtypeᵉ
                                  ( Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                  ( l1ᵉ)
                                  ( lzeroᵉ))
                                ( transposition-conjugation-equivᵉ {l4ᵉ = l1ᵉ}
                                  ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                  ( Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                  ( inv-equivᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                  ( Yᵉ)))) ∙ᵉ
                            ( apᵉ
                              ( map-hom-Groupᵉ
                                ( symmetric-Groupᵉ
                                  ( set-UU-Finᵉ (nᵉ +ℕᵉ 2ᵉ)
                                    ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
                                ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                                ( sign-homomorphismᵉ
                                  ( nᵉ +ℕᵉ 2ᵉ)
                                  ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
                              ( invᵉ
                                ( eq-equiv-universes-transpositionᵉ
                                  ( Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                  ( l1ᵉ)
                                  ( lzero)
                                  ( transposition-conjugation-equivᵉ
                                    ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                    ( Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                    ( inv-equivᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                    ( Yᵉ))) ∙ᵉ
                                ( eq-htpy-equivᵉ
                                  ( correct-transposition-conjugation-equivᵉ
                                    ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                    ( Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                    ( inv-equivᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                    ( Yᵉ)) ∙ᵉ
                                  ( associative-comp-equivᵉ
                                    ( inv-equivᵉ
                                      ( inv-equivᵉ
                                        ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                                    ( transpositionᵉ Yᵉ)
                                    ( inv-equivᵉ
                                      ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∙ᵉ
                                    ( apᵉ
                                      ( λ eᵉ →
                                        ( inv-equivᵉ
                                          ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∘eᵉ
                                        ( transpositionᵉ Yᵉ ∘eᵉ eᵉ))
                                      ( inv-inv-equivᵉ
                                        ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∙ᵉ
                                      ( apᵉ
                                        ( λ eᵉ →
                                          ( inv-equivᵉ
                                            ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∘eᵉ
                                          ( eᵉ ∘eᵉ compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                                        ( qᵉ))))))))))) ∙ᵉ
                    ( invᵉ
                      ( eq-map-restriction-generating-subset-Groupᵉ
                        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( is-transposition-permutation-Propᵉ)
                        ( trᵉ
                          ( λ sᵉ →
                            is-generating-set-Groupᵉ
                              ( symmetric-Groupᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ sᵉ))
                              ( is-transposition-permutation-Propᵉ))
                          ( eq-is-propᵉ
                            ( is-prop-is-setᵉ (raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                          ( is-generated-transposition-symmetric-Fin-Levelᵉ
                            ( nᵉ +ℕᵉ 2ᵉ)
                            ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                              unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
                        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( comp-hom-Groupᵉ
                          ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( comp-hom-Groupᵉ
                            ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                            ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( comp-hom-Groupᵉ
                              ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                              ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                              ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                              ( hom-inv-symmetric-group-loop-group-Setᵉ
                                ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                              ( hom-symmetric-group-equiv-Setᵉ
                                ( Fin-Setᵉ 2ᵉ)
                                ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                                ( that-thingᵉ nᵉ)))
                            ( sign-homomorphismᵉ
                              ( nᵉ +ℕᵉ 2ᵉ)
                              ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
                          ( hom-inv-symmetric-group-equiv-Setᵉ
                            ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
                            ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                            ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
                        ( fᵉ ,ᵉ sᵉ)))))))))

  eq-quotient-delooping-loop-UU-Fin-Groupᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( hom-iso-Groupᵉ
          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( comp-iso-Groupᵉ
            ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( inv-iso-Groupᵉ
              ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
              ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
              ( iso-loop-group-fin-UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( iso-loop-group-equiv-Setᵉ
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ))
              ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ)))))
        ( quotient-delooping-sign-loopᵉ nᵉ))
      ( comp-hom-Groupᵉ
        ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( hom-group-hom-Concrete-Groupᵉ
          ( UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( UU-Fin-Groupᵉ l4ᵉ 2ᵉ)
          ( quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( hom-iso-Groupᵉ
          ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))))
  eq-quotient-delooping-loop-UU-Fin-Groupᵉ nᵉ =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ pᵉ →
          apᵉ
            ( λ rᵉ → eq-pair-Σᵉ rᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))
            ( apᵉ invᵉ
              ( invᵉ
                ( compute-eq-equiv-comp-equivᵉ
                  ( equiv-eqᵉ
                    ( invᵉ
                      ( apᵉ
                        ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                        ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))) ∘eᵉ
                    ( inv-equivᵉ
                      ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ))))
                  ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ))) ∙ᵉ
                ( right-whisker-concatᵉ
                  ( invᵉ
                    ( compute-eq-equiv-comp-equivᵉ
                      ( inv-equivᵉ
                        ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ)))
                      ( equiv-eqᵉ
                        ( invᵉ
                          ( apᵉ
                            ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                            ( eq-pair-Σᵉ pᵉ
                              ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))) ∙ᵉ
                    ( right-whisker-concatᵉ
                      ( invᵉ
                        ( commutativity-inv-eq-equivᵉ
                          ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ
                            inv-equivᵉ (that-thingᵉ nᵉ))))
                      ( eq-equivᵉ
                        ( equiv-eqᵉ
                          ( invᵉ
                            ( apᵉ
                              ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                              ( eq-pair-Σᵉ pᵉ
                                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))) ∙ᵉ
                      ( apᵉ
                        ( λ eᵉ →
                          invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ) ∙ᵉ
                            ( map-equivᵉ eᵉ
                              ( invᵉ
                                ( apᵉ
                                  ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                                  ( eq-pair-Σᵉ pᵉ
                                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))))
                        ( left-inverse-law-equivᵉ equiv-univalenceᵉ))))
                  ( eq-counting-equivalence-class-Rᵉ nᵉ))) ∙ᵉ
              ( distributive-inv-concatᵉ
                ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ) ∙ᵉ
                  ( invᵉ
                    ( apᵉ
                      ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                      ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))
                ( eq-counting-equivalence-class-Rᵉ nᵉ) ∙ᵉ
                ( left-whisker-concatᵉ
                  ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ))
                  ( distributive-inv-concatᵉ
                    ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ))
                    ( invᵉ
                      ( apᵉ
                        ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                        ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))) ∙ᵉ
                    ( right-whisker-concatᵉ
                      ( inv-invᵉ
                        ( apᵉ
                          ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                          ( eq-pair-Σᵉ pᵉ
                            ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))
                      ( invᵉ (invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ))) ∙ᵉ
                      ( left-whisker-concatᵉ
                        ( apᵉ
                          ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                          ( eq-pair-Σᵉ pᵉ
                            ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))
                        ( inv-invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ)))))))) ∙ᵉ
            ( ( apᵉ
              ( eq-pair-Σᵉ
                ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ) ∙ᵉ
                  ( apᵉ
                    ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                    ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)) ∙ᵉ
                    ( eq-counting-equivalence-class-Rᵉ nᵉ))))
              ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _))) ∙ᵉ
              ( interchange-concat-eq-pair-Σᵉ
                ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ))
                ( apᵉ
                  ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                  ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)) ∙ᵉ
                  ( eq-counting-equivalence-class-Rᵉ nᵉ))
                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
                ( _) ∙ᵉ
                ( left-whisker-concatᵉ
                  ( eq-pair-Σᵉ
                    ( invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ))
                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
                  ( interchange-concat-eq-pair-Σᵉ
                    ( apᵉ
                      ( equivalence-classᵉ ∘ᵉ Rᵉ (nᵉ +ℕᵉ 2ᵉ))
                      ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))
                    ( eq-counting-equivalence-class-Rᵉ nᵉ)
                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ) ∙ᵉ
                    ( right-whisker-concatᵉ
                      ( apᵉ
                        ( λ wᵉ → eq-pair-Σᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ))
                        { yᵉ =
                          pair-eq-Σᵉ
                            ( apᵉ
                              ( map-quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ))
                              ( eq-pair-Σᵉ pᵉ
                                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))}
                        ( eq-pair-Σᵉ
                          ( invᵉ
                            ( pr1-pair-eq-Σ-apᵉ _
                              ( eq-pair-Σᵉ pᵉ
                                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))
                          ( eq-is-propᵉ
                            ( is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _)))) ∙ᵉ
                          is-section-pair-eq-Σᵉ
                          ( map-quotient-delooping-signᵉ
                            ( nᵉ +ℕᵉ 2ᵉ)
                            ( Fin-UU-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( map-quotient-delooping-signᵉ
                            ( nᵉ +ℕᵉ 2ᵉ)
                            ( Fin-UU-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( apᵉ
                            ( map-quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ))
                            ( eq-pair-Σᵉ pᵉ
                              ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))
                      ( eq-pair-Σᵉ
                        ( eq-equivᵉ
                          ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ
                            inv-equivᵉ (that-thingᵉ nᵉ)))
                        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))))) ∙ᵉ
              ( right-whisker-concatᵉ
                ( apᵉ
                  ( eq-pair-Σᵉ (invᵉ (eq-counting-equivalence-class-Rᵉ nᵉ)))
                  ( eq-is-propᵉ (is-trunc-Idᵉ (is-prop-type-trunc-Propᵉ _ _))) ∙ᵉ
                  ( invᵉ
                    ( distributive-inv-eq-pair-Σᵉ
                      ( eq-counting-equivalence-class-Rᵉ nᵉ)
                      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))))
                ( ( apᵉ
                    ( map-quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ))
                    ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                  ( eq-pair-Σᵉ
                    ( eq-counting-equivalence-class-Rᵉ nᵉ)
                    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                ( invᵉ
                  ( eq-tr-type-Ωᵉ
                    ( eq-pair-Σᵉ
                      ( eq-counting-equivalence-class-Rᵉ nᵉ)
                      ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
                    ( apᵉ (map-quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ))
                      ( eq-pair-Σᵉ pᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))))))
      ( eq-is-propᵉ
        ( is-prop-preserves-mul-Semigroupᵉ
          ( semigroup-Groupᵉ (loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
          ( semigroup-Groupᵉ (group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ)))
          ( pr1ᵉ
            ( comp-hom-Groupᵉ
              ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
              ( hom-group-hom-Concrete-Groupᵉ
                ( UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                ( UU-Fin-Groupᵉ l4ᵉ 2ᵉ)
                ( quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( hom-iso-Groupᵉ
                ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( inv-iso-Groupᵉ
                  ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( iso-loop-group-fin-UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))))))

  symmetric-abstract-UU-fin-group-quotient-homᵉ :
    (nᵉ : ℕᵉ) →
    hom-Groupᵉ
      ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
  symmetric-abstract-UU-fin-group-quotient-homᵉ nᵉ =
    comp-hom-Groupᵉ
      ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
      ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( hom-iso-Groupᵉ
          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( comp-iso-Groupᵉ
            ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( inv-iso-Groupᵉ
              ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
              ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
              ( iso-loop-group-fin-UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( iso-loop-group-equiv-Setᵉ
              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
              ( raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ))
              ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ)))))
        ( hom-inv-symmetric-group-loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( hom-symmetric-group-equiv-Setᵉ
        ( Fin-Setᵉ 2ᵉ)
        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( that-thingᵉ nᵉ))

  eq-quotient-delooping-sign-homomorphismᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( comp-hom-Groupᵉ
          ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( hom-group-hom-Concrete-Groupᵉ
            ( UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( UU-Fin-Groupᵉ l4ᵉ 2ᵉ)
            ( quotient-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( hom-inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( symmetric-abstract-UU-fin-group-quotient-homᵉ nᵉ)
          ( sign-homomorphismᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
        ( hom-inv-symmetric-group-equiv-Setᵉ
          ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
  eq-quotient-delooping-sign-homomorphismᵉ nᵉ =
    ( apᵉ
      ( λ fᵉ →
        comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( fᵉ)
          ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( invᵉ (eq-quotient-delooping-loop-UU-Fin-Groupᵉ nᵉ))) ∙ᵉ
    ( associative-comp-hom-Groupᵉ
      ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
      ( hom-iso-Groupᵉ
        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
        ( comp-iso-Groupᵉ
          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
          ( iso-loop-group-equiv-Setᵉ
            ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ))
            ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ)))))
      ( quotient-delooping-sign-loopᵉ nᵉ)
      ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) ∙ᵉ
      ( apᵉ
        ( comp-hom-Groupᵉ
            ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
            ( hom-iso-Groupᵉ
              ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
              ( comp-iso-Groupᵉ
                ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
                ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                ( inv-iso-Groupᵉ
                  ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                  ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
                  ( iso-loop-group-fin-UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                ( iso-loop-group-equiv-Setᵉ
                  ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                  ( raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ))
                  ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ inv-equivᵉ (that-thingᵉ nᵉ))))))
        ( eq-quotient-delooping-sign-loop-sign-homomorphismᵉ nᵉ) ∙ᵉ
        ( eq-pair-eq-fiberᵉ
          ( eq-is-propᵉ
            ( is-prop-preserves-mul-Semigroupᵉ
              ( semigroup-Groupᵉ (symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( semigroup-Groupᵉ
                ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ)))
              ( pr1ᵉ
                ( comp-hom-Groupᵉ
                  ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                  ( comp-hom-Groupᵉ
                    ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
                    ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                    ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                    ( comp-hom-Groupᵉ
                      ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
                      ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                      ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                      ( comp-hom-Groupᵉ
                        ( symmetric-Groupᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                        ( hom-iso-Groupᵉ
                          ( loop-group-Setᵉ (quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                          ( comp-iso-Groupᵉ
                            ( loop-group-Setᵉ ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                            ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
                            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                            ( inv-iso-Groupᵉ
                              ( group-Concrete-Groupᵉ
                                ( UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                              ( loop-group-Setᵉ (raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ)))
                              ( iso-loop-group-fin-UU-Fin-Groupᵉ l4ᵉ 2ᵉ))
                            ( iso-loop-group-equiv-Setᵉ
                              ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                              ( raise-Setᵉ l4ᵉ (Fin-Setᵉ 2ᵉ))
                              ( compute-raise-Finᵉ l4ᵉ 2 ∘eᵉ
                                inv-equivᵉ (that-thingᵉ nᵉ)))))
                        ( hom-inv-symmetric-group-loop-group-Setᵉ
                          ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))))
                      ( hom-symmetric-group-equiv-Setᵉ
                        ( Fin-Setᵉ 2ᵉ)
                        ( quotient-set-Finᵉ (nᵉ +ℕᵉ 2ᵉ))
                        ( that-thingᵉ nᵉ)))
                    ( sign-homomorphismᵉ
                      ( nᵉ +ℕᵉ 2ᵉ)
                      ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
                  ( hom-inv-symmetric-group-equiv-Setᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
                    ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
                    ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))))))))
```

### General case for the construction of the delooping of sign homomorphism (Proposition 22)

```agda
module _
  { l1ᵉ l2ᵉ : Level}
  ( Qᵉ : (nᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ nᵉ → UU-Finᵉ l2ᵉ 2ᵉ)
  ( equiv-Q-fin-fin-2ᵉ :
    (nᵉ : ℕᵉ) →
    leq-ℕᵉ 2 nᵉ →
    Finᵉ 2 ≃ᵉ
    ( type-UU-Finᵉ 2
      ( Qᵉ nᵉ (raiseᵉ l1ᵉ (Finᵉ nᵉ) ,ᵉ unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ nᵉ)))))
  ( Q-transposition-swapᵉ : (nᵉ : ℕᵉ) →
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ l1ᵉ (raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    ( xᵉ : type-UU-Finᵉ 2
      ( Qᵉ ( nᵉ +ℕᵉ 2ᵉ)
          ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))) →
    ( xᵉ) ≠ᵉ
    ( map-equivᵉ
      ( action-equiv-family-over-subuniverseᵉ
        ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( type-UU-Finᵉ 2 ∘ᵉ Qᵉ (nᵉ +ℕᵉ 2ᵉ))
        ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( raiseᵉ l1ᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( transpositionᵉ Yᵉ))
      ( xᵉ)))
  where

  private
    equiv-Q-equivalence-classᵉ :
      (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) →
      type-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ) ≃ᵉ
      equivalence-classᵉ (Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
    equiv-Q-equivalence-classᵉ nᵉ Xᵉ =
      equiv-uniqueness-set-quotientᵉ
        ( Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
        ( set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))
        ( id-reflecting-map-Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
        ( is-set-quotient-id-Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
        ( equivalence-class-Setᵉ
          ( Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))))
        ( quotient-reflecting-map-equivalence-classᵉ
          ( Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))))
        ( is-set-quotient-equivalence-classᵉ
          ( Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))))

    equiv-fin-2-equivalence-classᵉ :
      (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ l1ᵉ nᵉ) → leq-ℕᵉ 2 nᵉ →
      Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ →
      Finᵉ 2 ≃ᵉ equivalence-classᵉ (Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
    equiv-fin-2-equivalence-classᵉ nᵉ Xᵉ Hᵉ hᵉ =
      trᵉ
        ( λ Yᵉ →
          Finᵉ 2 ≃ᵉ
          equivalence-classᵉ (Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Yᵉ))))
        ( eq-pair-Σᵉ
          ( eq-equivᵉ (hᵉ ∘eᵉ inv-equivᵉ (compute-raise-Finᵉ l1ᵉ nᵉ)))
          ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
        ( equiv-Q-equivalence-classᵉ nᵉ
          ( raiseᵉ l1ᵉ (Finᵉ nᵉ) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ l1ᵉ nᵉ)) ∘eᵉ equiv-Q-fin-fin-2ᵉ nᵉ Hᵉ)

  delooping-signᵉ :
    (nᵉ : ℕᵉ) → hom-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ nᵉ) (UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ)
  delooping-signᵉ =
    quotient-delooping-signᵉ
      ( λ nᵉ Xᵉ → type-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))
      ( λ nᵉ Xᵉ → Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
      ( λ nᵉ _ Xᵉ → has-decidable-equality-has-cardinalityᵉ 2 (pr2ᵉ (Qᵉ nᵉ Xᵉ)))
      ( equiv-fin-2-equivalence-classᵉ)
      ( λ nᵉ _ → map-equivᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ))
      ( λ nᵉ Yᵉ →
        Q-transposition-swapᵉ nᵉ Yᵉ
          ( pr1ᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ)))

  eq-delooping-sign-homomorphismᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ))
          ( hom-group-hom-Concrete-Groupᵉ
            ( UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ)
            ( delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( hom-inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc l2ᵉ) 2ᵉ))
          ( symmetric-abstract-UU-fin-group-quotient-homᵉ
            ( λ nᵉ Xᵉ → type-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))
            ( λ nᵉ Xᵉ → Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
            ( λ nᵉ _ Xᵉ → has-decidable-equality-has-cardinalityᵉ 2 (pr2ᵉ (Qᵉ nᵉ Xᵉ)))
            ( equiv-fin-2-equivalence-classᵉ)
            ( λ nᵉ _ → pr1ᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ))
            ( λ nᵉ Yᵉ →
              Q-transposition-swapᵉ nᵉ Yᵉ
                ( pr1ᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ)))
            ( nᵉ))
          ( sign-homomorphismᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
        ( hom-inv-symmetric-group-equiv-Setᵉ
          ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( compute-raise-Finᵉ l1ᵉ (nᵉ +ℕᵉ 2ᵉ))))
  eq-delooping-sign-homomorphismᵉ =
    eq-quotient-delooping-sign-homomorphismᵉ
      ( λ nᵉ Xᵉ → type-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ))
      ( λ nᵉ Xᵉ → Id-equivalence-relationᵉ (set-UU-Finᵉ 2 (Qᵉ nᵉ Xᵉ)))
      ( λ nᵉ _ Xᵉ → has-decidable-equality-has-cardinalityᵉ 2 (pr2ᵉ (Qᵉ nᵉ Xᵉ)))
      ( equiv-fin-2-equivalence-classᵉ)
      ( λ nᵉ _ → pr1ᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ))
      ( λ nᵉ Yᵉ →
        Q-transposition-swapᵉ nᵉ Yᵉ
          ( pr1ᵉ (equiv-Q-fin-fin-2ᵉ (nᵉ +ℕᵉ 2ᵉ) starᵉ) (zero-Finᵉ 1ᵉ)))
```

## See also

-ᵉ Definitionᵉ ofᵉ theᵉ deloopingᵉ ofᵉ theᵉ signᵉ homomorphismᵉ basedᵉ onᵉ Cartierᵉ
  [`finite-group-theory.cartier-delooping-sign-homomorphism`](finite-group-theory.cartier-delooping-sign-homomorphism.md).ᵉ
-ᵉ Definitionᵉ ofᵉ theᵉ deloopingᵉ ofᵉ theᵉ signᵉ homomorphismᵉ basedᵉ onᵉ Simpsonᵉ
  [`finite-group-theory.simpson-delooping-sign-homomorphism`](finite-group-theory.simpson-delooping-sign-homomorphism.md).ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ MR23ᵉ}}