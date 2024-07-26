# Cartier's delooping of the sign homomorphism

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.cartier-delooping-sign-homomorphismᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.delooping-sign-homomorphismᵉ
open import finite-group-theory.finite-type-groupsᵉ
open import finite-group-theory.sign-homomorphismᵉ
open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-equivalences-type-families-over-subuniversesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.loop-groups-setsᵉ
open import group-theory.symmetric-groupsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.orientations-complete-undirected-graphᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ deloopingᵉ ofᵉ theᵉ signᵉ homomorphismᵉ byᵉ using aᵉ methodᵉ ofᵉ Cartier.ᵉ

## Definitions

```agda
module _
  { lᵉ : Level}
  where

  not-even-difference-action-equiv-family-on-subuniverseᵉ :
    (nᵉ : ℕᵉ) (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( even-difference-orientation-Complete-Undirected-Graphᵉ
        ( nᵉ +ℕᵉ 2ᵉ)
        ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( orientation-aut-countᵉ
        ( nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( starᵉ)
        ( transpositionᵉ Yᵉ))
      ( map-equivᵉ
        ( action-equiv-family-over-subuniverseᵉ
          ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( orientation-Complete-Undirected-Graphᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( transpositionᵉ Yᵉ))
        ( orientation-aut-countᵉ
          (nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) starᵉ (transpositionᵉ Yᵉ))))
  not-even-difference-action-equiv-family-on-subuniverseᵉ nᵉ =
    trᵉ
      ( λ fᵉ →
        ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ
          ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))) →
            ¬ᵉ ( sim-equivalence-relationᵉ
              ( even-difference-orientation-Complete-Undirected-Graphᵉ
                ( nᵉ +ℕᵉ 2ᵉ)
                ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
                  unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( orientation-aut-countᵉ
                  ( nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( starᵉ)
                  ( transpositionᵉ Yᵉ))
              ( map-equivᵉ
                ( fᵉ
                  ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                    unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                    unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( transpositionᵉ Yᵉ))
                ( orientation-aut-countᵉ
                  ( nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( starᵉ)
                  ( transpositionᵉ Yᵉ)))))
      ( apᵉ pr1ᵉ
        { xᵉ =
          orientation-complete-undirected-graph-equivᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          preserves-id-equiv-orientation-complete-undirected-graph-equivᵉ
            ( nᵉ +ℕᵉ 2ᵉ)}
        { yᵉ =
          ( action-equiv-family-over-subuniverseᵉ
            ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( orientation-Complete-Undirected-Graphᵉ (nᵉ +ℕᵉ 2ᵉ))) ,ᵉ
          ( compute-id-equiv-action-equiv-family-over-subuniverseᵉ
            ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( orientation-Complete-Undirected-Graphᵉ (nᵉ +ℕᵉ 2ᵉ)))}
        ( eq-is-contrᵉ
          ( is-contr-equiv'ᵉ _
            ( distributive-Π-Σᵉ)
            ( is-contr-Πᵉ
              ( unique-action-equiv-family-over-subuniverseᵉ
                ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( orientation-Complete-Undirected-Graphᵉ (nᵉ +ℕᵉ 2ᵉ)))))))
      ( not-even-difference-orientation-aut-transposition-countᵉ
        (nᵉ +ℕᵉ 2 ,ᵉ (compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))) (starᵉ))

  cartier-delooping-signᵉ :
    (nᵉ : ℕᵉ) → hom-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ) (UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ)
  cartier-delooping-signᵉ =
    quotient-delooping-signᵉ
      ( orientation-Complete-Undirected-Graphᵉ)
      ( even-difference-orientation-Complete-Undirected-Graphᵉ)
      ( λ nᵉ _ →
        is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ nᵉ)
      ( equiv-fin-2-quotient-sign-equiv-Finᵉ)
      ( λ nᵉ →
        orientation-aut-countᵉ (nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) (starᵉ))
      ( not-even-difference-action-equiv-family-on-subuniverseᵉ)

  eq-cartier-delooping-sign-homomorphismᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ))
          ( hom-group-hom-Concrete-Groupᵉ
            ( UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ)
            ( cartier-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( hom-inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lᵉ) 2ᵉ))
          ( symmetric-abstract-UU-fin-group-quotient-homᵉ
            ( orientation-Complete-Undirected-Graphᵉ)
            ( even-difference-orientation-Complete-Undirected-Graphᵉ)
            ( λ nᵉ _ →
              is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ
                ( nᵉ))
            ( equiv-fin-2-quotient-sign-equiv-Finᵉ)
            ( λ nᵉ →
              orientation-aut-countᵉ
                ( nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                ( starᵉ))
            ( not-even-difference-action-equiv-family-on-subuniverseᵉ)
            ( nᵉ))
          ( sign-homomorphismᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
        ( hom-inv-symmetric-group-equiv-Setᵉ
          ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
  eq-cartier-delooping-sign-homomorphismᵉ =
    eq-quotient-delooping-sign-homomorphismᵉ
      ( orientation-Complete-Undirected-Graphᵉ)
      ( even-difference-orientation-Complete-Undirected-Graphᵉ)
      ( λ nᵉ _ →
        is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ nᵉ)
      ( equiv-fin-2-quotient-sign-equiv-Finᵉ)
      ( λ nᵉ →
        orientation-aut-countᵉ (nᵉ +ℕᵉ 2 ,ᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))) (starᵉ))
      ( not-even-difference-action-equiv-family-on-subuniverseᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MR23ᵉ}}