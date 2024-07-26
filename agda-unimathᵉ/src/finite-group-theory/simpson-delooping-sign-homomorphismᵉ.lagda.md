# Simpson's delooping of the sign homomorphism

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.simpson-delooping-sign-homomorphismᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.delooping-sign-homomorphismᵉ
open import finite-group-theory.finite-type-groupsᵉ
open import finite-group-theory.permutationsᵉ
open import finite-group-theory.sign-homomorphismᵉ
open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-equivalences-type-families-over-subuniversesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equivalence-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.involutionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.loop-groups-setsᵉ
open import group-theory.symmetric-groupsᵉ

open import lists.listsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Ideas

Weᵉ giveᵉ aᵉ definitionᵉ ofᵉ theᵉ deloopingᵉ ofᵉ theᵉ signᵉ homomorphismᵉ basedᵉ onᵉ aᵉ
suggestionᵉ byᵉ Alexᵉ Simpson.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ)
  where

  sign-comp-equivalence-relationᵉ :
    equivalence-relationᵉ lzero (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ)
  pr1ᵉ sign-comp-equivalence-relationᵉ fᵉ gᵉ =
    Id-Propᵉ
      ( Fin-Setᵉ 2ᵉ)
      ( zero-Finᵉ 1ᵉ)
      ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ gᵉ))
  pr1ᵉ (pr2ᵉ sign-comp-equivalence-relationᵉ) fᵉ =
    apᵉ pr1ᵉ
      { xᵉ =
        zero-Finᵉ 1 ,ᵉ
        unit-trunc-Propᵉ (nilᵉ ,ᵉ reflᵉ ,ᵉ left-inverse-law-equivᵉ fᵉ)}
      { yᵉ =
        centerᵉ
          ( is-contr-parity-transposition-permutationᵉ nᵉ
            (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ fᵉ))}
      ( eq-is-contrᵉ
        ( is-contr-parity-transposition-permutationᵉ nᵉ
          (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ fᵉ)))
  pr1ᵉ (pr2ᵉ (pr2ᵉ sign-comp-equivalence-relationᵉ)) fᵉ gᵉ Pᵉ =
    apᵉ pr1ᵉ
      { xᵉ =
        zero-Finᵉ 1 ,ᵉ
        unit-trunc-Propᵉ
          ( nilᵉ ,ᵉ reflᵉ ,ᵉ left-inverse-law-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ))}
      { yᵉ =
        centerᵉ
          ( is-contr-parity-transposition-permutationᵉ nᵉ
            ( Fin-UU-Fin'ᵉ nᵉ)
            ( inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ) ∘eᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ)))}
      ( eq-is-contrᵉ
        ( is-contr-parity-transposition-permutationᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ)
          ( inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ) ∘eᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ)))) ∙ᵉ
      ( preserves-add-sign-homomorphism-Fin-twoᵉ nᵉ
        ( Fin-UU-Fin'ᵉ nᵉ)
        ( inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ))
        ( inv-equivᵉ fᵉ ∘eᵉ gᵉ) ∙ᵉ
        ( apᵉ
          ( add-Finᵉ 2
            ( sign-homomorphism-Fin-twoᵉ nᵉ
              (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ))))
          ( invᵉ Pᵉ) ∙ᵉ
          ( apᵉ
            ( mod-two-ℕᵉ ∘ᵉ
              ( nat-Finᵉ 2
                ( sign-homomorphism-Fin-twoᵉ nᵉ
                  (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ)))) +ℕᵉ_)
            ( is-zero-nat-zero-Finᵉ {kᵉ = 1ᵉ}) ∙ᵉ
            ( is-section-nat-Finᵉ 1
              ( sign-homomorphism-Fin-twoᵉ nᵉ
                (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ (inv-equivᵉ fᵉ ∘eᵉ gᵉ))) ∙ᵉ
              ( apᵉ
                ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ))
                ( distributive-inv-comp-equivᵉ gᵉ (inv-equivᵉ fᵉ) ∙ᵉ
                  apᵉ (inv-equivᵉ gᵉ ∘eᵉ_) (inv-inv-equivᵉ fᵉ)))))))
  pr2ᵉ (pr2ᵉ (pr2ᵉ sign-comp-equivalence-relationᵉ)) fᵉ gᵉ hᵉ Qᵉ Pᵉ =
    ( apᵉ mod-two-ℕᵉ
      ( apᵉ
        ( zero-ℕᵉ +ℕᵉ_)
        ( invᵉ (is-zero-nat-zero-Finᵉ {kᵉ = 1ᵉ}) ∙ᵉ apᵉ (nat-Finᵉ 2ᵉ) Qᵉ) ∙ᵉ
        ( apᵉ
          ( _+ℕᵉ
            ( nat-Finᵉ 2
              ( sign-homomorphism-Fin-twoᵉ nᵉ
                (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ gᵉ ∘eᵉ hᵉ))))
          ( invᵉ (is-zero-nat-zero-Finᵉ {kᵉ = 1ᵉ}) ∙ᵉ apᵉ (nat-Finᵉ 2ᵉ) Pᵉ)))) ∙ᵉ
    ( invᵉ
      ( preserves-add-sign-homomorphism-Fin-twoᵉ nᵉ
        (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ gᵉ) (inv-equivᵉ gᵉ ∘eᵉ hᵉ)) ∙ᵉ
      ( apᵉ
        ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ))
        ( associative-comp-equivᵉ (inv-equivᵉ gᵉ ∘eᵉ hᵉ) gᵉ (inv-equivᵉ fᵉ) ∙ᵉ
          ( apᵉ
            ( inv-equivᵉ fᵉ ∘eᵉ_)
            ( invᵉ (associative-comp-equivᵉ hᵉ (inv-equivᵉ gᵉ) gᵉ) ∙ᵉ
              ( apᵉ (_∘eᵉ hᵉ) (right-inverse-law-equivᵉ gᵉ) ∙ᵉ
                left-unit-law-equivᵉ hᵉ))))))

  is-decidable-sign-comp-equivalence-relationᵉ :
    (fᵉ gᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
    is-decidableᵉ (sim-equivalence-relationᵉ sign-comp-equivalence-relationᵉ fᵉ gᵉ)
  is-decidable-sign-comp-equivalence-relationᵉ fᵉ gᵉ =
    has-decidable-equality-is-finiteᵉ
      ( is-finite-Finᵉ 2ᵉ)
      ( zero-Finᵉ 1ᵉ)
      ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ gᵉ))

  quotient-sign-compᵉ : UUᵉ (lsuc lzero ⊔ lᵉ)
  quotient-sign-compᵉ = equivalence-classᵉ sign-comp-equivalence-relationᵉ

  quotient-sign-comp-Setᵉ : Setᵉ (lsuc lzero ⊔ lᵉ)
  quotient-sign-comp-Setᵉ = equivalence-class-Setᵉ sign-comp-equivalence-relationᵉ

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  (eXᵉ : countᵉ Xᵉ) (ineqᵉ : leq-ℕᵉ 2 (number-of-elements-countᵉ eXᵉ))
  where

  private
    transposition-eXᵉ : Finᵉ (pr1ᵉ eXᵉ) ≃ᵉ Finᵉ (pr1ᵉ eXᵉ)
    transposition-eXᵉ =
      transpositionᵉ
        ( standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-Finᵉ (number-of-elements-countᵉ eXᵉ))
          ( pr2ᵉ
            ( pr2ᵉ
              ( two-distinct-elements-leq-2-Finᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( ineqᵉ)))))

  private abstract
    lemmaᵉ :
      Idᵉ
        ( inrᵉ starᵉ)
        ( sign-homomorphism-Fin-twoᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
          ( inv-equivᵉ (equiv-countᵉ eXᵉ) ∘eᵉ (equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ)))
    lemmaᵉ =
      ( invᵉ
        ( eq-sign-homomorphism-Fin-two-transpositionᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-Finᵉ (number-of-elements-countᵉ eXᵉ))
            ( pr2ᵉ
              ( pr2ᵉ
                ( two-distinct-elements-leq-2-Finᵉ
                  (number-of-elements-countᵉ eXᵉ) (ineqᵉ))))))) ∙ᵉ
        ( apᵉ
          ( sign-homomorphism-Fin-twoᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ)))
          ( invᵉ (left-unit-law-equivᵉ transposition-eXᵉ) ∙ᵉ
            ( apᵉ
              ( _∘eᵉ transposition-eXᵉ)
              ( invᵉ (left-inverse-law-equivᵉ (equiv-countᵉ eXᵉ))) ∙ᵉ
              ( associative-comp-equivᵉ
                ( transposition-eXᵉ)
                ( equiv-countᵉ eXᵉ)
                ( inv-equivᵉ (equiv-countᵉ eXᵉ))))))

  not-sign-comp-transposition-countᵉ :
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( sign-comp-equivalence-relationᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
      ( transpositionᵉ Yᵉ ∘eᵉ equiv-countᵉ eXᵉ)
      ( transpositionᵉ Yᵉ ∘eᵉ (transpositionᵉ Yᵉ ∘eᵉ equiv-countᵉ eXᵉ)))
  not-sign-comp-transposition-countᵉ Yᵉ Pᵉ =
    neq-inl-inrᵉ
      ( Pᵉ ∙ᵉ
        ( apᵉ
          ( sign-homomorphism-Fin-twoᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ)))
          ( apᵉ
            ( inv-equivᵉ (transpositionᵉ Yᵉ ∘eᵉ equiv-countᵉ eXᵉ) ∘eᵉ_)
            ( invᵉ
              ( associative-comp-equivᵉ
                (equiv-countᵉ eXᵉ) (transpositionᵉ Yᵉ) (transpositionᵉ Yᵉ)) ∙ᵉ
              ( apᵉ
                ( _∘eᵉ equiv-countᵉ eXᵉ)
                ( eq-htpy-equivᵉ (is-involution-map-transpositionᵉ Yᵉ)) ∙ᵉ
                ( left-unit-law-equivᵉ (equiv-countᵉ eXᵉ)))) ∙ᵉ
            ( apᵉ
              ( _∘eᵉ equiv-countᵉ eXᵉ)
              ( distributive-inv-comp-equivᵉ
                (equiv-countᵉ eXᵉ) (transpositionᵉ Yᵉ)) ∙ᵉ
              ( associative-comp-equivᵉ
                ( equiv-countᵉ eXᵉ)
                ( inv-equivᵉ (transpositionᵉ Yᵉ))
                ( inv-equivᵉ (equiv-countᵉ eXᵉ)) ∙ᵉ
                ( apᵉ
                  ( λ hᵉ → inv-equivᵉ (equiv-countᵉ eXᵉ) ∘eᵉ (hᵉ ∘eᵉ equiv-countᵉ eXᵉ))
                  ( own-inverse-is-involutionᵉ
                    ( is-involution-map-transpositionᵉ Yᵉ)) ∙ᵉ
                  ( apᵉ
                    ( λ hᵉ →
                      inv-equivᵉ (equiv-countᵉ eXᵉ) ∘eᵉ (transpositionᵉ Yᵉ ∘eᵉ hᵉ))
                    ( invᵉ (inv-inv-equivᵉ (equiv-countᵉ eXᵉ)))))))) ∙ᵉ
          ( preserves-conjugation-sign-homomorphism-Fin-twoᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))
            ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
            ( transpositionᵉ Yᵉ)
            ( inv-equivᵉ (equiv-countᵉ eXᵉ)) ∙ᵉ
            ( eq-sign-homomorphism-Fin-two-transpositionᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))
              ( Yᵉ)))))

  inv-Fin-2-quotient-sign-comp-countᵉ :
    ( Tᵉ : quotient-sign-compᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))) →
    is-decidableᵉ
      ( is-in-equivalence-classᵉ
        ( sign-comp-equivalence-relationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( Tᵉ)
        ( equiv-countᵉ eXᵉ)) →
    Finᵉ 2
  inv-Fin-2-quotient-sign-comp-countᵉ Tᵉ (inlᵉ Pᵉ) = inlᵉ (inrᵉ starᵉ)
  inv-Fin-2-quotient-sign-comp-countᵉ Tᵉ (inrᵉ NPᵉ) = inrᵉ starᵉ

  equiv-Fin-2-quotient-sign-comp-countᵉ :
    Finᵉ 2 ≃ᵉ
    quotient-sign-compᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))
  pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ (inlᵉ (inrᵉ starᵉ)) =
    classᵉ
      ( sign-comp-equivalence-relationᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
      ( equiv-countᵉ eXᵉ)
  pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ (inrᵉ starᵉ) =
    classᵉ
      ( sign-comp-equivalence-relationᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
      ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ)
  pr2ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ =
    is-equiv-is-invertibleᵉ
      ( λ Tᵉ →
        inv-Fin-2-quotient-sign-comp-countᵉ Tᵉ
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( sign-comp-equivalence-relationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( λ aᵉ bᵉ →
              has-decidable-equality-Finᵉ 2
                ( zero-Finᵉ 1ᵉ)
                ( sign-homomorphism-Fin-twoᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
                  ( inv-equivᵉ aᵉ ∘eᵉ bᵉ)))
            ( Tᵉ)
            ( equiv-countᵉ eXᵉ)))
      ( λ Tᵉ →
        retraction-Fin-2-quotient-sign-comp-countᵉ Tᵉ
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( sign-comp-equivalence-relationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( λ aᵉ bᵉ →
              has-decidable-equality-Finᵉ 2
                ( zero-Finᵉ 1ᵉ)
                ( sign-homomorphism-Fin-twoᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
                  ( inv-equivᵉ aᵉ ∘eᵉ bᵉ)))
            ( Tᵉ)
            ( equiv-countᵉ eXᵉ)))
      ( λ kᵉ →
        section-Fin-2-quotient-sign-comp-countᵉ kᵉ
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( sign-comp-equivalence-relationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( λ aᵉ bᵉ →
              has-decidable-equality-Finᵉ 2
                ( zero-Finᵉ 1ᵉ)
                ( sign-homomorphism-Fin-twoᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
                  ( inv-equivᵉ aᵉ ∘eᵉ bᵉ)))
            ( pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ kᵉ)
            ( equiv-countᵉ eXᵉ)))
    where
    cases-retraction-Fin-2-quotient-sign-comp-countᵉ :
      ( Tᵉ : quotient-sign-compᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))) →
      ¬ᵉ ( is-in-equivalence-classᵉ
        ( sign-comp-equivalence-relationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( Tᵉ)
        ( equiv-countᵉ eXᵉ)) →
      ( fᵉ : Finᵉ (number-of-elements-countᵉ eXᵉ) ≃ᵉ Xᵉ) →
      Idᵉ
        ( classᵉ
          ( sign-comp-equivalence-relationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( fᵉ))
        ( Tᵉ) →
      ( kᵉ : Finᵉ 2ᵉ) →
      Idᵉ
        ( kᵉ)
        ( sign-homomorphism-Fin-twoᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
          ( inv-equivᵉ fᵉ ∘eᵉ equiv-countᵉ eXᵉ)) →
      is-in-equivalence-classᵉ
        ( sign-comp-equivalence-relationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( Tᵉ)
        ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ)
    cases-retraction-Fin-2-quotient-sign-comp-countᵉ
      Tᵉ NPᵉ fᵉ pᵉ (inlᵉ (inrᵉ starᵉ)) qᵉ =
      ex-falsoᵉ
        ( NPᵉ
          ( trᵉ
            ( λ xᵉ →
              is-in-equivalence-classᵉ
                ( sign-comp-equivalence-relationᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( xᵉ)
                ( equiv-countᵉ eXᵉ))
            ( pᵉ)
            ( qᵉ)))
    cases-retraction-Fin-2-quotient-sign-comp-countᵉ Tᵉ NPᵉ fᵉ pᵉ (inrᵉ starᵉ) qᵉ =
      trᵉ
        ( λ xᵉ →
          is-in-equivalence-classᵉ
            ( sign-comp-equivalence-relationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( xᵉ)
            ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ))
        ( pᵉ)
        ( eq-mod-succ-cong-ℕᵉ 1 0 2 (cong-zero-ℕ'ᵉ 2ᵉ) ∙ᵉ
          ( ap-add-Finᵉ 2 qᵉ lemmaᵉ ∙ᵉ
            ( invᵉ
              ( preserves-add-sign-homomorphism-Fin-twoᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
                ( inv-equivᵉ fᵉ ∘eᵉ equiv-countᵉ eXᵉ)
                ( inv-equivᵉ (equiv-countᵉ eXᵉ) ∘eᵉ
                  ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ))) ∙ᵉ
              ( apᵉ
                ( sign-homomorphism-Fin-twoᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ)))
                ( associative-comp-equivᵉ
                  ( inv-equivᵉ (equiv-countᵉ eXᵉ) ∘eᵉ
                    ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ))
                  ( equiv-countᵉ eXᵉ)
                  ( inv-equivᵉ fᵉ) ∙ᵉ
                  ( apᵉ
                    ( λ hᵉ → inv-equivᵉ fᵉ ∘eᵉ (equiv-countᵉ eXᵉ ∘eᵉ hᵉ))
                    ( invᵉ
                      ( associative-comp-equivᵉ
                        ( transposition-eXᵉ)
                        ( equiv-countᵉ eXᵉ)
                        ( inv-equivᵉ (equiv-countᵉ eXᵉ))) ∙ᵉ
                      ( apᵉ
                        ( _∘eᵉ transposition-eXᵉ)
                        ( left-inverse-law-equivᵉ (equiv-countᵉ eXᵉ)) ∙ᵉ
                        ( left-unit-law-equivᵉ transposition-eXᵉ)))))))))
    retraction-Fin-2-quotient-sign-comp-countᵉ :
      ( Tᵉ : quotient-sign-compᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))) →
      ( Hᵉ : is-decidableᵉ
        ( is-in-equivalence-classᵉ
          ( sign-comp-equivalence-relationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( Tᵉ)
          ( equiv-countᵉ eXᵉ))) →
      Idᵉ
        ( pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ
          ( inv-Fin-2-quotient-sign-comp-countᵉ Tᵉ Hᵉ))
        ( Tᵉ)
    retraction-Fin-2-quotient-sign-comp-countᵉ Tᵉ (inlᵉ Pᵉ) =
      eq-effective-quotient'ᵉ
        ( sign-comp-equivalence-relationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( equiv-countᵉ eXᵉ)
        ( Tᵉ)
        ( Pᵉ)
    retraction-Fin-2-quotient-sign-comp-countᵉ Tᵉ (inrᵉ NPᵉ) =
      eq-effective-quotient'ᵉ
        ( sign-comp-equivalence-relationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ)
        ( Tᵉ)
        ( apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ Tᵉ)
          ( pairᵉ
            ( is-in-equivalence-classᵉ
              ( sign-comp-equivalence-relationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( Tᵉ)
              ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ))
            ( is-prop-is-in-equivalence-classᵉ
              ( sign-comp-equivalence-relationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( Tᵉ)
              ( equiv-countᵉ eXᵉ ∘eᵉ transposition-eXᵉ)))
          ( λ (tᵉ ,ᵉ pᵉ) →
            cases-retraction-Fin-2-quotient-sign-comp-countᵉ Tᵉ NPᵉ tᵉ
              ( invᵉ
                ( eq-has-same-elements-equivalence-classᵉ
                  ( sign-comp-equivalence-relationᵉ
                    ( number-of-elements-countᵉ eXᵉ)
                    ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( Tᵉ)
                  ( classᵉ
                    ( sign-comp-equivalence-relationᵉ
                      ( number-of-elements-countᵉ eXᵉ)
                      ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                    ( tᵉ))
                  ( pᵉ)))
              ( sign-homomorphism-Fin-twoᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ))
                ( inv-equivᵉ tᵉ ∘eᵉ equiv-countᵉ eXᵉ))
              ( reflᵉ)))
    section-Fin-2-quotient-sign-comp-countᵉ :
      ( kᵉ : Finᵉ 2ᵉ) →
      ( Dᵉ : is-decidableᵉ
        ( is-in-equivalence-classᵉ
          ( sign-comp-equivalence-relationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ kᵉ)
          ( equiv-countᵉ eXᵉ))) →
      Idᵉ
        ( inv-Fin-2-quotient-sign-comp-countᵉ
          (pr1ᵉ equiv-Fin-2-quotient-sign-comp-countᵉ kᵉ) (Dᵉ))
        ( kᵉ)
    section-Fin-2-quotient-sign-comp-countᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ Dᵉ) = reflᵉ
    section-Fin-2-quotient-sign-comp-countᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ NDᵉ) =
      ex-falsoᵉ
        ( NDᵉ
          ( refl-equivalence-relationᵉ
            ( sign-comp-equivalence-relationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( pr2ᵉ eXᵉ)))
    section-Fin-2-quotient-sign-comp-countᵉ (inrᵉ starᵉ) (inlᵉ Dᵉ) =
      ex-falsoᵉ
        ( neq-inr-inlᵉ
          ( lemmaᵉ ∙ᵉ
            ( invᵉ
              ( Dᵉ ∙ᵉ
                ( apᵉ
                  ( sign-homomorphism-Fin-twoᵉ
                    ( number-of-elements-countᵉ eXᵉ)
                    ( Fin-UU-Fin'ᵉ (number-of-elements-countᵉ eXᵉ)))
                  ( apᵉ
                    ( _∘eᵉ equiv-countᵉ eXᵉ)
                    ( distributive-inv-comp-equivᵉ
                      ( transposition-eXᵉ)
                      ( equiv-countᵉ eXᵉ)) ∙ᵉ
                    ( associative-comp-equivᵉ
                      ( equiv-countᵉ eXᵉ)
                      ( inv-equivᵉ (equiv-countᵉ eXᵉ))
                      ( inv-equivᵉ transposition-eXᵉ) ∙ᵉ
                      ( apᵉ
                        ( inv-equivᵉ transposition-eXᵉ ∘eᵉ_)
                        ( left-inverse-law-equivᵉ (equiv-countᵉ eXᵉ)) ∙ᵉ
                        ( right-unit-law-equivᵉ (inv-equivᵉ transposition-eXᵉ) ∙ᵉ
                          ( own-inverse-is-involutionᵉ
                            ( is-involution-map-transpositionᵉ
                              ( standard-2-Element-Decidable-Subtypeᵉ
                                ( has-decidable-equality-Finᵉ
                                  ( number-of-elements-countᵉ eXᵉ))
                                ( pr2ᵉ
                                  ( pr2ᵉ
                                    ( two-distinct-elements-leq-2-Finᵉ
                                      ( number-of-elements-countᵉ eXᵉ)
                                      ( ineqᵉ)))))) ∙ᵉ
                            ( invᵉ (left-unit-law-equivᵉ transposition-eXᵉ) ∙ᵉ
                              ( apᵉ
                                  ( _∘eᵉ transposition-eXᵉ)
                                  ( invᵉ
                                    ( left-inverse-law-equivᵉ
                                      ( equiv-countᵉ eXᵉ))) ∙ᵉ
                                ( associative-comp-equivᵉ
                                  ( transposition-eXᵉ)
                                  ( equiv-countᵉ eXᵉ)
                                  ( inv-equivᵉ (equiv-countᵉ eXᵉ)))))))))))))))
    section-Fin-2-quotient-sign-comp-countᵉ (inrᵉ starᵉ) (inrᵉ NDᵉ) = reflᵉ

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ) (ineqᵉ : leq-ℕᵉ 2 nᵉ)
  where

  equiv-fin-2-quotient-sign-comp-equiv-Finᵉ :
    (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) → (Finᵉ 2 ≃ᵉ quotient-sign-compᵉ nᵉ Xᵉ)
  equiv-fin-2-quotient-sign-comp-equiv-Finᵉ hᵉ =
    trᵉ
      ( λ eᵉ → Finᵉ 2 ≃ᵉ quotient-sign-compᵉ nᵉ (type-UU-Finᵉ nᵉ Xᵉ ,ᵉ eᵉ))
      ( all-elements-equal-type-trunc-Propᵉ
        ( unit-trunc-Propᵉ (equiv-countᵉ (nᵉ ,ᵉ hᵉ))) (pr2ᵉ Xᵉ))
      ( equiv-Fin-2-quotient-sign-comp-countᵉ (nᵉ ,ᵉ hᵉ) ineqᵉ)
```

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ)
  where

  map-simpson-comp-equivᵉ :
    (Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ) →
    (type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
    (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) → (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ)
  map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ fᵉ = eᵉ ∘eᵉ fᵉ

  simpson-comp-equivᵉ :
    (Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ) →
    (type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
    (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) ≃ᵉ (Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ)
  pr1ᵉ (simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ) = map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ
  pr2ᵉ (simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ) =
    is-equiv-is-invertibleᵉ
      ( map-simpson-comp-equivᵉ X'ᵉ Xᵉ (inv-equivᵉ eᵉ))
      ( λ fᵉ →
        ( invᵉ (associative-comp-equivᵉ fᵉ (inv-equivᵉ eᵉ) eᵉ)) ∙ᵉ
        ( apᵉ (_∘eᵉ fᵉ) (right-inverse-law-equivᵉ eᵉ) ∙ᵉ left-unit-law-equivᵉ fᵉ))
      ( λ fᵉ →
        ( invᵉ (associative-comp-equivᵉ fᵉ eᵉ (inv-equivᵉ eᵉ))) ∙ᵉ
        ( apᵉ (_∘eᵉ fᵉ) (left-inverse-law-equivᵉ eᵉ) ∙ᵉ left-unit-law-equivᵉ fᵉ))

  abstract
    preserves-id-equiv-simpson-comp-equivᵉ :
      (Xᵉ : UU-Finᵉ lᵉ nᵉ) → Idᵉ (simpson-comp-equivᵉ Xᵉ Xᵉ id-equivᵉ) id-equivᵉ
    preserves-id-equiv-simpson-comp-equivᵉ Xᵉ =
      eq-htpy-equivᵉ left-unit-law-equivᵉ

    preserves-comp-simpson-comp-equivᵉ :
      ( Xᵉ Yᵉ Zᵉ : UU-Finᵉ lᵉ nᵉ)
      ( eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ Yᵉ) →
      ( fᵉ : type-UU-Finᵉ nᵉ Yᵉ ≃ᵉ type-UU-Finᵉ nᵉ Zᵉ) →
      Idᵉ
        ( simpson-comp-equivᵉ Xᵉ Zᵉ (fᵉ ∘eᵉ eᵉ))
        ( simpson-comp-equivᵉ Yᵉ Zᵉ fᵉ ∘eᵉ simpson-comp-equivᵉ Xᵉ Yᵉ eᵉ)
    preserves-comp-simpson-comp-equivᵉ Xᵉ Yᵉ Zᵉ eᵉ fᵉ =
      eq-htpy-equivᵉ
        ( λ hᵉ → associative-comp-equivᵉ hᵉ eᵉ fᵉ)

  private
    lemma-sign-compᵉ :
      ( Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ)
      ( eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
      ( fᵉ f'ᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      Idᵉ
        ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ) (inv-equivᵉ fᵉ ∘eᵉ f'ᵉ))
        ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ)
          ( inv-equivᵉ ( map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ fᵉ) ∘eᵉ
            map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ f'ᵉ))
    lemma-sign-compᵉ Xᵉ X'ᵉ eᵉ fᵉ f'ᵉ =
      apᵉ
        ( sign-homomorphism-Fin-twoᵉ nᵉ (Fin-UU-Fin'ᵉ nᵉ))
        ( apᵉ
          ( inv-equivᵉ fᵉ ∘eᵉ_)
          ( invᵉ (left-unit-law-equivᵉ f'ᵉ) ∙ᵉ
            ( apᵉ (_∘eᵉ f'ᵉ) (invᵉ (left-inverse-law-equivᵉ eᵉ)) ∙ᵉ
              ( associative-comp-equivᵉ f'ᵉ eᵉ (inv-equivᵉ eᵉ)))) ∙ᵉ
          ( ( invᵉ
              ( associative-comp-equivᵉ (eᵉ ∘eᵉ f'ᵉ) (inv-equivᵉ eᵉ) (inv-equivᵉ fᵉ))) ∙ᵉ
            ( apᵉ
              ( _∘eᵉ map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ f'ᵉ)
              ( invᵉ (distributive-inv-comp-equivᵉ fᵉ eᵉ)))))

  preserves-sign-comp-simpson-comp-equivᵉ :
    ( Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ)
    ( eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
    ( fᵉ f'ᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
    ( sim-equivalence-relationᵉ (sign-comp-equivalence-relationᵉ nᵉ Xᵉ) fᵉ f'ᵉ ↔ᵉ
      sim-equivalence-relationᵉ
        ( sign-comp-equivalence-relationᵉ nᵉ X'ᵉ)
        ( map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ fᵉ)
        ( map-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ f'ᵉ))
  pr1ᵉ (preserves-sign-comp-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ fᵉ f'ᵉ) =
    _∙ᵉ lemma-sign-compᵉ Xᵉ X'ᵉ eᵉ fᵉ f'ᵉ
  pr2ᵉ (preserves-sign-comp-simpson-comp-equivᵉ Xᵉ X'ᵉ eᵉ fᵉ f'ᵉ) =
    _∙ᵉ invᵉ (lemma-sign-compᵉ Xᵉ X'ᵉ eᵉ fᵉ f'ᵉ)
```

```agda
module _
  {lᵉ : Level}
  where

  sign-comp-aut-succ-succ-Finᵉ :
    (nᵉ : ℕᵉ) →
    type-Groupᵉ (symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    Finᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))
  sign-comp-aut-succ-succ-Finᵉ nᵉ = _∘eᵉ compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ))

  not-action-equiv-family-on-subuniverse-transpositionᵉ :
    ( nᵉ : ℕᵉ) →
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ
      ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( sign-comp-equivalence-relationᵉ (nᵉ +ℕᵉ 2ᵉ)
        ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( sign-comp-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))
      ( map-equivᵉ
        ( action-equiv-family-over-subuniverseᵉ
          ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( λ Xᵉ → Finᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ pr1ᵉ Xᵉ)
          ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
            unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( transpositionᵉ Yᵉ))
        ( sign-comp-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))))
  not-action-equiv-family-on-subuniverse-transpositionᵉ nᵉ =
    trᵉ
      ( λ fᵉ →
        ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ
          ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))) →
            ¬ᵉ ( sim-equivalence-relationᵉ
              ( sign-comp-equivalence-relationᵉ
                ( nᵉ +ℕᵉ 2ᵉ)
                ( raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
                  unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
              ( sign-comp-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ))
              ( map-equivᵉ
                ( fᵉ
                  ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                    unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)) ,ᵉ
                    unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( transpositionᵉ Yᵉ))
                ( sign-comp-aut-succ-succ-Finᵉ nᵉ (transpositionᵉ Yᵉ)))))
      ( apᵉ pr1ᵉ
        { xᵉ =
          simpson-comp-equivᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ
          preserves-id-equiv-simpson-comp-equivᵉ (nᵉ +ℕᵉ 2ᵉ)}
        { yᵉ =
          ( action-equiv-family-over-subuniverseᵉ
            ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( λ Xᵉ → Finᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ type-UU-Finᵉ (nᵉ +ℕᵉ 2ᵉ) Xᵉ) ,ᵉ
            ( compute-id-equiv-action-equiv-family-over-subuniverseᵉ
              ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
              ( λ Xᵉ → Finᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ type-UU-Finᵉ (nᵉ +ℕᵉ 2ᵉ) Xᵉ)))}
        ( eq-is-contrᵉ
          ( is-contr-equiv'ᵉ _
            ( distributive-Π-Σᵉ)
            ( is-contr-Πᵉ
              ( unique-action-equiv-family-over-subuniverseᵉ
                  ( mere-equiv-Propᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))
                  ( λ Yᵉ → Finᵉ (nᵉ +ℕᵉ 2ᵉ) ≃ᵉ type-UU-Finᵉ (nᵉ +ℕᵉ 2ᵉ) Yᵉ))))))
      ( not-sign-comp-transposition-countᵉ
        (nᵉ +ℕᵉ 2 ,ᵉ (compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))) (starᵉ))

  simpson-delooping-signᵉ :
    (nᵉ : ℕᵉ) →
    hom-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ nᵉ) (UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ)
  simpson-delooping-signᵉ =
    quotient-delooping-signᵉ
      ( λ nᵉ Xᵉ → Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ)
      ( sign-comp-equivalence-relationᵉ)
      ( λ nᵉ _ → is-decidable-sign-comp-equivalence-relationᵉ nᵉ)
      ( equiv-fin-2-quotient-sign-comp-equiv-Finᵉ)
      ( sign-comp-aut-succ-succ-Finᵉ)
      ( not-action-equiv-family-on-subuniverse-transpositionᵉ)

  eq-simpson-delooping-sign-homomorphismᵉ :
    (nᵉ : ℕᵉ) →
    Idᵉ
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ))
          ( hom-group-hom-Concrete-Groupᵉ
            ( UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))
            ( UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ)
            ( simpson-delooping-signᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( hom-inv-iso-Groupᵉ
            ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
            ( iso-loop-group-fin-UU-Fin-Groupᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
        ( hom-inv-symmetric-group-loop-group-Setᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))))
      ( comp-hom-Groupᵉ
        ( symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
        ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ))
        ( comp-hom-Groupᵉ
          ( symmetric-Groupᵉ (Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ)))
          ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
          ( group-Concrete-Groupᵉ (UU-Fin-Groupᵉ (lsuc lzero ⊔ lᵉ) 2ᵉ))
          ( symmetric-abstract-UU-fin-group-quotient-homᵉ
            ( λ nᵉ Xᵉ → Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ)
            ( sign-comp-equivalence-relationᵉ)
            ( λ nᵉ Hᵉ → is-decidable-sign-comp-equivalence-relationᵉ nᵉ)
            ( equiv-fin-2-quotient-sign-comp-equiv-Finᵉ)
            ( sign-comp-aut-succ-succ-Finᵉ)
            ( not-action-equiv-family-on-subuniverse-transpositionᵉ)
            ( nᵉ))
          ( sign-homomorphismᵉ
            ( nᵉ +ℕᵉ 2ᵉ)
            ( Finᵉ (nᵉ +ℕᵉ 2ᵉ) ,ᵉ unit-trunc-Propᵉ id-equivᵉ)))
        ( hom-inv-symmetric-group-equiv-Setᵉ
          ( Fin-Setᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( raise-Fin-Setᵉ lᵉ (nᵉ +ℕᵉ 2ᵉ))
          ( compute-raiseᵉ lᵉ (Finᵉ (nᵉ +ℕᵉ 2ᵉ)))))
  eq-simpson-delooping-sign-homomorphismᵉ =
    eq-quotient-delooping-sign-homomorphismᵉ
      ( λ nᵉ Xᵉ → Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ)
      ( sign-comp-equivalence-relationᵉ)
      ( λ nᵉ _ → is-decidable-sign-comp-equivalence-relationᵉ nᵉ)
      ( equiv-fin-2-quotient-sign-comp-equiv-Finᵉ)
      ( sign-comp-aut-succ-succ-Finᵉ)
      ( not-action-equiv-family-on-subuniverse-transpositionᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ MR23ᵉ}}