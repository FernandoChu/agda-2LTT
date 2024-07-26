# Orientations of the complete undirected graph

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module univalent-combinatorics.orientations-complete-undirected-graphᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equivalence-relationsᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.involutionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
open import univalent-combinatorics.symmetric-differenceᵉ
```

</details>

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ)
  where

  orientation-Complete-Undirected-Graphᵉ : UUᵉ (lsuc lᵉ)
  orientation-Complete-Undirected-Graphᵉ =
    ((pairᵉ Pᵉ Hᵉ) : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
    Σᵉ (type-UU-Finᵉ nᵉ Xᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)

  is-set-orientation-Complete-Undirected-Graphᵉ :
    is-setᵉ orientation-Complete-Undirected-Graphᵉ
  is-set-orientation-Complete-Undirected-Graphᵉ =
    is-set-Πᵉ
      ( λ (Pᵉ ,ᵉ Hᵉ) →
        is-set-Σᵉ
          ( is-set-type-UU-Finᵉ nᵉ Xᵉ)
          ( λ xᵉ → is-set-is-propᵉ (is-prop-type-Decidable-Propᵉ (Pᵉ xᵉ))))

  2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ :
    orientation-Complete-Undirected-Graphᵉ →
    orientation-Complete-Undirected-Graphᵉ →
    2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ) → Decidable-Propᵉ lᵉ
  pr1ᵉ (2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ dᵉ d'ᵉ Yᵉ) =
    dᵉ Yᵉ ≠ᵉ d'ᵉ Yᵉ
  pr1ᵉ (pr2ᵉ (2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ dᵉ d'ᵉ Yᵉ)) =
    is-prop-negᵉ
  pr2ᵉ (pr2ᵉ (2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ dᵉ d'ᵉ Yᵉ)) =
    is-decidable-negᵉ
      ( has-decidable-equality-is-finiteᵉ
        ( is-finite-type-decidable-subtypeᵉ
          ( pr1ᵉ Yᵉ)
          ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
        ( dᵉ Yᵉ)
        ( d'ᵉ Yᵉ))
  is-finite-subtype-pointwise-differenceᵉ :
    (dᵉ d'ᵉ : orientation-Complete-Undirected-Graphᵉ) →
    is-finiteᵉ
      ( Σᵉ
        ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
        ( λ Yᵉ →
          type-Decidable-Propᵉ
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ dᵉ d'ᵉ Yᵉ)))
  is-finite-subtype-pointwise-differenceᵉ dᵉ d'ᵉ =
    is-finite-type-decidable-subtypeᵉ
      ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ dᵉ d'ᵉ)
      ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ)
  mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ :
    orientation-Complete-Undirected-Graphᵉ →
    orientation-Complete-Undirected-Graphᵉ → Finᵉ 2
  mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ dᵉ d'ᵉ =
    mod-two-ℕᵉ (number-of-elements-is-finiteᵉ
      ( is-finite-subtype-pointwise-differenceᵉ dᵉ d'ᵉ))
  abstract
    equiv-symmetric-difference-subtype-pointwise-differenceᵉ :
      ( d1ᵉ d2ᵉ d3ᵉ : orientation-Complete-Undirected-Graphᵉ) →
      ( type-decidable-subtypeᵉ
        ( symmetric-difference-decidable-subtypeᵉ
          ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ)
          ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d2ᵉ d3ᵉ)) ≃ᵉ
        type-decidable-subtypeᵉ
          ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d3ᵉ))
    equiv-symmetric-difference-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ d3ᵉ =
      equiv-Σᵉ
        ( λ xᵉ →
          pr1ᵉ
            (subtype-decidable-subtypeᵉ
              (2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d3ᵉ)
              ( xᵉ)))
        ( id-equivᵉ)
        ( λ Yᵉ →
          equiv-iffᵉ
            ( prop-Decidable-Propᵉ
              ( symmetric-difference-decidable-subtypeᵉ
                ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                  d1ᵉ d2ᵉ)
                ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                  d2ᵉ d3ᵉ)
                ( Yᵉ)))
            ( prop-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                d1ᵉ d3ᵉ Yᵉ))
            ( fᵉ Yᵉ)
            ( gᵉ Yᵉ))
      where
      fᵉ :
        (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
        type-Propᵉ
          ( prop-Decidable-Propᵉ
            ( symmetric-difference-decidable-subtypeᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ)
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d2ᵉ d3ᵉ)
              ( Yᵉ))) →
          type-Propᵉ
            ( prop-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                d1ᵉ d3ᵉ Yᵉ))
      fᵉ Yᵉ (inlᵉ (pairᵉ npᵉ nnqᵉ)) rᵉ =
        npᵉ (rᵉ ∙ᵉ
          invᵉ
            ( double-negation-elim-is-decidableᵉ
              ( has-decidable-equality-is-finiteᵉ
                ( is-finite-type-decidable-subtypeᵉ
                  ( pr1ᵉ Yᵉ)
                  ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
                ( d2ᵉ Yᵉ)
                ( d3ᵉ Yᵉ))
              ( nnqᵉ)))
      fᵉ Yᵉ (inrᵉ (pairᵉ nqᵉ nnpᵉ)) rᵉ =
        nqᵉ
          ( ( invᵉ
              ( double-negation-elim-is-decidableᵉ
                ( has-decidable-equality-is-finiteᵉ
                  ( is-finite-type-decidable-subtypeᵉ
                    ( pr1ᵉ Yᵉ)
                    ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
                  ( d1ᵉ Yᵉ)
                  ( d2ᵉ Yᵉ))
                ( nnpᵉ))) ∙ᵉ
            ( rᵉ))
      cases-gᵉ :
        (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
        d1ᵉ Yᵉ ≠ᵉ d3ᵉ Yᵉ → (is-decidableᵉ (d1ᵉ Yᵉ ＝ᵉ d2ᵉ Yᵉ)) →
        is-decidableᵉ (d2ᵉ Yᵉ ＝ᵉ d3ᵉ Yᵉ) →
        ((d1ᵉ Yᵉ ≠ᵉ d2ᵉ Yᵉ) ×ᵉ ¬ᵉ (d2ᵉ Yᵉ ≠ᵉ d3ᵉ Yᵉ)) +ᵉ
        ((d2ᵉ Yᵉ ≠ᵉ d3ᵉ Yᵉ) ×ᵉ ¬ᵉ (d1ᵉ Yᵉ ≠ᵉ d2ᵉ Yᵉ))
      cases-gᵉ Yᵉ nrᵉ (inlᵉ pᵉ) (inlᵉ qᵉ) = ex-falsoᵉ (nrᵉ (pᵉ ∙ᵉ qᵉ))
      cases-gᵉ Yᵉ nrᵉ (inlᵉ pᵉ) (inrᵉ nqᵉ) = inrᵉ (pairᵉ nqᵉ (λ fᵉ → fᵉ pᵉ))
      cases-gᵉ Yᵉ nrᵉ (inrᵉ npᵉ) (inlᵉ qᵉ) = inlᵉ (pairᵉ npᵉ (λ fᵉ → fᵉ qᵉ))
      cases-gᵉ Yᵉ nrᵉ (inrᵉ npᵉ) (inrᵉ nqᵉ) =
        ex-falsoᵉ
          (apply-universal-property-trunc-Propᵉ
            ( pr2ᵉ Yᵉ)
            ( empty-Propᵉ)
            ( λ hᵉ →
              contradiction-3-distinct-element-2-Element-Typeᵉ
                ( 2-element-type-2-Element-Decidable-Subtypeᵉ Yᵉ)
                ( d1ᵉ Yᵉ)
                ( d2ᵉ Yᵉ)
                ( d3ᵉ Yᵉ)
                ( npᵉ)
                ( nqᵉ)
                ( nrᵉ)))
      gᵉ :
        (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
        type-Decidable-Propᵉ
          ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d3ᵉ Yᵉ) →
        type-Decidable-Propᵉ
          ( symmetric-difference-decidable-subtypeᵉ
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d2ᵉ d3ᵉ) Yᵉ)
      gᵉ Yᵉ rᵉ =
        cases-gᵉ Yᵉ rᵉ
          ( has-decidable-equality-is-finiteᵉ
            ( is-finite-type-decidable-subtypeᵉ
              ( pr1ᵉ Yᵉ)
              ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
            ( d1ᵉ Yᵉ)
            ( d2ᵉ Yᵉ))
          ( has-decidable-equality-is-finiteᵉ
            ( is-finite-type-decidable-subtypeᵉ
              ( pr1ᵉ Yᵉ)
              ( is-finite-type-UU-Finᵉ nᵉ Xᵉ))
            ( d2ᵉ Yᵉ)
            ( d3ᵉ Yᵉ))
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ :
    ( dᵉ d'ᵉ : orientation-Complete-Undirected-Graphᵉ) (mᵉ : Finᵉ 2ᵉ) →
    Idᵉ
      ( mᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
        dᵉ d'ᵉ) →
    Idᵉ
      ( mᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
        d'ᵉ dᵉ)
  is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
    dᵉ d'ᵉ mᵉ pᵉ =
    ( pᵉ) ∙ᵉ
    ( apᵉ
      ( mod-two-ℕᵉ ∘ᵉ number-of-elements-has-finite-cardinalityᵉ)
      ( all-elements-equal-has-finite-cardinalityᵉ
        ( has-finite-cardinality-d'-dᵉ)
        ( has-finite-cardinality-is-finiteᵉ
          ( is-finite-subtype-pointwise-differenceᵉ d'ᵉ dᵉ))))
    where
    has-finite-cardinality-d'-dᵉ :
      has-finite-cardinalityᵉ
        ( Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
            ( λ Yᵉ →
              type-Decidable-Propᵉ
                ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                  d'ᵉ dᵉ Yᵉ)))
    pr1ᵉ has-finite-cardinality-d'-dᵉ =
      pr1ᵉ
        ( has-finite-cardinality-is-finiteᵉ
          ( is-finite-subtype-pointwise-differenceᵉ dᵉ d'ᵉ))
    pr2ᵉ has-finite-cardinality-d'-dᵉ =
      apply-universal-property-trunc-Propᵉ
        ( pr2ᵉ
          ( has-finite-cardinality-is-finiteᵉ
            ( is-finite-subtype-pointwise-differenceᵉ dᵉ d'ᵉ)))
        ( trunc-Propᵉ
          ( ( Finᵉ (pr1ᵉ has-finite-cardinality-d'-dᵉ)) ≃ᵉ
            ( Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
                ( λ Yᵉ → d'ᵉ Yᵉ ≠ᵉ dᵉ Yᵉ))))
        ( λ hᵉ → unit-trunc-Propᵉ (h'ᵉ ∘eᵉ hᵉ))
      where
      h'ᵉ :
        Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
          ( λ Yᵉ → dᵉ Yᵉ ≠ᵉ d'ᵉ Yᵉ) ≃ᵉ
        Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
          ( λ Yᵉ → d'ᵉ Yᵉ ≠ᵉ dᵉ Yᵉ)
      pr1ᵉ h'ᵉ (pairᵉ Yᵉ npᵉ) = pairᵉ Yᵉ (λ p'ᵉ → npᵉ (invᵉ p'ᵉ))
      pr2ᵉ h'ᵉ =
        is-equiv-is-invertibleᵉ
          ( λ (pairᵉ Yᵉ npᵉ) → pairᵉ Yᵉ (λ p'ᵉ → npᵉ (invᵉ p'ᵉ)))
          ( λ (pairᵉ Yᵉ npᵉ) → eq-pair-eq-fiberᵉ (eq-is-propᵉ is-prop-negᵉ))
          ( λ (pairᵉ Yᵉ npᵉ) → eq-pair-eq-fiberᵉ (eq-is-propᵉ is-prop-negᵉ))
  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ :
    (d1ᵉ d2ᵉ d3ᵉ : orientation-Complete-Undirected-Graphᵉ) (mᵉ : Finᵉ 2ᵉ) →
    Idᵉ
      ( mᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
        d1ᵉ d2ᵉ) →
    Idᵉ
      ( mᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
        d2ᵉ d3ᵉ) →
    Idᵉ
      ( zero-Finᵉ 1ᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
        d1ᵉ d3ᵉ)
  eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
    d1ᵉ d2ᵉ d3ᵉ mᵉ p1ᵉ p2ᵉ =
    invᵉ
      ( is-zero-mod-succ-ℕᵉ
        ( 1ᵉ)
        ( dist-ℕᵉ (k1ᵉ +ℕᵉ k2ᵉ) (2ᵉ *ℕᵉ k'ᵉ))
        ( transitive-cong-ℕᵉ
          ( 2ᵉ)
          ( k1ᵉ +ℕᵉ k2ᵉ)
          ( zero-ℕᵉ)
          ( 2 *ℕᵉ k'ᵉ)
          ( scalar-invariant-cong-ℕ'ᵉ 2 0 2 k'ᵉ (cong-zero-ℕ'ᵉ 2ᵉ))
          ( transitive-cong-ℕᵉ 2
            ( k1ᵉ +ℕᵉ k2ᵉ)
            ( add-ℕᵉ
              ( nat-Finᵉ 2
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                    d1ᵉ d2ᵉ))
              ( nat-Finᵉ 2
                ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                    d2ᵉ d3ᵉ)))
            ( zero-ℕᵉ)
            ( concatenate-eq-cong-ℕᵉ 2
              ( ( ap-binaryᵉ
                  ( add-ℕᵉ)
                  ( apᵉ (nat-Finᵉ 2ᵉ) (invᵉ p1ᵉ))
                  ( apᵉ (nat-Finᵉ 2ᵉ) (invᵉ p2ᵉ))) ∙ᵉ
                ( apᵉ
                  ( λ nᵉ → nᵉ +ℕᵉ (nat-Finᵉ 2 mᵉ))
                  ( invᵉ (left-unit-law-mul-ℕᵉ (nat-Finᵉ 2 mᵉ)))))
              ( scalar-invariant-cong-ℕ'ᵉ 2 2 0 (nat-Finᵉ 2 mᵉ) (cong-zero-ℕ'ᵉ 2ᵉ)))
            ( symmetric-cong-ℕᵉ 2
              ( add-ℕᵉ
                ( nat-Finᵉ 2
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                      d1ᵉ d2ᵉ))
                ( nat-Finᵉ 2
                  ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                      d2ᵉ d3ᵉ)))
              ( k1ᵉ +ℕᵉ k2ᵉ)
              ( cong-add-ℕᵉ k1ᵉ k2ᵉ))))) ∙ᵉ
      ( apᵉ
        ( mod-two-ℕᵉ)
        ( ( symmetric-dist-ℕᵉ (k1ᵉ +ℕᵉ k2ᵉ) (2ᵉ *ℕᵉ k'ᵉ)) ∙ᵉ
          ( invᵉ
            ( rewrite-left-add-dist-ℕᵉ
              ( kᵉ)
              ( 2 *ℕᵉ k'ᵉ)
              ( k1ᵉ +ℕᵉ k2ᵉ)
              ( invᵉ
                ( eq-symmetric-differenceᵉ
                  ( 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
                  ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                      d1ᵉ d2ᵉ)
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                      d2ᵉ d3ᵉ)))) ∙ᵉ
            ( apᵉ
              ( number-of-elements-has-finite-cardinalityᵉ)
              ( all-elements-equal-has-finite-cardinalityᵉ
                ( has-finite-cardinality-is-finiteᵉ
                  ( is-finite-type-decidable-subtypeᵉ
                    ( symmetric-difference-decidable-subtypeᵉ
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                          d1ᵉ d2ᵉ)
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                          d2ᵉ d3ᵉ))
                    ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ)))
                ( pairᵉ
                  ( number-of-elements-is-finiteᵉ
                    ( is-finite-type-decidable-subtypeᵉ
                      ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                          d1ᵉ d3ᵉ)
                      ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ)))
                  ( transitive-mere-equivᵉ _ _ _
                    ( unit-trunc-Propᵉ
                      ( inv-equivᵉ
                        ( equiv-symmetric-difference-subtype-pointwise-differenceᵉ
                            d1ᵉ d2ᵉ d3ᵉ)))
                    ( pr2ᵉ
                      ( has-finite-cardinality-is-finiteᵉ
                        ( is-finite-type-decidable-subtypeᵉ
                          ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                              d1ᵉ d3ᵉ)
                          ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ)))))))))))
    where
    kᵉ : ℕᵉ
    kᵉ =
      number-of-elements-is-finiteᵉ
        ( is-finite-type-decidable-subtypeᵉ
          ( symmetric-difference-decidable-subtypeᵉ
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                d1ᵉ d2ᵉ)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                d2ᵉ d3ᵉ))
          ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ))
    k1ᵉ : ℕᵉ
    k1ᵉ =
      number-of-elements-is-finiteᵉ
        (is-finite-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ)
    k2ᵉ : ℕᵉ
    k2ᵉ =
      number-of-elements-is-finiteᵉ
        (is-finite-subtype-pointwise-differenceᵉ d2ᵉ d3ᵉ)
    k'ᵉ : ℕᵉ
    k'ᵉ =
      number-of-elements-is-finiteᵉ
        ( is-finite-type-decidable-subtypeᵉ
          ( intersection-decidable-subtypeᵉ
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d1ᵉ d2ᵉ)
            ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ d2ᵉ d3ᵉ))
          ( is-finite-2-Element-Decidable-Subtypeᵉ nᵉ Xᵉ))
  even-difference-orientation-Complete-Undirected-Graphᵉ :
    equivalence-relationᵉ lzero orientation-Complete-Undirected-Graphᵉ
  pr1ᵉ even-difference-orientation-Complete-Undirected-Graphᵉ dᵉ d'ᵉ =
    Id-Propᵉ
      ( Fin-Setᵉ 2ᵉ)
      ( zero-Finᵉ 1ᵉ)
      ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
          dᵉ d'ᵉ)
  pr1ᵉ (pr2ᵉ even-difference-orientation-Complete-Undirected-Graphᵉ) dᵉ =
    apᵉ
      ( mod-two-ℕᵉ ∘ᵉ number-of-elements-has-finite-cardinalityᵉ)
      ( all-elements-equal-has-finite-cardinalityᵉ
        ( pairᵉ
          ( 0ᵉ)
          ( unit-trunc-Propᵉ (equiv-is-emptyᵉ idᵉ (λ (ᵉ_ ,ᵉ npᵉ) → npᵉ reflᵉ))))
        ( has-finite-cardinality-is-finiteᵉ
          ( is-finite-subtype-pointwise-differenceᵉ dᵉ dᵉ)))
  pr1ᵉ (pr2ᵉ (pr2ᵉ even-difference-orientation-Complete-Undirected-Graphᵉ))
    dᵉ d'ᵉ pᵉ =
    is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
      dᵉ d'ᵉ (zero-Finᵉ 1ᵉ) pᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ even-difference-orientation-Complete-Undirected-Graphᵉ))
    d1ᵉ d2ᵉ d3ᵉ p1ᵉ p2ᵉ =
    eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
      d1ᵉ d2ᵉ d3ᵉ (zero-Finᵉ 1ᵉ) p2ᵉ p1ᵉ
  abstract
    is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ :
      (Yᵉ Y'ᵉ : orientation-Complete-Undirected-Graphᵉ) →
      is-decidableᵉ
        ( sim-equivalence-relationᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ)
            ( Yᵉ)
            ( Y'ᵉ))
    is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ Yᵉ Y'ᵉ =
      has-decidable-equality-is-finiteᵉ
        ( is-finite-Finᵉ 2ᵉ)
        ( zero-Finᵉ 1ᵉ)
        ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
            Yᵉ Y'ᵉ)
  quotient-signᵉ : UUᵉ (lsuc lᵉ)
  quotient-signᵉ =
    equivalence-classᵉ even-difference-orientation-Complete-Undirected-Graphᵉ
  quotient-sign-Setᵉ : Setᵉ (lsuc lᵉ)
  quotient-sign-Setᵉ =
    equivalence-class-Setᵉ even-difference-orientation-Complete-Undirected-Graphᵉ
module _
  {lᵉ : Level} (nᵉ : ℕᵉ)
  where
  map-orientation-complete-undirected-graph-equivᵉ :
    (Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ) →
    (type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
    orientation-Complete-Undirected-Graphᵉ nᵉ Xᵉ →
    orientation-Complete-Undirected-Graphᵉ nᵉ X'ᵉ
  pr1ᵉ (map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ Yᵉ) =
    map-equivᵉ eᵉ (pr1ᵉ (dᵉ (precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ Yᵉ)))
  pr2ᵉ (map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ Yᵉ) =
    pr2ᵉ (dᵉ (precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ Yᵉ))
  orientation-complete-undirected-graph-equivᵉ :
    (Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ) →
    (type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
    orientation-Complete-Undirected-Graphᵉ nᵉ Xᵉ ≃ᵉ
    orientation-Complete-Undirected-Graphᵉ nᵉ X'ᵉ
  pr1ᵉ (orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ) =
    map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ
  pr2ᵉ (orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ) =
    is-equiv-is-invertibleᵉ
      ( map-orientation-complete-undirected-graph-equivᵉ X'ᵉ Xᵉ (inv-equivᵉ eᵉ))
      ( λ dᵉ →
        eq-htpyᵉ
          ( λ Yᵉ →
            eq-pair-Σᵉ
              (( ( apᵉ
                ( λ Y'ᵉ → (map-equivᵉ eᵉ ∘ᵉ (map-equivᵉ (inv-equivᵉ eᵉ))) (pr1ᵉ (dᵉ Y'ᵉ)))
                ( eq-pair-Σᵉ
                  ( apᵉ
                    ( λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ map-equivᵉ hᵉ)
                    ( left-inverse-law-equivᵉ (inv-equivᵉ eᵉ)))
                  ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                ( apᵉ
                  ( λ hᵉ → map-equivᵉ hᵉ (pr1ᵉ (dᵉ Yᵉ)))
                  ( left-inverse-law-equivᵉ (inv-equivᵉ eᵉ)))))
              ( eq-is-propᵉ
                ( is-prop-type-Decidable-Propᵉ (pr1ᵉ Yᵉ (pr1ᵉ (idᵉ dᵉ Yᵉ)))))))
      ( λ dᵉ →
        eq-htpyᵉ
          ( λ Yᵉ →
            eq-pair-Σᵉ
              ( ( apᵉ
                ( λ Y'ᵉ → (map-equivᵉ (inv-equivᵉ eᵉ) ∘ᵉ map-equivᵉ eᵉ) (pr1ᵉ (dᵉ Y'ᵉ)))
                ( eq-pair-Σᵉ
                  ( apᵉ
                    ( λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ map-equivᵉ hᵉ)
                    ( right-inverse-law-equivᵉ (inv-equivᵉ eᵉ)))
                  ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                ( apᵉ
                  ( λ hᵉ → map-equivᵉ hᵉ (pr1ᵉ (dᵉ Yᵉ)))
                  ( right-inverse-law-equivᵉ (inv-equivᵉ eᵉ))))
              ( eq-is-propᵉ
                ( is-prop-type-Decidable-Propᵉ (pr1ᵉ Yᵉ (pr1ᵉ (idᵉ dᵉ Yᵉ)))))))
  abstract
    preserves-id-equiv-orientation-complete-undirected-graph-equivᵉ :
      (Xᵉ : UU-Finᵉ lᵉ nᵉ) →
      Idᵉ (orientation-complete-undirected-graph-equivᵉ Xᵉ Xᵉ id-equivᵉ) id-equivᵉ
    preserves-id-equiv-orientation-complete-undirected-graph-equivᵉ Xᵉ =
      eq-htpy-equivᵉ
        ( λ dᵉ →
          eq-htpyᵉ
            ( λ Yᵉ →
              eq-pair-Σᵉ
                ( apᵉ
                  ( pr1ᵉ ∘ᵉ dᵉ)
                  ( eq-pair-eq-fiberᵉ (eq-is-propᵉ is-prop-type-trunc-Propᵉ)))
                ( eq-is-propᵉ
                  ( is-prop-type-Decidable-Propᵉ
                    ( pr1ᵉ Yᵉ (pr1ᵉ (map-equivᵉ id-equivᵉ dᵉ Yᵉ)))))))
    preserves-comp-orientation-complete-undirected-graph-equivᵉ :
      ( Xᵉ Yᵉ Zᵉ : UU-Finᵉ lᵉ nᵉ)
      (eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ Yᵉ) →
      (fᵉ : type-UU-Finᵉ nᵉ Yᵉ ≃ᵉ type-UU-Finᵉ nᵉ Zᵉ) →
      Idᵉ
        ( orientation-complete-undirected-graph-equivᵉ Xᵉ Zᵉ (fᵉ ∘eᵉ eᵉ))
        ( ( orientation-complete-undirected-graph-equivᵉ Yᵉ Zᵉ fᵉ) ∘eᵉ
          ( orientation-complete-undirected-graph-equivᵉ Xᵉ Yᵉ eᵉ))
    preserves-comp-orientation-complete-undirected-graph-equivᵉ Xᵉ Yᵉ Zᵉ eᵉ fᵉ =
      eq-htpy-equivᵉ
        ( λ dᵉ →
          eq-htpyᵉ
            ( λ Sᵉ →
              eq-pair-Σᵉ
                ( apᵉ
                  ( λ S'ᵉ → map-equivᵉ (fᵉ ∘eᵉ eᵉ) (pr1ᵉ (dᵉ S'ᵉ)))
                  ( htpy-eqᵉ
                    ( preserves-comp-precomp-equiv-2-Element-Decidable-Subtypeᵉ
                        eᵉ fᵉ)
                    ( Sᵉ)))
                ( eq-is-propᵉ
                  ( is-prop-type-Decidable-Propᵉ
                    ( pr1ᵉ Sᵉ
                      ( pr1ᵉ
                        ( map-equivᵉ
                          ( orientation-complete-undirected-graph-equivᵉ Yᵉ Zᵉ fᵉ ∘eᵉ
                            orientation-complete-undirected-graph-equivᵉ Xᵉ Yᵉ eᵉ)
                          ( dᵉ)
                          ( Sᵉ))))))))
    preserves-even-difference-orientation-complete-undirected-graph-equivᵉ :
      (Xᵉ X'ᵉ : UU-Finᵉ lᵉ nᵉ) ( eᵉ : type-UU-Finᵉ nᵉ Xᵉ ≃ᵉ type-UU-Finᵉ nᵉ X'ᵉ) →
      ( dᵉ d'ᵉ : orientation-Complete-Undirected-Graphᵉ nᵉ Xᵉ) →
      ( sim-equivalence-relationᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ nᵉ Xᵉ)
        ( dᵉ)
        ( d'ᵉ) ↔ᵉ
        sim-equivalence-relationᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ nᵉ X'ᵉ)
          ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ)
          ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ d'ᵉ))
    pr1ᵉ
      ( preserves-even-difference-orientation-complete-undirected-graph-equivᵉ
          Xᵉ X'ᵉ eᵉ dᵉ d'ᵉ) =
      _∙ᵉ apᵉ
          ( mod-two-ℕᵉ ∘ᵉ number-of-elements-has-finite-cardinalityᵉ)
          ( all-elements-equal-has-finite-cardinalityᵉ
            ( has-finite-cardinality-is-finiteᵉ
              ( is-finite-subtype-pointwise-differenceᵉ nᵉ Xᵉ dᵉ d'ᵉ))
            ( pairᵉ
              ( number-of-elements-is-finiteᵉ
                ( is-finite-subtype-pointwise-differenceᵉ nᵉ X'ᵉ
                  ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ)
                  ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ d'ᵉ)))
              ( map-trunc-Propᵉ
                ( equiv-subtype-pointwise-difference-equivᵉ ∘eᵉ_)
                ( pr2ᵉ
                  ( has-finite-cardinality-is-finiteᵉ
                    ( is-finite-subtype-pointwise-differenceᵉ nᵉ X'ᵉ
                      ( map-orientation-complete-undirected-graph-equivᵉ
                          Xᵉ X'ᵉ eᵉ dᵉ)
                      ( map-orientation-complete-undirected-graph-equivᵉ
                          Xᵉ X'ᵉ eᵉ d'ᵉ)))))))
      where
      equiv-subtype-pointwise-difference-equivᵉ :
        Σᵉ (2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ X'ᵉ))
          ( λ Yᵉ →
            type-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ nᵉ X'ᵉ
                ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ)
                ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ d'ᵉ)
                ( Yᵉ))) ≃ᵉ
        Σᵉ (2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ))
          ( λ Yᵉ →
            type-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                  nᵉ Xᵉ dᵉ d'ᵉ Yᵉ))
      pr1ᵉ (pr1ᵉ equiv-subtype-pointwise-difference-equivᵉ (pairᵉ Yᵉ NQᵉ)) =
        precomp-equiv-2-Element-Decidable-Subtypeᵉ eᵉ Yᵉ
      pr2ᵉ (pr1ᵉ equiv-subtype-pointwise-difference-equivᵉ (pairᵉ Yᵉ NQᵉ)) pᵉ =
        NQᵉ
          ( eq-pair-Σᵉ
            ( apᵉ (map-equivᵉ eᵉ) (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
            ( eq-is-propᵉ
              ( is-prop-type-Decidable-Propᵉ
                ( pr1ᵉ
                  ( Yᵉ)
                  ( pr1ᵉ
                    ( map-orientation-complete-undirected-graph-equivᵉ
                        Xᵉ X'ᵉ eᵉ d'ᵉ Yᵉ))))))
      pr2ᵉ equiv-subtype-pointwise-difference-equivᵉ =
        is-equiv-is-invertibleᵉ
          ( λ (pairᵉ Yᵉ NQᵉ) →
            pairᵉ
              ( precomp-equiv-2-Element-Decidable-Subtypeᵉ (inv-equivᵉ eᵉ) Yᵉ)
              ( λ pᵉ →
                NQᵉ
                  ( eq-pair-Σᵉ
                    ( ( apᵉ
                      ( λ Y'ᵉ → pr1ᵉ (dᵉ Y'ᵉ))
                      ( eq-pair-Σᵉ
                        ( apᵉ
                          ( λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ (map-equivᵉ hᵉ))
                          ( invᵉ (left-inverse-law-equivᵉ eᵉ)))
                        ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))) ∙ᵉ
                      ( ( is-injective-equivᵉ eᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ))) ∙ᵉ
                        ( apᵉ
                          ( λ Y'ᵉ → pr1ᵉ (d'ᵉ Y'ᵉ))
                          ( eq-pair-Σᵉ
                            ( apᵉ
                              ( λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ map-equivᵉ hᵉ)
                              ( left-inverse-law-equivᵉ eᵉ))
                            ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))
                    ( eq-is-propᵉ
                      ( is-prop-type-Decidable-Propᵉ (pr1ᵉ Yᵉ (pr1ᵉ (d'ᵉ Yᵉ))))))))
          ( λ (pairᵉ Yᵉ NQᵉ) →
            eq-pair-Σᵉ
              ( eq-pair-Σᵉ
                ( apᵉ (λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ map-equivᵉ hᵉ) (left-inverse-law-equivᵉ eᵉ))
                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
              ( eq-is-propᵉ
                ( is-prop-type-Decidable-Propᵉ
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                      nᵉ Xᵉ dᵉ d'ᵉ Yᵉ))))
          ( λ (pairᵉ Yᵉ NQᵉ) →
            eq-pair-Σᵉ
              ( eq-pair-Σᵉ
                ( apᵉ (λ hᵉ → pr1ᵉ Yᵉ ∘ᵉ map-equivᵉ hᵉ) (right-inverse-law-equivᵉ eᵉ))
                ( eq-is-propᵉ is-prop-type-trunc-Propᵉ))
              ( eq-is-propᵉ
                ( is-prop-type-Decidable-Propᵉ
                  ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                    ( nᵉ)
                    ( X'ᵉ)
                    ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ)
                    ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ d'ᵉ)
                    ( Yᵉ)))))
    pr2ᵉ
      ( preserves-even-difference-orientation-complete-undirected-graph-equivᵉ
          Xᵉ X'ᵉ eᵉ dᵉ d'ᵉ)
      Pᵉ =
      trᵉ
        ( λ gᵉ →
          sim-equivalence-relationᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ nᵉ Xᵉ)
            ( map-equivᵉ gᵉ dᵉ)
            ( map-equivᵉ gᵉ d'ᵉ))
        { xᵉ =
          orientation-complete-undirected-graph-equivᵉ X'ᵉ Xᵉ (inv-equivᵉ eᵉ) ∘eᵉ
          orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ}
        { yᵉ = id-equivᵉ}
        ( ( invᵉ
            ( preserves-comp-orientation-complete-undirected-graph-equivᵉ
                Xᵉ X'ᵉ Xᵉ eᵉ (inv-equivᵉ eᵉ))) ∙ᵉ
          ( ( apᵉ
              ( orientation-complete-undirected-graph-equivᵉ Xᵉ Xᵉ)
              ( left-inverse-law-equivᵉ eᵉ)) ∙ᵉ
            ( preserves-id-equiv-orientation-complete-undirected-graph-equivᵉ
              ( Xᵉ))))
        ( pr1ᵉ
          ( preserves-even-difference-orientation-complete-undirected-graph-equivᵉ
            ( X'ᵉ)
            ( Xᵉ)
            ( inv-equivᵉ eᵉ)
            ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ dᵉ)
            ( map-orientation-complete-undirected-graph-equivᵉ Xᵉ X'ᵉ eᵉ d'ᵉ))
          ( Pᵉ))
```

</details>

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  (eXᵉ : countᵉ Xᵉ) (ineqᵉ : leq-ℕᵉ 2 (number-of-elements-countᵉ eXᵉ))
  where

  cases-orientation-aut-countᵉ :
    (eᵉ : Xᵉ ≃ᵉ Xᵉ)
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
    ( two-elementsᵉ : Σᵉ Xᵉ
      ( λ xᵉ → Σᵉ Xᵉ
        ( λ yᵉ →
          Σᵉ (xᵉ ≠ᵉ yᵉ)
          ( λ npᵉ →
            Idᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))
              ( Yᵉ))))) →
    is-decidableᵉ
      ( Idᵉ (map-equivᵉ eᵉ (pr1ᵉ two-elementsᵉ)) (pr1ᵉ two-elementsᵉ)) →
    is-decidableᵉ
      ( Idᵉ (map-equivᵉ eᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ))) (pr1ᵉ (pr2ᵉ two-elementsᵉ))) →
    Σᵉ Xᵉ (λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ zᵉ))
  cases-orientation-aut-countᵉ
    eᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ npᵉ Pᵉ))) (inlᵉ qᵉ) rᵉ =
    pairᵉ xᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
  cases-orientation-aut-countᵉ
    eᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ npᵉ Pᵉ))) (inrᵉ nqᵉ) (inlᵉ nrᵉ) =
    pairᵉ yᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
  cases-orientation-aut-countᵉ
    eᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ npᵉ Pᵉ))) (inrᵉ nqᵉ) (inrᵉ nrᵉ) =
    pairᵉ xᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))

  orientation-aut-countᵉ :
    Xᵉ ≃ᵉ Xᵉ →
    orientation-Complete-Undirected-Graphᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
  orientation-aut-countᵉ eᵉ Yᵉ =
    cases-orientation-aut-countᵉ eᵉ Yᵉ
      ( two-elements-transpositionᵉ eXᵉ Yᵉ)
      ( has-decidable-equality-countᵉ eXᵉ
        ( map-equivᵉ eᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
        ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
      ( has-decidable-equality-countᵉ eXᵉ
        ( map-equivᵉ eᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
        ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))

  cases-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ)
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
    ( two-elementsᵉ : Σᵉ Xᵉ
      ( λ xᵉ → Σᵉ Xᵉ
        ( λ yᵉ →
          Σᵉ (xᵉ ≠ᵉ yᵉ)
          ( λ np'ᵉ →
            Idᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( np'ᵉ))
              ( Yᵉ))))) →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ) →
    Σᵉ Xᵉ (λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ zᵉ))
  cases-orientation-two-elements-countᵉ
    iᵉ jᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inlᵉ qᵉ) rᵉ sᵉ =
    pairᵉ yᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
  cases-orientation-two-elements-countᵉ
    iᵉ jᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) =
    pairᵉ xᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
  cases-orientation-two-elements-countᵉ
    iᵉ jᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) =
    pairᵉ yᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
  cases-orientation-two-elements-countᵉ
    iᵉ jᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inrᵉ nrᵉ) sᵉ =
    pairᵉ xᵉ (trᵉ (λ Zᵉ → type-Decidable-Propᵉ (pr1ᵉ Zᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))

  orientation-two-elements-countᵉ :
    (iᵉ jᵉ : Xᵉ) → iᵉ ≠ᵉ jᵉ →
    orientation-Complete-Undirected-Graphᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
  orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ =
    cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
      ( two-elements-transpositionᵉ eXᵉ Yᵉ)
      ( has-decidable-equality-countᵉ eXᵉ
        ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ)
      ( has-decidable-equality-countᵉ eXᵉ
        ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ)
      ( has-decidable-equality-countᵉ eXᵉ
        ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) iᵉ)

  first-element-countᵉ : Xᵉ
  first-element-countᵉ =
    map-equiv-countᵉ
      ( eXᵉ)
      ( pr1ᵉ
        ( two-distinct-elements-leq-2-Finᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( ineqᵉ)))

  second-element-countᵉ : Xᵉ
  second-element-countᵉ =
    map-equiv-countᵉ
      ( eXᵉ)
      ( pr1ᵉ
        ( pr2ᵉ
          ( two-distinct-elements-leq-2-Finᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( ineqᵉ))))

  abstract
    distinct-two-elements-countᵉ :
      first-element-countᵉ ≠ᵉ second-element-countᵉ
    distinct-two-elements-countᵉ pᵉ =
      pr2ᵉ
        ( pr2ᵉ
          ( two-distinct-elements-leq-2-Finᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( ineqᵉ)))
        ( is-injective-equivᵉ (equiv-countᵉ eXᵉ) pᵉ)

  canonical-2-Element-Decidable-Subtype-countᵉ :
    2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ
  canonical-2-Element-Decidable-Subtype-countᵉ =
    standard-2-Element-Decidable-Subtypeᵉ
      ( has-decidable-equality-countᵉ eXᵉ)
      ( distinct-two-elements-countᵉ)

  canonical-orientation-countᵉ :
    orientation-Complete-Undirected-Graphᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
  canonical-orientation-countᵉ =
    orientation-two-elements-countᵉ
      ( first-element-countᵉ)
      ( second-element-countᵉ)
      ( distinct-two-elements-countᵉ)

  transitive-canonical-orientation-countᵉ :
    orientation-Complete-Undirected-Graphᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
  transitive-canonical-orientation-countᵉ =
    orientation-two-elements-countᵉ
      ( second-element-countᵉ)
      ( first-element-countᵉ)
      ( λ pᵉ → distinct-two-elements-countᵉ (invᵉ pᵉ))

  abstract
    cases-inward-edge-left-two-elements-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) iᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) xᵉ)) →
      Idᵉ
        ( pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ))
        ( xᵉ)
    cases-inward-edge-left-two-elements-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inlᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( pr1ᵉ dᵉ)
              ( pr2ᵉ dᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))))
        { xᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( iᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( jᵉ))}
        { yᵉ = pairᵉ (inrᵉ (λ pᵉ → nqᵉ (invᵉ r1ᵉ ∙ᵉ pᵉ))) (inrᵉ (λ pᵉ → nrᵉ (invᵉ r1ᵉ ∙ᵉ pᵉ)))}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ)))
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ))))) ∙ᵉ
        ( r1ᵉ)
    cases-inward-edge-left-two-elements-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inrᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( dᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
                ( jᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))))
        { xᵉ =
          has-decidable-equality-countᵉ
            ( eXᵉ)
            ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
            ( iᵉ)}
        { yᵉ = inlᵉ r1ᵉ}
        ( eq-is-propᵉ
          ( is-prop-is-decidableᵉ
            ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ)))) ∙ᵉ
      ( r2ᵉ)

    inward-edge-left-two-elements-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ iᵉ)) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      Idᵉ
        ( pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ))
        ( xᵉ)
    inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ p1ᵉ p2ᵉ nqᵉ nrᵉ =
      cases-inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ
        ( eq-two-elements-transpositionᵉ eXᵉ Yᵉ xᵉ iᵉ nqᵉ p1ᵉ p2ᵉ)

    cases-inward-edge-left-transposition-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) iᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) xᵉ)) →
      Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)))
        ( xᵉ)
    cases-inward-edge-left-transposition-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inlᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-aut-countᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( dᵉ)
              ( has-decidable-equality-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))))
        { xᵉ =
          has-decidable-equality-countᵉ eXᵉ
            ( map-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))}

        { yᵉ =
          inlᵉ
            ( trᵉ
              ( λ yᵉ →
                Idᵉ
                  ( map-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( yᵉ))
                  ( yᵉ))
              ( invᵉ r1ᵉ)
              ( is-fixed-point-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)
                ( xᵉ)
                ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                ( λ rᵉ → nrᵉ (invᵉ rᵉ))))}
        ( eq-is-propᵉ
          ( is-prop-is-decidableᵉ
            ( is-set-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))) ∙ᵉ
        ( r1ᵉ)
    cases-inward-edge-left-transposition-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inrᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ wᵉ →
          pr1ᵉ
            ( cases-orientation-aut-countᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( pr1ᵉ wᵉ)
              ( pr2ᵉ wᵉ)))
        { xᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
              ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))}
        { yᵉ =
          pairᵉ
            ( inrᵉ
              ( λ sᵉ →
                npᵉ
                  ( invᵉ r1ᵉ ∙ᵉ
                    ( invᵉ sᵉ ∙ᵉ
                      trᵉ
                        ( λ yᵉ →
                          Idᵉ
                            ( map-equivᵉ
                              ( transpositionᵉ
                                ( standard-2-Element-Decidable-Subtypeᵉ
                                  ( has-decidable-equality-countᵉ eXᵉ)
                                  ( npᵉ)))
                              ( yᵉ))
                            ( jᵉ))
                        ( invᵉ r1ᵉ)
                        ( left-computation-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ))))))
            ( inlᵉ
              ( trᵉ
                ( λ yᵉ →
                  Idᵉ
                    ( map-equivᵉ
                      ( transpositionᵉ
                        ( standard-2-Element-Decidable-Subtypeᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ)))
                      ( yᵉ))
                    ( yᵉ))
                ( invᵉ r2ᵉ)
                ( is-fixed-point-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)
                  ( xᵉ)
                  ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                  ( λ rᵉ → nrᵉ (invᵉ rᵉ)))))}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))))) ∙ᵉ
        ( r2ᵉ)

    inward-edge-left-transposition-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ iᵉ)) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)))
        ( xᵉ)
    inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ p1ᵉ p2ᵉ nqᵉ nrᵉ =
      cases-inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ
        ( eq-two-elements-transpositionᵉ eXᵉ Yᵉ xᵉ iᵉ nqᵉ p1ᵉ p2ᵉ)

    cases-inward-edge-right-two-elements-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) jᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) xᵉ)) →
      Idᵉ
        ( pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ))
        ( xᵉ)
    cases-inward-edge-right-two-elements-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inlᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( pr1ᵉ dᵉ)
              ( pr2ᵉ dᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))))
        { xᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( iᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( jᵉ))}
        { yᵉ = pairᵉ (inrᵉ (λ pᵉ → nqᵉ (invᵉ r1ᵉ ∙ᵉ pᵉ))) (inrᵉ (λ pᵉ → nrᵉ (invᵉ r1ᵉ ∙ᵉ pᵉ)))}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ)))
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ))))) ∙ᵉ
        ( r1ᵉ)
    cases-inward-edge-right-two-elements-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inrᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( pr1ᵉ dᵉ)
              ( pr2ᵉ dᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))))
        { xᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( iᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( jᵉ))}
        { yᵉ = pairᵉ (inrᵉ λ pᵉ → npᵉ (invᵉ pᵉ ∙ᵉ r1ᵉ)) (inlᵉ r1ᵉ)}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) iᵉ)))
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ))))) ∙ᵉ
        ( ( apᵉ
          ( λ dᵉ →
            pr1ᵉ
              ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
                ( two-elements-transpositionᵉ eXᵉ Yᵉ)
                ( inrᵉ λ pᵉ → npᵉ (invᵉ pᵉ ∙ᵉ r1ᵉ))
                ( inlᵉ r1ᵉ)
                ( dᵉ)))
          { xᵉ =
            has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( iᵉ)}
          { yᵉ = inrᵉ (λ qᵉ → nqᵉ (invᵉ r2ᵉ ∙ᵉ qᵉ))}
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))))) ∙ᵉ
          ( r2ᵉ))

    inward-edge-right-two-elements-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ jᵉ)) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      Idᵉ
        ( pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ))
        ( xᵉ)
    inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ p1ᵉ p2ᵉ nqᵉ nrᵉ =
      cases-inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ
        ( eq-two-elements-transpositionᵉ eXᵉ Yᵉ xᵉ jᵉ nrᵉ p1ᵉ p2ᵉ)

    cases-inward-edge-right-transposition-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) jᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)) jᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))) xᵉ)) →
      Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)))
        ( xᵉ)
    cases-inward-edge-right-transposition-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inlᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ dᵉ →
          pr1ᵉ
            ( cases-orientation-aut-countᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( dᵉ)
              ( has-decidable-equality-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))))
        { xᵉ =
          has-decidable-equality-countᵉ eXᵉ
            ( map-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))}
        { yᵉ =
          inlᵉ
            ( trᵉ
              ( λ yᵉ →
                Idᵉ
                  ( map-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( yᵉ))
                  ( yᵉ))
              ( invᵉ r1ᵉ)
              ( is-fixed-point-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)
                ( xᵉ)
                ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                ( λ rᵉ → nrᵉ (invᵉ rᵉ))))}
        ( eq-is-propᵉ
          ( is-prop-is-decidableᵉ
            ( is-set-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))) ∙ᵉ
        ( r1ᵉ)
    cases-inward-edge-right-transposition-orientation-countᵉ
      iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ (inrᵉ (pairᵉ r1ᵉ r2ᵉ)) =
      ( apᵉ
        ( λ wᵉ →
          pr1ᵉ
            ( cases-orientation-aut-countᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( pr1ᵉ wᵉ)
              ( pr2ᵉ wᵉ)))
        { xᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
              ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))}
        { yᵉ =
          pairᵉ
            ( inrᵉ
                λ sᵉ →
                npᵉ
                  ( ( trᵉ
                      ( λ yᵉ →
                        Idᵉ
                          ( iᵉ)
                          ( map-equivᵉ
                            ( transpositionᵉ
                              ( standard-2-Element-Decidable-Subtypeᵉ
                                ( has-decidable-equality-countᵉ eXᵉ)
                                ( npᵉ)))
                            ( yᵉ)))
                      ( invᵉ r1ᵉ)
                      ( invᵉ
                        ( right-computation-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ))) ∙ᵉ
                    ( sᵉ ∙ᵉ r1ᵉ))))
            ( inlᵉ
              ( trᵉ
                ( λ yᵉ →
                  Idᵉ
                    ( map-equivᵉ
                      ( transpositionᵉ
                        ( standard-2-Element-Decidable-Subtypeᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ)))
                      ( yᵉ))
                    ( yᵉ))
                ( invᵉ r2ᵉ)
                ( is-fixed-point-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)
                  ( xᵉ)
                  ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                  ( λ rᵉ → nrᵉ (invᵉ rᵉ)))))}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-set-countᵉ eXᵉ
                ( map-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))))))) ∙ᵉ
        ( r2ᵉ)

    inward-edge-right-transposition-orientation-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
      (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)) →
      ( type-Decidable-Propᵉ (pr1ᵉ Yᵉ jᵉ)) →
      xᵉ ≠ᵉ iᵉ → xᵉ ≠ᵉ jᵉ →
      Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)))
        ( xᵉ)
    inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ p1ᵉ p2ᵉ nqᵉ nrᵉ =
      cases-inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ nqᵉ nrᵉ
        ( eq-two-elements-transpositionᵉ eXᵉ Yᵉ xᵉ jᵉ nrᵉ p1ᵉ p2ᵉ)

    cases-eq-orientation-two-elements-countᵉ :
      ( iᵉ jᵉ : Xᵉ)
      ( npᵉ : iᵉ ≠ᵉ jᵉ)
      ( two-elementsᵉ : Σᵉ Xᵉ
        ( λ xᵉ → Σᵉ Xᵉ
          ( λ yᵉ → Σᵉ (xᵉ ≠ᵉ yᵉ)
            ( λ np'ᵉ →
              Idᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( np'ᵉ))
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))))) →
      (qᵉ : is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ)) →
      (rᵉ : is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ)) →
      (sᵉ : is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ)) →
      (tᵉ : is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) jᵉ)) →
      Idᵉ
        ( pr1ᵉ
          ( cases-orientation-two-elements-countᵉ iᵉ jᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))
            ( two-elementsᵉ)
            ( qᵉ)
            ( rᵉ)
            ( sᵉ)))
        ( jᵉ)
    cases-eq-orientation-two-elements-countᵉ
      iᵉ jᵉ npᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ tᵉ) = tᵉ
    cases-eq-orientation-two-elements-countᵉ
      iᵉ jᵉ npᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ ntᵉ) =
      ex-falsoᵉ
        ( ntᵉ
          ( ( invᵉ
            ( left-computation-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( np'ᵉ))) ∙ᵉ
            ( ( apᵉ
              ( map-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( np'ᵉ))
              ( qᵉ)) ∙ᵉ
              ( ( apᵉ (λ Yᵉ → map-transpositionᵉ Yᵉ iᵉ) Pᵉ) ∙ᵉ
                ( left-computation-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ))))))
    cases-eq-orientation-two-elements-countᵉ
      iᵉ jᵉ npᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) tᵉ = rᵉ
    cases-eq-orientation-two-elements-countᵉ
      iᵉ jᵉ npᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) tᵉ =
      ex-falsoᵉ
        ( nsᵉ
          ( ( invᵉ
              ( left-computation-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( np'ᵉ))) ∙ᵉ
            ( ( apᵉ
                ( map-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( np'ᵉ))
                ( rᵉ)) ∙ᵉ
              ( ( apᵉ (λ Yᵉ → map-transpositionᵉ Yᵉ jᵉ) Pᵉ) ∙ᵉ
                ( right-computation-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ))))))
    cases-eq-orientation-two-elements-countᵉ
      iᵉ jᵉ npᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) (inrᵉ nqᵉ) (inrᵉ nrᵉ) sᵉ tᵉ =
      ex-falsoᵉ
        ( contradiction-3-distinct-element-2-Element-Typeᵉ
          ( 2-element-type-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))
          ( pairᵉ iᵉ (inlᵉ reflᵉ))
          ( pairᵉ jᵉ (inrᵉ reflᵉ))
          ( pairᵉ
            ( xᵉ)
            (trᵉ (λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ)))
          ( λ eqᵉ → npᵉ (pr1ᵉ (pair-eq-Σᵉ eqᵉ)))
          ( λ eqᵉ → nrᵉ (invᵉ (pr1ᵉ (pair-eq-Σᵉ eqᵉ))))
          ( λ eqᵉ → nqᵉ (invᵉ (pr1ᵉ (pair-eq-Σᵉ eqᵉ)))))

    eq-orientation-two-elements-countᵉ :
      (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
      Idᵉ
        ( pr1ᵉ
          ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( jᵉ)
    eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ =
      cases-eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ
        ( two-elements-transpositionᵉ eXᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ)))
        ( has-decidable-equality-countᵉ eXᵉ
          ( pr1ᵉ
            ( two-elements-transpositionᵉ eXᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))))
          ( iᵉ))
        ( has-decidable-equality-countᵉ eXᵉ
          ( pr1ᵉ
          ( two-elements-transpositionᵉ eXᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
          ( jᵉ))
        ( has-decidable-equality-countᵉ eXᵉ
          ( pr1ᵉ
          ( pr2ᵉ
            ( two-elements-transpositionᵉ eXᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))))
          ( iᵉ))
        ( has-decidable-equality-countᵉ eXᵉ
          ( pr1ᵉ
            ( pr2ᵉ
              ( two-elements-transpositionᵉ eXᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))))
          ( jᵉ))

  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    ( Idᵉ
      ( pr1ᵉ
        ( orientation-aut-countᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( jᵉ)) →
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) →
    ( two-elementsᵉ : Σᵉ Xᵉ
      ( λ xᵉ → Σᵉ Xᵉ
        ( λ yᵉ → Σᵉ (xᵉ ≠ᵉ yᵉ)
          ( λ np'ᵉ →
            Idᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( np'ᵉ))
              ( Yᵉ))))) →
    Idᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ) two-elementsᵉ →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) jᵉ) →
    Idᵉ
      ( pr1ᵉ
        ( orientation-aut-countᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( Yᵉ)))
      ( pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ tᵉ) =
    ( apᵉ
      ( λ Y'ᵉ →
        pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Y'ᵉ)))
      ( invᵉ Pᵉ ∙ᵉ
        ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( np'ᵉ)
          ( npᵉ)
          ( qᵉ)
          ( tᵉ)))) ∙ᵉ
      ( Qᵉ ∙ᵉ
        ( ( invᵉ (eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) ∙ᵉ
          ( apᵉ
            ( λ Y'ᵉ → pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Y'ᵉ))
            ( ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
              (has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)
              ( np'ᵉ)
              ( invᵉ qᵉ)
              ( invᵉ tᵉ)) ∙ᵉ
              ( Pᵉ)))))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ ntᵉ) =
    ( inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inlᵉ qᵉ))
      ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ))
      ( ntᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inlᵉ qᵉ))
          ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ))
          ( ntᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) tᵉ =
    ( apᵉ
      ( λ Y'ᵉ →
        pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Y'ᵉ)))
      ( invᵉ Pᵉ ∙ᵉ
        ( ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( np'ᵉ)) ∙ᵉ
          ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( λ pᵉ → np'ᵉ (invᵉ pᵉ))
            ( npᵉ)
            ( sᵉ)
            ( rᵉ))))) ∙ᵉ
      ( Qᵉ ∙ᵉ
        ( ( invᵉ (eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) ∙ᵉ
          ( apᵉ
            ( λ Y'ᵉ → pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Y'ᵉ))
            ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)
              ( λ pᵉ → np'ᵉ (invᵉ pᵉ))
              ( invᵉ sᵉ)
              ( invᵉ rᵉ) ∙ᵉ
              ( ( invᵉ
                ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( np'ᵉ))) ∙ᵉ
                ( Pᵉ))))))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) tᵉ =
    ( inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inlᵉ rᵉ))
      ( nsᵉ)
      ( λ t'ᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ t'ᵉ))) ∙ᵉ
      ( invᵉ
        ( inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inlᵉ rᵉ))
          ( nsᵉ)
          ( λ t'ᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ t'ᵉ))))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inlᵉ sᵉ) tᵉ =
    ( inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inrᵉ sᵉ))
      ( nqᵉ)
      ( nrᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inrᵉ sᵉ))
          ( nqᵉ)
          ( nrᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inlᵉ tᵉ) =
    ( inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inrᵉ tᵉ))
      ( nqᵉ)
      ( nrᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inrᵉ tᵉ))
          ( nqᵉ)
          ( nrᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inrᵉ ntᵉ) =
    ( apᵉ
      ( λ wᵉ →
        pr1ᵉ
          ( cases-orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)
            ( pr1ᵉ wᵉ)
            ( pr2ᵉ wᵉ)
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                (pr1ᵉ (pr2ᵉ (pr1ᵉ wᵉ))))
              (pr1ᵉ (pr2ᵉ (pr1ᵉ wᵉ))))))
      { xᵉ =
        pairᵉ
          ( two-elements-transpositionᵉ eXᵉ Yᵉ)
          ( has-decidable-equality-countᵉ eXᵉ
            ( map-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))}
      { yᵉ =
        pairᵉ
          ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
          ( inlᵉ
            ( is-fixed-point-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)
              ( xᵉ)
              ( λ qᵉ → nqᵉ (invᵉ qᵉ))
              ( λ rᵉ → nrᵉ (invᵉ rᵉ))))}
      ( eq-pair-Σᵉ
        ( Rᵉ)
        ( eq-is-propᵉ
          ( is-prop-is-decidableᵉ
            ( is-set-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( xᵉ))
              ( xᵉ)))))) ∙ᵉ
      ( apᵉ
        ( λ wᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
              ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
              ( pr1ᵉ wᵉ)
              ( pr2ᵉ wᵉ)
              ( has-decidable-equality-countᵉ eXᵉ yᵉ iᵉ)))
        { xᵉ = pairᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ)}
        { yᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ eXᵉ xᵉ iᵉ)
            ( has-decidable-equality-countᵉ eXᵉ xᵉ jᵉ)}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ)))
          ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ)))) ∙ᵉ
        apᵉ
          ( λ kᵉ →
            pr1ᵉ
              ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ kᵉ
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) iᵉ)
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) jᵉ)
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ (pr2ᵉ kᵉ)) iᵉ)))
          ( invᵉ Rᵉ))

  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    ( Idᵉ
      ( pr1ᵉ
        ( orientation-aut-countᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( iᵉ)) →
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) →
    ( two-elementsᵉ : Σᵉ Xᵉ
      ( λ xᵉ → Σᵉ Xᵉ
        ( λ yᵉ → Σᵉ (xᵉ ≠ᵉ yᵉ)
          ( λ np'ᵉ →
            Idᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( np'ᵉ))
              ( Yᵉ))))) →
    Idᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ) two-elementsᵉ →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) jᵉ) →
    Idᵉ
      ( pr1ᵉ
        ( orientation-aut-countᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( Yᵉ)))
      ( pr1ᵉ (orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ tᵉ) =
    ( apᵉ
      ( λ Y'ᵉ →
        pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Y'ᵉ)))
      ( invᵉ Pᵉ ∙ᵉ
        ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( np'ᵉ)
          ( npᵉ)
          ( qᵉ)
          ( tᵉ)))) ∙ᵉ
      ( Qᵉ ∙ᵉ
        ( ( invᵉ (eq-orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))) ∙ᵉ
          ( apᵉ
            ( pr1ᵉ ∘ᵉ orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
            ( ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ ∘ᵉ invᵉ)) ∙ᵉ
              ( ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( λ pᵉ → npᵉ (invᵉ (invᵉ pᵉ)))
                ( np'ᵉ)
                ( invᵉ qᵉ)
                ( invᵉ tᵉ)) ∙ᵉ
                ( Pᵉ))))))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ ntᵉ) =
    ( inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inlᵉ qᵉ))
      ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ))
      ( ntᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-right-two-elements-orientation-countᵉ
          ( jᵉ)
          ( iᵉ)
          ( npᵉ ∘ᵉ invᵉ)
          ( Yᵉ)
          ( yᵉ)
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inlᵉ qᵉ))
          ( ntᵉ)
          ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ))))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) tᵉ =
    ( apᵉ
      ( λ Y'ᵉ →
        pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Y'ᵉ)))
      ( invᵉ Pᵉ ∙ᵉ
        ( ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( np'ᵉ)) ∙ᵉ
          ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( λ pᵉ → np'ᵉ (invᵉ pᵉ))
            ( npᵉ)
            ( sᵉ)
            ( rᵉ))))) ∙ᵉ
      ( Qᵉ ∙ᵉ
        ( ( invᵉ (eq-orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))) ∙ᵉ
          ( apᵉ
            ( pr1ᵉ ∘ᵉ orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
            ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ ∘ᵉ invᵉ)
                ( np'ᵉ)
                ( invᵉ rᵉ)
                ( invᵉ sᵉ) ∙ᵉ
                ( Pᵉ)))))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) tᵉ =
    ( inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ yᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inlᵉ rᵉ))
      ( nsᵉ)
      ( λ t'ᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ t'ᵉ))) ∙ᵉ
      ( invᵉ
        ( inward-edge-left-two-elements-orientation-countᵉ
          ( jᵉ)
          ( iᵉ)
          ( npᵉ ∘ᵉ invᵉ)
          ( Yᵉ)
          ( yᵉ)
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inlᵉ rᵉ))
          ( λ t'ᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ t'ᵉ))
          ( nsᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inlᵉ sᵉ) tᵉ =
    ( inward-edge-left-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inrᵉ sᵉ))
      ( nqᵉ)
      ( nrᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-right-two-elements-orientation-countᵉ
          ( jᵉ)
          ( iᵉ)
          ( npᵉ ∘ᵉ invᵉ)
          ( Yᵉ)
          ( xᵉ)
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inrᵉ sᵉ))
          ( nrᵉ)
          ( nqᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inlᵉ tᵉ) =
    ( inward-edge-right-transposition-orientation-countᵉ iᵉ jᵉ npᵉ Yᵉ xᵉ
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
      ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inrᵉ tᵉ))
      ( nqᵉ)
      ( nrᵉ)) ∙ᵉ
      ( invᵉ
        ( inward-edge-left-two-elements-orientation-countᵉ
          ( jᵉ)
          ( iᵉ)
          ( npᵉ ∘ᵉ invᵉ)
          ( Yᵉ)
          ( xᵉ)
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inrᵉ tᵉ))
          ( nrᵉ)
          ( nqᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
    iᵉ jᵉ npᵉ Qᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inrᵉ ntᵉ) =
    ( apᵉ
      ( λ wᵉ →
        pr1ᵉ
          ( cases-orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ)
            ( pr1ᵉ wᵉ)
            ( pr2ᵉ wᵉ)
            ( has-decidable-equality-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                (pr1ᵉ (pr2ᵉ (pr1ᵉ wᵉ))))
              (pr1ᵉ (pr2ᵉ (pr1ᵉ wᵉ))))))
      { xᵉ =
        pairᵉ
          ( two-elements-transpositionᵉ eXᵉ Yᵉ)
          ( has-decidable-equality-countᵉ eXᵉ
            ( map-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
            ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))}
      { yᵉ =
        pairᵉ
          ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
          ( inlᵉ
            ( is-fixed-point-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)
              ( xᵉ)
              ( λ qᵉ → nqᵉ (invᵉ qᵉ))
              ( λ rᵉ → nrᵉ (invᵉ rᵉ))))}
      ( eq-pair-Σᵉ
        ( Rᵉ)
        ( eq-is-propᵉ
          ( is-prop-is-decidableᵉ
            ( is-set-countᵉ eXᵉ
              ( map-equivᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))
                ( xᵉ))
              ( xᵉ)))))) ∙ᵉ
      ( apᵉ
        ( λ wᵉ →
          pr1ᵉ
            ( cases-orientation-two-elements-countᵉ jᵉ iᵉ Yᵉ
              ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
              ( pr1ᵉ wᵉ)
              ( pr2ᵉ wᵉ)
              ( has-decidable-equality-countᵉ eXᵉ yᵉ jᵉ)))
        { xᵉ = pairᵉ (inrᵉ nrᵉ) (inrᵉ nqᵉ)}
        { yᵉ =
          pairᵉ
            ( has-decidable-equality-countᵉ eXᵉ xᵉ jᵉ)
            ( has-decidable-equality-countᵉ eXᵉ xᵉ iᵉ)}
        ( eq-pair-Σᵉ
          ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ)))
          ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ)))) ∙ᵉ
        ( apᵉ
          ( λ kᵉ →
            pr1ᵉ
              ( cases-orientation-two-elements-countᵉ jᵉ iᵉ Yᵉ kᵉ
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) jᵉ)
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) iᵉ)
                ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ (pr2ᵉ kᵉ)) jᵉ)))
          ( invᵉ Rᵉ)))

  cases-eq-orientation-aut-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    is-decidableᵉ
      ( Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( jᵉ)) →
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) +ᵉ
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ)))
  cases-eq-orientation-aut-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ (inlᵉ qᵉ) =
    inlᵉ
      ( eq-htpyᵉ
        ( λ Yᵉ →
          eq-pair-Σᵉ
            ( cases-eq-orientation-aut-orientation-two-elements-count-leftᵉ
              ( iᵉ)
              ( jᵉ)
              ( npᵉ)
              ( qᵉ)
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( reflᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
                ( iᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
                ( jᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( jᵉ)))
            ( eq-is-propᵉ
              ( is-prop-type-Decidable-Propᵉ
                ( pr1ᵉ Yᵉ (pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Yᵉ)))))))
  cases-eq-orientation-aut-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ (inrᵉ nqᵉ) =
    inrᵉ
      ( eq-htpyᵉ
        ( λ Yᵉ →
          eq-pair-Σᵉ
            ( cases-eq-orientation-aut-orientation-two-elements-count-rightᵉ
              ( iᵉ)
              ( jᵉ)
              ( npᵉ)
              ( q'ᵉ
                ( has-decidable-equality-countᵉ eXᵉ
                  ( pr1ᵉ
                    ( orientation-aut-countᵉ
                      ( transpositionᵉ
                        ( standard-2-Element-Decidable-Subtypeᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ)))
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ))))
                  ( iᵉ)))
              ( Yᵉ)
              ( two-elements-transpositionᵉ eXᵉ Yᵉ)
              ( reflᵉ)
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
                ( iᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
                ( jᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( iᵉ))
              ( has-decidable-equality-countᵉ
                ( eXᵉ)
                ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
                ( jᵉ)))
            ( eq-is-propᵉ
              ( is-prop-type-Decidable-Propᵉ
                ( pr1ᵉ
                  ( Yᵉ)
                  ( pr1ᵉ
                    ( orientation-two-elements-countᵉ
                        jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ)))))))
    where
    q'ᵉ :
      is-decidableᵉ
        ( Idᵉ
          ( pr1ᵉ
            ( orientation-aut-countᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))))
          ( iᵉ)) →
      Idᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( iᵉ)
    q'ᵉ (inlᵉ rᵉ) = rᵉ
    q'ᵉ (inrᵉ nrᵉ) =
      ex-falsoᵉ
        ( contradiction-3-distinct-element-2-Element-Typeᵉ
          ( 2-element-type-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))
          ( pairᵉ iᵉ (inlᵉ reflᵉ))
          ( pairᵉ jᵉ (inrᵉ reflᵉ))
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( λ pᵉ → npᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ qᵉ → nqᵉ (pr1ᵉ (pair-eq-Σᵉ (invᵉ qᵉ))))
          ( λ rᵉ → nrᵉ (pr1ᵉ (pair-eq-Σᵉ (invᵉ rᵉ)))))

  eq-orientation-aut-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
      ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) +ᵉ
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ)))
  eq-orientation-aut-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ =
    cases-eq-orientation-aut-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ
      (has-decidable-equality-countᵉ eXᵉ
        ( pr1ᵉ
          ( orientation-aut-countᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( jᵉ))

  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ)
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
    ( two-elementsᵉ :
      Σᵉ Xᵉ
        ( λ xᵉ → Σᵉ Xᵉ
          ( λ yᵉ → Σᵉ (xᵉ ≠ᵉ yᵉ)
            ( λ np'ᵉ →
              Idᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( np'ᵉ))
                ( Yᵉ))))) →
    Idᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ) two-elementsᵉ →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ) →
    is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) jᵉ) →
    Idᵉ
      ( pr1ᵉ
        ( map-orientation-complete-undirected-graph-equivᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
          ( Yᵉ)))
      ( pr1ᵉ ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ tᵉ) =
    ( apᵉ
      ( λ Y'ᵉ →
        map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( pr1ᵉ
            ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Y'ᵉ)))
      ( ( apᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( invᵉ Pᵉ ∙ᵉ
          ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( np'ᵉ)
            ( npᵉ)
            ( qᵉ)
            ( tᵉ)))) ∙ᵉ
        ( eq-transposition-precomp-standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ)))) ∙ᵉ
      ( ( apᵉ
        ( map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) ∙ᵉ
        ( ( apᵉ
          ( λ eᵉ → map-equivᵉ eᵉ jᵉ)
          { xᵉ =
            inv-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))}
          ( own-inverse-is-involutionᵉ
            ( is-involution-map-transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))))) ∙ᵉ
          ( ( right-computation-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)) ∙ᵉ
            ( invᵉ (eq-orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ)) ∙ᵉ
              ( apᵉ
              ( λ Y'ᵉ → pr1ᵉ (orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Y'ᵉ))
              ( ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ ∘ᵉ invᵉ)) ∙ᵉ
                ( ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( λ pᵉ → npᵉ (invᵉ (invᵉ pᵉ)))
                  ( np'ᵉ)
                  ( invᵉ qᵉ)
                  ( invᵉ tᵉ)) ∙ᵉ
                  ( Pᵉ))))))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ ntᵉ) =
    ( apᵉ
      ( map-inv-equivᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( Yᵉ))
        ( yᵉ)
        ( trᵉ
          ( λ Y'ᵉ →
            type-Decidable-Propᵉ
              ( ( pr1ᵉ Y'ᵉ
                  ( map-inv-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( yᵉ)))))
          ( Pᵉ)
          ( inrᵉ
            ( invᵉ
              ( is-fixed-point-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)
                ( yᵉ)
                ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ s'ᵉ))
                ( λ tᵉ → ntᵉ (invᵉ tᵉ))))))
        ( trᵉ
          ( λ Y'ᵉ →
            type-Decidable-Propᵉ
              ( pr1ᵉ Y'ᵉ
                ( map-inv-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( jᵉ))))
          ( Pᵉ)
          ( inlᵉ
            ( qᵉ ∙ᵉ
              ( invᵉ
                ( right-computation-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ))))))
        ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ))
        ( ntᵉ))) ∙ᵉ
      ( ( is-fixed-point-standard-transpositionᵉ
        ( has-decidable-equality-countᵉ eXᵉ)
        ( npᵉ)
        ( yᵉ)
        ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ s'ᵉ))
        ( λ tᵉ → ntᵉ (invᵉ tᵉ))) ∙ᵉ
        ( invᵉ
          ( inward-edge-right-two-elements-orientation-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ yᵉ
            ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
            ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inlᵉ qᵉ))
            ( ntᵉ)
            ( λ s'ᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ s'ᵉ)))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) tᵉ =
    ( apᵉ
      ( λ Y'ᵉ →
        map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( pr1ᵉ
            ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Y'ᵉ)))
      ( ( apᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( invᵉ Pᵉ ∙ᵉ
          ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( np'ᵉ) ∙ᵉ
            ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( λ pᵉ → np'ᵉ (invᵉ pᵉ))
              ( npᵉ)
              ( sᵉ)
              ( rᵉ))))) ∙ᵉ
        ( eq-transposition-precomp-standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ)))) ∙ᵉ
      ( ( apᵉ
        ( map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) ∙ᵉ
        ( ( apᵉ
          ( λ eᵉ → map-equivᵉ eᵉ jᵉ)
          { xᵉ =
            inv-equivᵉ
              ( transpositionᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))}
          ( own-inverse-is-involutionᵉ
            ( is-involution-map-transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))))) ∙ᵉ
          ( ( right-computation-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)) ∙ᵉ
            ( ( invᵉ (eq-orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))) ∙ᵉ
              ( apᵉ
                ( pr1ᵉ ∘ᵉ orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
                ( eq-equal-elements-standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ ∘ᵉ invᵉ)
                    ( np'ᵉ)
                    ( invᵉ rᵉ)
                    ( invᵉ sᵉ) ∙ᵉ
                    ( Pᵉ)))))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) tᵉ =
      apᵉ
        ( map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
          ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ))
          ( yᵉ)
          ( trᵉ
            ( λ Y'ᵉ →
              type-Decidable-Propᵉ
                ( pr1ᵉ Y'ᵉ
                  ( map-inv-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( yᵉ))))
            ( Pᵉ)
            ( inrᵉ
              ( invᵉ
                ( is-fixed-point-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)
                  ( yᵉ)
                  ( λ s'ᵉ → nsᵉ (invᵉ s'ᵉ))
                  ( λ tᵉ → np'ᵉ (rᵉ ∙ᵉ tᵉ))))))
          ( trᵉ
            ( λ Y'ᵉ →
              type-Decidable-Propᵉ
                ( pr1ᵉ Y'ᵉ
                  ( map-inv-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( iᵉ))))
            ( Pᵉ)
            ( inlᵉ
              ( rᵉ ∙ᵉ
                invᵉ
                  ( left-computation-standard-transpositionᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ)))))
          ( nsᵉ)
          ( λ tᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ tᵉ))) ∙ᵉ
        ( ( is-fixed-point-standard-transpositionᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ)
            ( yᵉ)
            ( λ s'ᵉ → nsᵉ (invᵉ s'ᵉ))
            ( λ tᵉ → np'ᵉ (rᵉ ∙ᵉ tᵉ))) ∙ᵉ
          ( invᵉ
            ( inward-edge-left-two-elements-orientation-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ yᵉ
              ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ yᵉ)) Pᵉ (inrᵉ reflᵉ))
              ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inlᵉ rᵉ))
              ( λ t'ᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ t'ᵉ))
              ( nsᵉ))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inlᵉ sᵉ) tᵉ =
      apᵉ
        ( map-inv-equivᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))
        ( inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
          ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
            ( transpositionᵉ
              ( standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))
            ( Yᵉ))
          ( xᵉ)
          ( trᵉ
            ( λ Y'ᵉ →
              type-Decidable-Propᵉ
                ( pr1ᵉ Y'ᵉ
                    ( map-inv-equivᵉ
                      ( transpositionᵉ
                        ( standard-2-Element-Decidable-Subtypeᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ)))
                      ( xᵉ))))
            ( Pᵉ)
            ( inlᵉ
              ( invᵉ
                ( is-fixed-point-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)
                  ( xᵉ)
                  ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                  ( λ rᵉ → nrᵉ (invᵉ rᵉ))))))
          ( trᵉ
            ( λ Y'ᵉ →
              type-Decidable-Propᵉ
                ( pr1ᵉ Y'ᵉ
                  ( map-inv-equivᵉ
                    ( transpositionᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)))
                    ( jᵉ))))
            ( Pᵉ)
            ( inrᵉ
              ( sᵉ ∙ᵉ
                ( invᵉ
                  ( right-computation-standard-transpositionᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ))))))
          ( nqᵉ)
          ( nrᵉ)) ∙ᵉ
        ( is-fixed-point-standard-transpositionᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ)
          ( xᵉ)
          ( λ qᵉ → nqᵉ (invᵉ qᵉ))
          ( λ rᵉ → nrᵉ (invᵉ rᵉ)) ∙ᵉ
          ( invᵉ
            ( inward-edge-right-two-elements-orientation-countᵉ
              jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ xᵉ
              ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
              ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ iᵉ)) Pᵉ (inrᵉ sᵉ))
              ( nrᵉ)
              ( nqᵉ))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inlᵉ tᵉ) =
    ( apᵉ
      ( map-inv-equivᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
          ( Yᵉ))
        ( xᵉ)
        ( trᵉ
          ( λ Y'ᵉ →
            type-Decidable-Propᵉ
              ( pr1ᵉ Y'ᵉ
                ( map-inv-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( xᵉ))))
          ( Pᵉ)
          ( inlᵉ
            ( invᵉ
              ( is-fixed-point-standard-transpositionᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)
                ( xᵉ)
                ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                ( λ rᵉ → nrᵉ (invᵉ rᵉ))))))
        ( trᵉ
          ( λ Y'ᵉ →
            type-Decidable-Propᵉ
              ( pr1ᵉ Y'ᵉ
                ( map-inv-equivᵉ
                  ( transpositionᵉ
                    ( standard-2-Element-Decidable-Subtypeᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)))
                  ( iᵉ))))
          ( Pᵉ)
          ( inrᵉ
            ( tᵉ ∙ᵉ
              invᵉ
                ( left-computation-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)))))
        ( nqᵉ)
        ( nrᵉ))) ∙ᵉ
    ( ( is-fixed-point-standard-transpositionᵉ
        ( has-decidable-equality-countᵉ eXᵉ)
        ( npᵉ)
        ( xᵉ)
        ( λ qᵉ → nqᵉ (invᵉ qᵉ))
        ( λ rᵉ → nrᵉ (invᵉ rᵉ))) ∙ᵉ
      ( invᵉ
        ( inward-edge-left-two-elements-orientation-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ xᵉ
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ xᵉ)) Pᵉ (inlᵉ reflᵉ))
          ( trᵉ (λ Y'ᵉ → type-Decidable-Propᵉ (pr1ᵉ Y'ᵉ jᵉ)) Pᵉ (inrᵉ tᵉ))
          ( nrᵉ)
          ( nqᵉ))))
  cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
    iᵉ jᵉ npᵉ Yᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
    Rᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) (inrᵉ nsᵉ) (inrᵉ ntᵉ) =
    ( apᵉ
      ( map-inv-equivᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( ( apᵉ
          ( λ Y'ᵉ → pr1ᵉ (orientation-two-elements-countᵉ iᵉ jᵉ npᵉ Y'ᵉ))
          ( ( apᵉ
              ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
                ( transpositionᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ))))
              ( invᵉ Pᵉ)) ∙ᵉ
            ( ( eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)
                ( np'ᵉ)
                ( λ qᵉ → nqᵉ (invᵉ qᵉ))
                ( λ sᵉ → nsᵉ (invᵉ sᵉ))
                ( λ rᵉ → nrᵉ (invᵉ rᵉ))
                ( λ tᵉ → ntᵉ (invᵉ tᵉ))) ∙ᵉ
              ( Pᵉ)))) ∙ᵉ
        ( ( apᵉ
            ( λ kᵉ →
              pr1ᵉ
                ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ kᵉ
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) iᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) jᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ (pr2ᵉ kᵉ)) iᵉ)))
            ( Rᵉ)) ∙ᵉ
          ( apᵉ
            ( λ wᵉ →
              pr1ᵉ
                ( cases-orientation-two-elements-countᵉ iᵉ jᵉ Yᵉ
                  ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
                  ( pr1ᵉ wᵉ)
                  ( pr2ᵉ wᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ yᵉ iᵉ)))
            { xᵉ =
              pairᵉ
                ( has-decidable-equality-countᵉ eXᵉ xᵉ iᵉ)
                ( has-decidable-equality-countᵉ eXᵉ xᵉ jᵉ)}
            { yᵉ = pairᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ)}
            ( eq-pair-Σᵉ
              ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ)))
              ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ)))))))) ∙ᵉ
      ( ( is-fixed-point-standard-transpositionᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ)
          ( xᵉ)
          ( λ qᵉ → nqᵉ (invᵉ qᵉ))
          ( λ rᵉ → nrᵉ (invᵉ rᵉ))) ∙ᵉ
        ( ( apᵉ
            ( λ wᵉ →
              pr1ᵉ
                ( cases-orientation-two-elements-countᵉ jᵉ iᵉ Yᵉ
                  ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
                  ( pr1ᵉ wᵉ)
                  ( pr2ᵉ wᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ yᵉ jᵉ)))
            { xᵉ = pairᵉ (inrᵉ nrᵉ) (inrᵉ nqᵉ)}
            { yᵉ =
              pairᵉ
                ( has-decidable-equality-countᵉ eXᵉ xᵉ jᵉ)
                ( has-decidable-equality-countᵉ eXᵉ xᵉ iᵉ)}
            ( eq-pair-Σᵉ
              ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ)))
              ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ))))) ∙ᵉ
          ( apᵉ
            ( λ kᵉ →
              pr1ᵉ
                ( cases-orientation-two-elements-countᵉ jᵉ iᵉ Yᵉ kᵉ
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) jᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ kᵉ) iᵉ)
                  ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ (pr2ᵉ kᵉ)) jᵉ)))
            ( invᵉ Rᵉ))))

  eq-map-orientation-transposition-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    Idᵉ
      ( map-orientation-complete-undirected-graph-equivᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ)))
        ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ))
      ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
  eq-map-orientation-transposition-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ =
    eq-htpyᵉ
      ( λ Yᵉ →
        eq-pair-Σᵉ
          ( cases-eq-map-orientation-transposition-orientation-two-elements-countᵉ
            ( iᵉ)
            ( jᵉ)
            ( npᵉ)
            ( Yᵉ)
            ( two-elements-transpositionᵉ eXᵉ Yᵉ)
            ( reflᵉ)
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( iᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
              ( jᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( iᵉ))
            ( has-decidable-equality-countᵉ
              ( eXᵉ)
              ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
              ( jᵉ)))
          ( eq-is-propᵉ
            ( is-prop-type-Decidable-Propᵉ
              ( pr1ᵉ Yᵉ
                ( pr1ᵉ (orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ))))))

  equiv-fin-1-difference-orientation-two-elements-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    Finᵉ 1 ≃ᵉ
    Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
      ( λ Yᵉ → type-Decidable-Propᵉ
        ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
          ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
          ( Yᵉ)))
  pr1ᵉ (pr1ᵉ (equiv-fin-1-difference-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ) xᵉ) =
    standard-2-Element-Decidable-Subtypeᵉ (has-decidable-equality-countᵉ eXᵉ) npᵉ
  pr2ᵉ (pr1ᵉ (equiv-fin-1-difference-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ) xᵉ) qᵉ =
    npᵉ
      ( ( invᵉ (eq-orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))) ∙ᵉ
        ( ( apᵉ
            ( λ Yᵉ → pr1ᵉ (orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) Yᵉ))
            { xᵉ =
              standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ ∘ᵉ invᵉ)}
            { yᵉ =
              standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)}
            ( invᵉ
              ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ)))) ∙ᵉ
            ( invᵉ (apᵉ pr1ᵉ qᵉ) ∙ᵉ
              eq-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)))
  pr2ᵉ (equiv-fin-1-difference-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ) =
    is-equiv-is-invertibleᵉ
      ( λ xᵉ → inrᵉ starᵉ)
      ( λ Tᵉ →
        eq-pair-Σᵉ
          ( retraction-fin-1-difference-orientation-two-elements-countᵉ
            ( Tᵉ)
            ( two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ))
            ( reflᵉ)
            ( has-decidable-equality-countᵉ
              (eXᵉ) (pr1ᵉ (two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ))) (iᵉ))
            ( has-decidable-equality-countᵉ
              (eXᵉ) (pr1ᵉ (two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ))) (jᵉ))
            ( has-decidable-equality-countᵉ
              (eXᵉ) (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ)))) (iᵉ))
            ( has-decidable-equality-countᵉ
              (eXᵉ) (pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ)))) (jᵉ)))
          ( eq-is-propᵉ
            ( is-prop-type-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
                ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
                ( pr1ᵉ Tᵉ)))))
      ( section-fin-1-difference-orientation-two-elements-countᵉ)
    where
    retraction-fin-1-difference-orientation-two-elements-countᵉ :
      ( Tᵉ :
        Σᵉ ( 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
          ( λ Yᵉ →
            type-Decidable-Propᵉ
              ( 2-Element-Decidable-Subtype-subtype-pointwise-differenceᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
                ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
                ( Yᵉ)))) →
      ( two-elementsᵉ : Σᵉ Xᵉ
        ( λ xᵉ → Σᵉ Xᵉ
          ( λ yᵉ → Σᵉ (xᵉ ≠ᵉ yᵉ)
            ( λ np'ᵉ →
              Idᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( np'ᵉ))
                ( pr1ᵉ Tᵉ))))) →
      Idᵉ two-elementsᵉ (two-elements-transpositionᵉ eXᵉ (pr1ᵉ Tᵉ)) →
      is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) iᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ two-elementsᵉ) jᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) iᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elementsᵉ)) jᵉ) →
      Idᵉ
        ( standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ))
        ( pr1ᵉ Tᵉ)
    retraction-fin-1-difference-orientation-two-elements-countᵉ
      Tᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Qᵉ (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ tᵉ) =
        apᵉ
        ( λ wᵉ →
          standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            {xᵉ = pr1ᵉ wᵉ}
            {yᵉ = jᵉ}
            ( pr2ᵉ wᵉ))
        { xᵉ = pairᵉ iᵉ npᵉ}
        { yᵉ = pairᵉ xᵉ (λ pᵉ → npᵉ (invᵉ qᵉ ∙ᵉ pᵉ))}
        ( eq-pair-Σᵉ
          ( invᵉ qᵉ)
          ( eq-is-propᵉ is-prop-negᵉ)) ∙ᵉ
        ( ( apᵉ
            ( λ wᵉ →
              standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                {xᵉ = xᵉ}
                {yᵉ = pr1ᵉ wᵉ}
                ( pr2ᵉ wᵉ))
            { xᵉ = pairᵉ jᵉ (λ pᵉ → npᵉ (invᵉ qᵉ ∙ᵉ pᵉ))}
            { yᵉ = pairᵉ yᵉ np'ᵉ}
            ( eq-pair-Σᵉ
              ( invᵉ tᵉ)
              ( eq-is-propᵉ is-prop-negᵉ))) ∙ᵉ
          ( Pᵉ))
    retraction-fin-1-difference-orientation-two-elements-countᵉ
      Tᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Qᵉ (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ ntᵉ) =
      ex-falsoᵉ
        ( pr2ᵉ Tᵉ
          ( eq-pair-Σᵉ
            ( ( inward-edge-left-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
                ( pr1ᵉ Tᵉ)
                ( yᵉ)
                ( trᵉ
                  ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
                  ( Pᵉ)
                  ( inrᵉ reflᵉ))
                ( trᵉ
                  ( λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ (pr1ᵉ Tᵉ) zᵉ))
                  ( qᵉ)
                  ( trᵉ
                    ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))
                    ( Pᵉ)
                    ( inlᵉ reflᵉ)))
                ( λ sᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ sᵉ))
                ( ntᵉ)) ∙ᵉ
              ( invᵉ
                ( inward-edge-right-two-elements-orientation-countᵉ jᵉ iᵉ
                  ( npᵉ ∘ᵉ invᵉ)
                  ( pr1ᵉ Tᵉ)
                  ( yᵉ)
                  ( trᵉ
                    ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
                    ( Pᵉ)
                    ( inrᵉ reflᵉ))
                  ( trᵉ
                    ( λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ (pr1ᵉ Tᵉ) zᵉ))
                    ( qᵉ)
                    ( trᵉ
                      ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))
                      ( Pᵉ)
                      ( inlᵉ reflᵉ)))
                  ( ntᵉ)
                  ( λ sᵉ → np'ᵉ (qᵉ ∙ᵉ invᵉ sᵉ)))))
            ( eq-is-propᵉ
              ( is-prop-type-Decidable-Propᵉ
                ( pr1ᵉ
                  ( pr1ᵉ Tᵉ)
                  ( pr1ᵉ
                    ( orientation-two-elements-countᵉ
                        jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) (pr1ᵉ Tᵉ))))))))
    retraction-fin-1-difference-orientation-two-elements-countᵉ
      Tᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Qᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) tᵉ =
      apᵉ
        ( λ wᵉ →
          standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            {xᵉ = pr1ᵉ wᵉ}
            {yᵉ = jᵉ}
            ( pr2ᵉ wᵉ))
        { xᵉ = pairᵉ iᵉ npᵉ}
        { yᵉ = pairᵉ yᵉ (λ pᵉ → npᵉ (invᵉ sᵉ ∙ᵉ pᵉ))}
        ( eq-pair-Σᵉ
          ( invᵉ sᵉ)
          ( eq-is-propᵉ is-prop-negᵉ)) ∙ᵉ
        ( ( apᵉ
            ( λ wᵉ →
              standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                {xᵉ = yᵉ}
                {yᵉ = pr1ᵉ wᵉ}
                ( pr2ᵉ wᵉ))
            { xᵉ = pairᵉ jᵉ (λ pᵉ → npᵉ (invᵉ sᵉ ∙ᵉ pᵉ))}
            { yᵉ = pairᵉ xᵉ (λ pᵉ → np'ᵉ (invᵉ pᵉ))}
            ( eq-pair-Σᵉ
              ( invᵉ rᵉ)
              ( eq-is-propᵉ is-prop-negᵉ))) ∙ᵉ
          ( invᵉ
            ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( np'ᵉ)) ∙ᵉ
            ( Pᵉ)))
    retraction-fin-1-difference-orientation-two-elements-countᵉ
      Tᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Qᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) tᵉ =
      ex-falsoᵉ
        ( pr2ᵉ Tᵉ
          ( eq-pair-Σᵉ
            ( inward-edge-right-two-elements-orientation-countᵉ iᵉ jᵉ npᵉ
              ( pr1ᵉ Tᵉ)
              ( yᵉ)
              ( trᵉ
                ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
                ( Pᵉ)
                ( inrᵉ reflᵉ))
              ( trᵉ
                ( λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ (pr1ᵉ Tᵉ) zᵉ))
                ( rᵉ)
                ( trᵉ
                  ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))
                  ( Pᵉ)
                  ( inlᵉ reflᵉ)))
              ( nsᵉ)
              ( λ tᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ tᵉ)) ∙ᵉ
              ( invᵉ
                ( inward-edge-left-two-elements-orientation-countᵉ jᵉ iᵉ
                  ( npᵉ ∘ᵉ invᵉ)
                  ( pr1ᵉ Tᵉ)
                  ( yᵉ)
                  ( trᵉ
                    ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
                    ( Pᵉ)
                    ( inrᵉ reflᵉ))
                  ( trᵉ
                    ( λ zᵉ → type-Decidable-Propᵉ (pr1ᵉ (pr1ᵉ Tᵉ) zᵉ))
                    ( rᵉ)
                    ( trᵉ
                      ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))
                      ( Pᵉ)
                      ( inlᵉ reflᵉ)))
                  ( λ tᵉ → np'ᵉ (rᵉ ∙ᵉ invᵉ tᵉ))
                  ( nsᵉ))))
            ( eq-is-propᵉ
              ( is-prop-type-Decidable-Propᵉ
                ( pr1ᵉ
                  ( pr1ᵉ Tᵉ)
                  ( pr1ᵉ
                    ( orientation-two-elements-countᵉ
                        jᵉ iᵉ (npᵉ ∘ᵉ invᵉ) (pr1ᵉ Tᵉ))))))))
    retraction-fin-1-difference-orientation-two-elements-countᵉ
      Tᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ))) Qᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) sᵉ tᵉ =
      ex-falsoᵉ
        ( pr2ᵉ Tᵉ
          ( apᵉ
            ( λ wᵉ →
              cases-orientation-two-elements-countᵉ iᵉ jᵉ
                ( pr1ᵉ Tᵉ)
                ( wᵉ)
                ( has-decidable-equality-countᵉ eXᵉ
                  ( pr1ᵉ wᵉ) iᵉ)
                ( has-decidable-equality-countᵉ eXᵉ
                  (pr1ᵉ wᵉ) jᵉ)
                ( has-decidable-equality-countᵉ eXᵉ
                  (pr1ᵉ (pr2ᵉ wᵉ)) iᵉ))
            ( invᵉ Qᵉ) ∙ᵉ
            ( ( apᵉ
                ( λ Dᵉ →
                  cases-orientation-two-elements-countᵉ iᵉ jᵉ
                    ( pr1ᵉ Tᵉ)
                    ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
                    ( pr1ᵉ Dᵉ)
                    ( pr2ᵉ Dᵉ)
                    ( has-decidable-equality-countᵉ eXᵉ yᵉ iᵉ))
                { yᵉ = pairᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ)}
                ( eq-pair-Σᵉ
                  ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ)))
                  ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ))))) ∙ᵉ
              ( apᵉ
                ( λ Dᵉ →
                  cases-orientation-two-elements-countᵉ jᵉ iᵉ
                    ( pr1ᵉ Tᵉ)
                    ( pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ np'ᵉ Pᵉ)))
                    ( pr1ᵉ Dᵉ)
                    ( pr2ᵉ Dᵉ)
                    ( has-decidable-equality-countᵉ eXᵉ yᵉ jᵉ))
                { xᵉ = pairᵉ (inrᵉ nrᵉ) (inrᵉ nqᵉ)}
                { yᵉ =
                  pairᵉ
                    ( has-decidable-equality-countᵉ eXᵉ xᵉ jᵉ)
                    ( has-decidable-equality-countᵉ eXᵉ xᵉ iᵉ)}
                ( eq-pair-Σᵉ
                  ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ jᵉ)))
                  ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-set-countᵉ eXᵉ xᵉ iᵉ)))) ∙ᵉ
                ( apᵉ
                  ( λ wᵉ →
                    cases-orientation-two-elements-countᵉ jᵉ iᵉ
                      ( pr1ᵉ Tᵉ)
                      ( wᵉ)
                      ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ wᵉ) jᵉ)
                      ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ wᵉ) iᵉ)
                      ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ (pr2ᵉ wᵉ)) jᵉ))
                  ( Qᵉ))))))
    section-fin-1-difference-orientation-two-elements-countᵉ :
      ( ( λ xᵉ → inrᵉ {Aᵉ = emptyᵉ} starᵉ) ∘ᵉ
        pr1ᵉ (equiv-fin-1-difference-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) ~ᵉ
      ( idᵉ)
    section-fin-1-difference-orientation-two-elements-countᵉ (inrᵉ starᵉ) = reflᵉ

  eq-orientation-pointwise-difference-two-elements-countᵉ :
    (iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    Idᵉ
      ( 1ᵉ)
      ( number-of-elements-is-finiteᵉ
        ( is-finite-subtype-pointwise-differenceᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
          ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))))
  eq-orientation-pointwise-difference-two-elements-countᵉ iᵉ jᵉ npᵉ =
    apᵉ
      ( number-of-elements-has-finite-cardinalityᵉ)
      ( all-elements-equal-has-finite-cardinalityᵉ
        ( pairᵉ
          ( 1ᵉ)
          ( unit-trunc-Propᵉ
            ( equiv-fin-1-difference-orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)))
        ( has-finite-cardinality-is-finiteᵉ
          ( is-finite-subtype-pointwise-differenceᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
            ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ)))))

  cases-not-even-difference-orientation-aut-transposition-countᵉ :
    ( iᵉ jᵉ : Xᵉ) (npᵉ : iᵉ ≠ᵉ jᵉ) →
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)) +ᵉ
    ( Idᵉ
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( even-difference-orientation-Complete-Undirected-Graphᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
      ( orientation-aut-countᵉ
        ( transpositionᵉ
          ( standard-2-Element-Decidable-Subtypeᵉ
            ( has-decidable-equality-countᵉ eXᵉ)
            ( npᵉ))))
      ( map-orientation-complete-undirected-graph-equivᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( transpositionᵉ (standard-2-Element-Decidable-Subtypeᵉ
          ( has-decidable-equality-countᵉ eXᵉ)
          ( npᵉ)))
        ( orientation-aut-countᵉ
          ( transpositionᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ))))))
  cases-not-even-difference-orientation-aut-transposition-countᵉ
    iᵉ jᵉ npᵉ (inlᵉ plᵉ) =
    trᵉ
      ( λ dᵉ →
        ¬ᵉ ( sim-equivalence-relationᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
          ( dᵉ)
          ( map-orientation-complete-undirected-graph-equivᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( transpositionᵉ (standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
            ( dᵉ))))
      ( invᵉ plᵉ)
      ( trᵉ
        ( λ dᵉ →
          ¬ᵉ ( sim-equivalence-relationᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( orientation-two-elements-countᵉ iᵉ jᵉ npᵉ)
            ( dᵉ)))
        ( invᵉ
          ( eq-map-orientation-transposition-orientation-two-elements-countᵉ
              iᵉ jᵉ npᵉ))
        ( λ pᵉ →
          neq-inl-inrᵉ
            ( pᵉ ∙ᵉ
              ( invᵉ
                ( apᵉ mod-two-ℕᵉ
                  ( eq-orientation-pointwise-difference-two-elements-countᵉ
                      iᵉ jᵉ npᵉ))))))
  cases-not-even-difference-orientation-aut-transposition-countᵉ
    iᵉ jᵉ npᵉ (inrᵉ prᵉ) =
    trᵉ
      ( λ dᵉ →
        ¬ᵉ ( sim-equivalence-relationᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
          ( dᵉ)
          ( map-orientation-complete-undirected-graph-equivᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( transpositionᵉ (standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)))
            ( dᵉ))))
      ( invᵉ prᵉ)
      ( trᵉ
        ( λ dᵉ →
          ¬ᵉ ( sim-equivalence-relationᵉ
              ( even-difference-orientation-Complete-Undirected-Graphᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
              ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))
              ( dᵉ)))
        ( invᵉ
          ( ( apᵉ
              ( λ wᵉ →
                map-orientation-complete-undirected-graph-equivᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( transpositionᵉ wᵉ)
                  ( orientation-two-elements-countᵉ jᵉ iᵉ (npᵉ ∘ᵉ invᵉ)))
              ( is-commutative-standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( npᵉ))) ∙ᵉ
            ( eq-map-orientation-transposition-orientation-two-elements-countᵉ
                jᵉ iᵉ (npᵉ ∘ᵉ invᵉ))))
        ( λ pᵉ →
          neq-inl-inrᵉ
            ( pᵉ ∙ᵉ
              ( invᵉ
                ( apᵉ
                  ( mod-two-ℕᵉ)
                  ( eq-orientation-pointwise-difference-two-elements-countᵉ jᵉ iᵉ
                    ( npᵉ ∘ᵉ invᵉ)))))))

  not-even-difference-orientation-aut-transposition-countᵉ :
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) →
    ¬ᵉ ( sim-equivalence-relationᵉ
      ( even-difference-orientation-Complete-Undirected-Graphᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
      ( orientation-aut-countᵉ (transpositionᵉ Yᵉ))
      ( map-orientation-complete-undirected-graph-equivᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
        ( transpositionᵉ Yᵉ)
        ( orientation-aut-countᵉ (transpositionᵉ Yᵉ))))
  not-even-difference-orientation-aut-transposition-countᵉ Yᵉ =
    trᵉ
      ( λ Y'ᵉ →
        ¬ᵉ ( sim-equivalence-relationᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
          ( orientation-aut-countᵉ (transpositionᵉ Y'ᵉ))
          ( map-orientation-complete-undirected-graph-equivᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( transpositionᵉ Y'ᵉ)
            ( orientation-aut-countᵉ (transpositionᵉ Y'ᵉ)))))
      ( pr2ᵉ (pr2ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
      ( cases-not-even-difference-orientation-aut-transposition-countᵉ
        ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
        ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
        ( pr1ᵉ (pr2ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))
        ( eq-orientation-aut-orientation-two-elements-countᵉ
          ( pr1ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))
          ( pr1ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ)))
          ( pr1ᵉ (pr2ᵉ (pr2ᵉ (two-elements-transpositionᵉ eXᵉ Yᵉ))))))

  inv-orientationᵉ :
    ( Tᵉ :
      quotient-signᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))) →
    is-decidableᵉ
      ( is-in-equivalence-classᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( Tᵉ)
        ( canonical-orientation-countᵉ)) →
    Finᵉ 2
  inv-orientationᵉ Tᵉ (inlᵉ Pᵉ) = inlᵉ (inrᵉ starᵉ)
  inv-orientationᵉ Tᵉ (inrᵉ NPᵉ) = inrᵉ starᵉ

  equiv-fin-2-quotient-sign-countᵉ :
    Finᵉ 2 ≃ᵉ
    ( quotient-signᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
  pr1ᵉ equiv-fin-2-quotient-sign-countᵉ (inlᵉ (inrᵉ starᵉ)) =
    classᵉ
      ( even-difference-orientation-Complete-Undirected-Graphᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
      ( canonical-orientation-countᵉ)
  pr1ᵉ equiv-fin-2-quotient-sign-countᵉ (inrᵉ starᵉ) =
    classᵉ
      ( even-difference-orientation-Complete-Undirected-Graphᵉ
        ( number-of-elements-countᵉ eXᵉ)
        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
      ( transitive-canonical-orientation-countᵉ)
  pr2ᵉ equiv-fin-2-quotient-sign-countᵉ =
    is-equiv-is-invertibleᵉ
      ( λ Tᵉ →
        inv-orientationᵉ
          ( Tᵉ)
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( Tᵉ)
            ( canonical-orientation-countᵉ)))
      ( λ Tᵉ →
        retraction-orientationᵉ
          ( Tᵉ)
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( Tᵉ)
            ( canonical-orientation-countᵉ)))
      ( λ kᵉ →
        section-orientationᵉ
          kᵉ
          ( is-decidable-is-in-equivalence-class-is-decidableᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( is-decidable-even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( pr1ᵉ equiv-fin-2-quotient-sign-countᵉ kᵉ)
            ( canonical-orientation-countᵉ)))
    where
    cases-retraction-orientationᵉ :
      (Tᵉ :
        equivalence-classᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))) →
      ¬ᵉ ( is-in-equivalence-classᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ
          (number-of-elements-countᵉ eXᵉ)
          (pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( Tᵉ)
        ( canonical-orientation-countᵉ)) →
      ( tᵉ :
        orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))) →
      Idᵉ
        ( classᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
          ( tᵉ))
        ( Tᵉ) →
      ( kᵉ : Finᵉ 2ᵉ) →
      Idᵉ
        ( kᵉ)
        ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( tᵉ)
          ( canonical-orientation-countᵉ)) →
      is-in-equivalence-classᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( Tᵉ)
        ( transitive-canonical-orientation-countᵉ)
    cases-retraction-orientationᵉ Tᵉ NHᵉ tᵉ qᵉ (inlᵉ (inrᵉ starᵉ)) rᵉ =
      ex-falsoᵉ
        ( NHᵉ
          ( trᵉ
            ( λ xᵉ →
              is-in-equivalence-classᵉ
                ( even-difference-orientation-Complete-Undirected-Graphᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
                ( xᵉ)
                ( canonical-orientation-countᵉ))
            ( qᵉ)
            ( rᵉ)))
    cases-retraction-orientationᵉ Tᵉ NHᵉ tᵉ qᵉ (inrᵉ starᵉ) rᵉ =
      trᵉ
        (λ xᵉ →
          is-in-equivalence-classᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( xᵉ)
            ( transitive-canonical-orientation-countᵉ))
        ( qᵉ)
        ( eq-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( tᵉ)
            ( canonical-orientation-countᵉ)
            ( transitive-canonical-orientation-countᵉ)
            ( inrᵉ starᵉ)
            ( rᵉ)
            ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( transitive-canonical-orientation-countᵉ)
              ( canonical-orientation-countᵉ)
              ( inrᵉ starᵉ)
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( canonical-orientation-countᵉ)
                ( transitive-canonical-orientation-countᵉ)
                ( inrᵉ starᵉ)
                ( apᵉ
                  ( mod-two-ℕᵉ)
                  { xᵉ = 1ᵉ}
                  { yᵉ =
                    number-of-elements-is-finiteᵉ
                      ( is-finite-subtype-pointwise-differenceᵉ
                        ( number-of-elements-countᵉ eXᵉ)
                        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                        ( canonical-orientation-countᵉ)
                        ( transitive-canonical-orientation-countᵉ))}
                  ( eq-orientation-pointwise-difference-two-elements-countᵉ
                    ( first-element-countᵉ)
                    ( second-element-countᵉ)
                    ( distinct-two-elements-countᵉ))))))
    retraction-orientationᵉ :
      ( Tᵉ :
        quotient-signᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))) →
      ( Hᵉ :
        is-decidableᵉ
          (is-in-equivalence-classᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( Tᵉ)
            ( canonical-orientation-countᵉ))) →
      Idᵉ (pr1ᵉ equiv-fin-2-quotient-sign-countᵉ (inv-orientationᵉ Tᵉ Hᵉ)) Tᵉ
    retraction-orientationᵉ Tᵉ (inlᵉ Hᵉ) =
      eq-effective-quotient'ᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( canonical-orientation-countᵉ)
        ( Tᵉ)
        ( Hᵉ)
    retraction-orientationᵉ Tᵉ (inrᵉ NHᵉ) =
      eq-effective-quotient'ᵉ
        ( even-difference-orientation-Complete-Undirected-Graphᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( transitive-canonical-orientation-countᵉ)
        ( Tᵉ)
        ( apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ Tᵉ)
          ( pairᵉ
            ( is-in-equivalence-classᵉ
              ( even-difference-orientation-Complete-Undirected-Graphᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
              ( Tᵉ)
              ( transitive-canonical-orientation-countᵉ))
            ( is-prop-is-in-equivalence-classᵉ
              ( even-difference-orientation-Complete-Undirected-Graphᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
              ( Tᵉ)
              ( transitive-canonical-orientation-countᵉ)))
          ( λ (pairᵉ tᵉ rᵉ) →
            cases-retraction-orientationᵉ
              ( Tᵉ)
              ( NHᵉ)
              ( tᵉ)
              ( eq-pair-Σᵉ
                ( apᵉ
                  ( pr1ᵉ)
                  ( invᵉ
                    ( eq-has-same-elements-equivalence-classᵉ
                      ( even-difference-orientation-Complete-Undirected-Graphᵉ
                        ( number-of-elements-countᵉ eXᵉ)
                        ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
                      ( Tᵉ)
                      ( classᵉ
                        ( even-difference-orientation-Complete-Undirected-Graphᵉ
                          ( number-of-elements-countᵉ eXᵉ)
                          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
                        ( tᵉ))
                      ( rᵉ))))
                ( all-elements-equal-type-trunc-Propᵉ _ (pr2ᵉ Tᵉ)))
              ( mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( tᵉ)
                  ( canonical-orientation-countᵉ))
              ( reflᵉ)))
    section-orientationᵉ :
      (kᵉ : Finᵉ 2ᵉ)
      ( Dᵉ : is-decidableᵉ
        ( is-in-equivalence-classᵉ
          ( even-difference-orientation-Complete-Undirected-Graphᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
          ( pr1ᵉ equiv-fin-2-quotient-sign-countᵉ kᵉ)
          ( canonical-orientation-countᵉ))) →
      Idᵉ
        ( inv-orientationᵉ
          ( pr1ᵉ equiv-fin-2-quotient-sign-countᵉ kᵉ)
          ( Dᵉ))
        ( kᵉ)
    section-orientationᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ Qᵉ) = reflᵉ
    section-orientationᵉ (inlᵉ (inrᵉ starᵉ)) (inrᵉ NQᵉ) =
      ex-falsoᵉ
        ( NQᵉ
          ( refl-equivalence-relationᵉ
            ( even-difference-orientation-Complete-Undirected-Graphᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( Xᵉ ,ᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
            ( canonical-orientation-countᵉ)))
    section-orientationᵉ (inrᵉ starᵉ) (inlᵉ Qᵉ) =
      ex-falsoᵉ
        ( neq-inl-inrᵉ
          ( Qᵉ ∙ᵉ
            invᵉ
              ( is-symmetric-mod-two-number-of-differences-orientation-Complete-Undirected-Graphᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( Xᵉ ,ᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( canonical-orientation-countᵉ)
                ( transitive-canonical-orientation-countᵉ)
                ( inrᵉ starᵉ)
                ( apᵉ mod-two-ℕᵉ
                  ( eq-orientation-pointwise-difference-two-elements-countᵉ
                    ( first-element-countᵉ)
                    ( second-element-countᵉ)
                    ( distinct-two-elements-countᵉ))))))
    section-orientationᵉ (inrᵉ starᵉ) (inrᵉ NQᵉ) = reflᵉ

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ) (ineqᵉ : leq-ℕᵉ 2 nᵉ)
  where

  equiv-fin-2-quotient-sign-equiv-Finᵉ :
    (hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) → Finᵉ 2 ≃ᵉ quotient-signᵉ nᵉ Xᵉ
  equiv-fin-2-quotient-sign-equiv-Finᵉ hᵉ =
    trᵉ
      ( λ eᵉ → Finᵉ 2 ≃ᵉ quotient-signᵉ nᵉ (pairᵉ (type-UU-Finᵉ nᵉ Xᵉ) eᵉ))
      ( all-elements-equal-type-trunc-Propᵉ
        ( unit-trunc-Propᵉ (equiv-countᵉ (pairᵉ nᵉ hᵉ)))
        ( pr2ᵉ Xᵉ))
      ( equiv-fin-2-quotient-sign-countᵉ (pairᵉ nᵉ hᵉ) ineqᵉ)
```