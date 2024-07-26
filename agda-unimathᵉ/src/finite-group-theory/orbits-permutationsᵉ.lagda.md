# Orbits of permutations

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.orbits-permutationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.euclidean-division-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-equivalence-relationsᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.iterating-functionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.repetitions-of-valuesᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.image-of-mapsᵉ
open import univalent-combinatorics.pigeonhole-principleᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ orbitᵉ ofᵉ aᵉ pointᵉ `x`ᵉ forᵉ aᵉ permutationᵉ `f`ᵉ isᵉ theᵉ setᵉ ofᵉ pointᵉ obtainedᵉ byᵉ
iteratingᵉ `f`ᵉ onᵉ `x`.ᵉ

## Definition

### The groupoid of iterative orbits of an automorphism on a finite set

```agda
module _
  {lᵉ : Level} (Xᵉ : 𝔽ᵉ lᵉ) (eᵉ : type-𝔽ᵉ Xᵉ ≃ᵉ type-𝔽ᵉ Xᵉ)
  where

  iso-iterative-groupoid-automorphism-𝔽ᵉ : (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) → UUᵉ lᵉ
  iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ yᵉ =
    Σᵉ ℕᵉ (λ nᵉ → Idᵉ (iterateᵉ nᵉ (map-equivᵉ eᵉ) xᵉ) yᵉ)

  natural-isomorphism-iterative-groupoid-automorphism-𝔽ᵉ :
    (xᵉ yᵉ : type-𝔽ᵉ Xᵉ) (fᵉ : iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ yᵉ) → ℕᵉ
  natural-isomorphism-iterative-groupoid-automorphism-𝔽ᵉ xᵉ yᵉ = pr1ᵉ

  id-iso-iterative-groupoid-automorphism-𝔽ᵉ :
    (xᵉ : type-𝔽ᵉ Xᵉ) → iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ xᵉ
  pr1ᵉ (id-iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ) = 0
  pr2ᵉ (id-iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ) = reflᵉ

  comp-iso-iterative-groupoid-automorphism-𝔽ᵉ :
    {xᵉ yᵉ zᵉ : type-𝔽ᵉ Xᵉ} →
    iso-iterative-groupoid-automorphism-𝔽ᵉ yᵉ zᵉ →
    iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ yᵉ →
    iso-iterative-groupoid-automorphism-𝔽ᵉ xᵉ zᵉ
  pr1ᵉ (comp-iso-iterative-groupoid-automorphism-𝔽ᵉ (pairᵉ nᵉ qᵉ) (pairᵉ mᵉ pᵉ)) =
    nᵉ +ℕᵉ mᵉ
  pr2ᵉ (comp-iso-iterative-groupoid-automorphism-𝔽ᵉ (pairᵉ nᵉ qᵉ) (pairᵉ mᵉ pᵉ)) =
    iterate-add-ℕᵉ nᵉ mᵉ (map-equivᵉ eᵉ) _ ∙ᵉ (apᵉ (iterateᵉ nᵉ (map-equivᵉ eᵉ)) pᵉ ∙ᵉ qᵉ)
```

## Properties

### For types equipped with a counting, orbits of permutations are finite

Theᵉ mapᵉ `iᵉ ↦ᵉ eⁱᵉ a`ᵉ repeatsᵉ itself.ᵉ

```agda
module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) (eXᵉ : countᵉ Xᵉ) (fᵉ : Autᵉ Xᵉ) (aᵉ : Xᵉ)
  where

  repetition-iterate-automorphism-Finᵉ :
    repetition-of-valuesᵉ
      ( λ (kᵉ : Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ eXᵉ))) →
        iterateᵉ
          ( nat-Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ eXᵉ)) kᵉ)
          ( map-equivᵉ fᵉ)
          ( aᵉ))
  repetition-iterate-automorphism-Finᵉ =
    repetition-of-values-le-countᵉ
      ( count-Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ eXᵉ)))
      ( eXᵉ)
      ( λ kᵉ →
        iterateᵉ
          ( nat-Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ eXᵉ)) kᵉ)
          ( map-equivᵉ fᵉ)
          ( aᵉ))
      ( succ-le-ℕᵉ (number-of-elements-countᵉ eXᵉ))

  point1-iterate-ℕᵉ : ℕᵉ
  point1-iterate-ℕᵉ =
    nat-Finᵉ
      ( succ-ℕᵉ (number-of-elements-countᵉ eXᵉ))
      ( pr1ᵉ (pr1ᵉ repetition-iterate-automorphism-Finᵉ))

  point2-iterate-ℕᵉ : ℕᵉ
  point2-iterate-ℕᵉ =
    nat-Finᵉ
      ( succ-ℕᵉ (number-of-elements-countᵉ eXᵉ))
      ( pr1ᵉ (pr2ᵉ (pr1ᵉ repetition-iterate-automorphism-Finᵉ)))

  neq-points-iterate-ℕᵉ : point1-iterate-ℕᵉ ≠ᵉ point2-iterate-ℕᵉ
  neq-points-iterate-ℕᵉ pᵉ =
    pr2ᵉ
      ( pr2ᵉ (pr1ᵉ repetition-iterate-automorphism-Finᵉ))
      ( is-injective-nat-Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ eXᵉ)) pᵉ)

  two-points-iterate-ordered-ℕᵉ :
    ( point1-iterate-ℕᵉ ≤-ℕᵉ point2-iterate-ℕᵉ) +ᵉ
    ( point2-iterate-ℕᵉ ≤-ℕᵉ point1-iterate-ℕᵉ) →
    Σᵉ ( ℕᵉ)
      ( λ nᵉ →
        Σᵉ ( ℕᵉ)
          ( λ mᵉ →
            ( le-ℕᵉ mᵉ nᵉ) ×ᵉ
            ( Idᵉ (iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ) (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))))
  pr1ᵉ (two-points-iterate-ordered-ℕᵉ (inlᵉ pᵉ)) = point2-iterate-ℕᵉ
  pr1ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inlᵉ pᵉ))) = point1-iterate-ℕᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inlᵉ pᵉ)))) =
    le-leq-neq-ℕᵉ pᵉ neq-points-iterate-ℕᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inlᵉ pᵉ)))) =
    invᵉ (pr2ᵉ repetition-iterate-automorphism-Finᵉ)
  pr1ᵉ (two-points-iterate-ordered-ℕᵉ (inrᵉ pᵉ)) = point1-iterate-ℕᵉ
  pr1ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inrᵉ pᵉ))) = point2-iterate-ℕᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inrᵉ pᵉ)))) =
    le-leq-neq-ℕᵉ pᵉ λ eᵉ → neq-points-iterate-ℕᵉ (invᵉ eᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (two-points-iterate-ordered-ℕᵉ (inrᵉ pᵉ)))) =
    pr2ᵉ repetition-iterate-automorphism-Finᵉ

  leq-greater-point-number-elementsᵉ :
    ( pᵉ :
      ( point1-iterate-ℕᵉ ≤-ℕᵉ point2-iterate-ℕᵉ) +ᵉ
      ( point2-iterate-ℕᵉ ≤-ℕᵉ point1-iterate-ℕᵉ)) →
    pr1ᵉ (two-points-iterate-ordered-ℕᵉ pᵉ) ≤-ℕᵉ number-of-elements-countᵉ eXᵉ
  leq-greater-point-number-elementsᵉ (inlᵉ pᵉ) =
    ( upper-bound-nat-Finᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pr1ᵉ (pr2ᵉ (pr1ᵉ repetition-iterate-automorphism-Finᵉ))))
  leq-greater-point-number-elementsᵉ (inrᵉ pᵉ) =
    ( upper-bound-nat-Finᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pr1ᵉ (pr1ᵉ repetition-iterate-automorphism-Finᵉ)))

  abstract
    min-repeatingᵉ :
      minimal-element-ℕᵉ
        ( λ nᵉ →
          Σᵉ ( ℕᵉ)
            ( λ mᵉ →
              ( le-ℕᵉ mᵉ nᵉ) ×ᵉ
              ( Idᵉ (iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ) (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))))
    min-repeatingᵉ =
      well-ordering-principle-ℕᵉ
        ( λ nᵉ →
          Σᵉ ( ℕᵉ)
            ( λ mᵉ →
              ( le-ℕᵉ mᵉ nᵉ) ×ᵉ
              ( Idᵉ (iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ) (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))))
        ( λ nᵉ →
          is-decidable-bounded-Σ-ℕᵉ nᵉ ( λ mᵉ → le-ℕᵉ mᵉ nᵉ)
            ( λ mᵉ → Idᵉ (iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ) (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))
            ( λ mᵉ → is-decidable-le-ℕᵉ mᵉ nᵉ)
            ( λ mᵉ →
              has-decidable-equality-countᵉ eXᵉ
                ( iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ)
                ( iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))
            ( λ mᵉ pᵉ → leq-le-ℕᵉ mᵉ nᵉ pᵉ))
        ( two-points-iterate-ordered-ℕᵉ
          ( linear-leq-ℕᵉ point1-iterate-ℕᵉ point2-iterate-ℕᵉ))

    first-point-min-repeatingᵉ : ℕᵉ
    first-point-min-repeatingᵉ = pr1ᵉ min-repeatingᵉ

    second-point-min-repeatingᵉ : ℕᵉ
    second-point-min-repeatingᵉ = pr1ᵉ (pr1ᵉ (pr2ᵉ min-repeatingᵉ))

    le-min-reportingᵉ : le-ℕᵉ second-point-min-repeatingᵉ first-point-min-repeatingᵉ
    le-min-reportingᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ min-repeatingᵉ)))

    is-lower-bound-min-reportingᵉ :
      is-lower-bound-ℕᵉ
        ( λ nᵉ →
          Σᵉ ( ℕᵉ)
            ( λ mᵉ →
              ( le-ℕᵉ mᵉ nᵉ) ×ᵉ
              ( Idᵉ (iterateᵉ nᵉ (map-equivᵉ fᵉ) aᵉ) (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ))))
        ( first-point-min-repeatingᵉ)
    is-lower-bound-min-reportingᵉ = pr2ᵉ (pr2ᵉ min-repeatingᵉ)

    same-image-iterate-min-reportingᵉ :
      Idᵉ ( iterateᵉ first-point-min-repeatingᵉ (map-equivᵉ fᵉ) aᵉ)
        ( iterateᵉ second-point-min-repeatingᵉ (map-equivᵉ fᵉ) aᵉ)
    same-image-iterate-min-reportingᵉ = pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ min-repeatingᵉ)))

  leq-first-point-min-reporting-succ-number-elementsᵉ :
    first-point-min-repeatingᵉ ≤-ℕᵉ (number-of-elements-countᵉ eXᵉ)
  leq-first-point-min-reporting-succ-number-elementsᵉ =
    transitive-leq-ℕᵉ
      ( first-point-min-repeatingᵉ)
      ( pr1ᵉ
        ( two-points-iterate-ordered-ℕᵉ
          ( linear-leq-ℕᵉ point1-iterate-ℕᵉ point2-iterate-ℕᵉ)))
      ( number-of-elements-countᵉ eXᵉ)
      ( leq-greater-point-number-elementsᵉ
        ( linear-leq-ℕᵉ point1-iterate-ℕᵉ point2-iterate-ℕᵉ))
      ( is-lower-bound-min-reportingᵉ
        ( pr1ᵉ
          ( two-points-iterate-ordered-ℕᵉ
            ( linear-leq-ℕᵉ point1-iterate-ℕᵉ point2-iterate-ℕᵉ)))
        ( pr2ᵉ
          ( two-points-iterate-ordered-ℕᵉ
            ( linear-leq-ℕᵉ point1-iterate-ℕᵉ point2-iterate-ℕᵉ))))

  abstract
    not-not-eq-second-point-zero-min-reportingᵉ :
      ¬¬ᵉ (Idᵉ second-point-min-repeatingᵉ zero-ℕᵉ)
    not-not-eq-second-point-zero-min-reportingᵉ npᵉ =
      contradiction-le-ℕᵉ
        ( pred-firstᵉ)
        ( first-point-min-repeatingᵉ)
        ( trᵉ
          ( λ xᵉ → le-ℕᵉ pred-firstᵉ xᵉ)
          ( invᵉ equality-pred-firstᵉ)
          ( succ-le-ℕᵉ pred-firstᵉ))
        ( is-lower-bound-min-reportingᵉ
          ( pred-firstᵉ)
          ( pairᵉ
            ( pred-secondᵉ)
            ( pairᵉ
              ( trᵉ
                ( λ xᵉ → le-ℕᵉ (succ-ℕᵉ pred-secondᵉ) xᵉ)
                ( equality-pred-firstᵉ)
                ( trᵉ
                  ( λ xᵉ → le-ℕᵉ xᵉ first-point-min-repeatingᵉ)
                  ( equality-pred-secondᵉ)
                  ( le-min-reportingᵉ)))
              ( is-injective-equivᵉ
                ( fᵉ)
                ( trᵉ
                  ( λ xᵉ →
                    Idᵉ
                      ( iterateᵉ xᵉ (map-equivᵉ fᵉ) aᵉ)
                      ( iterateᵉ (succ-ℕᵉ pred-secondᵉ) (map-equivᵉ fᵉ) aᵉ))
                  ( equality-pred-firstᵉ)
                  ( trᵉ
                    ( λ xᵉ →
                      Idᵉ
                        ( iterateᵉ first-point-min-repeatingᵉ (map-equivᵉ fᵉ) aᵉ)
                        ( iterateᵉ xᵉ (map-equivᵉ fᵉ) aᵉ))
                    ( equality-pred-secondᵉ)
                    ( same-image-iterate-min-reportingᵉ)))))))
      where
      is-successor-first-point-min-repeatingᵉ :
        is-successor-ℕᵉ first-point-min-repeatingᵉ
      is-successor-first-point-min-repeatingᵉ =
        is-successor-is-nonzero-ℕᵉ
          ( is-nonzero-le-ℕᵉ
              second-point-min-repeatingᵉ
              first-point-min-repeatingᵉ
              le-min-reportingᵉ)
      pred-firstᵉ : ℕᵉ
      pred-firstᵉ = pr1ᵉ is-successor-first-point-min-repeatingᵉ
      equality-pred-firstᵉ : Idᵉ first-point-min-repeatingᵉ (succ-ℕᵉ pred-firstᵉ)
      equality-pred-firstᵉ = pr2ᵉ is-successor-first-point-min-repeatingᵉ
      is-successor-second-point-min-repeatingᵉ :
        is-successor-ℕᵉ second-point-min-repeatingᵉ
      is-successor-second-point-min-repeatingᵉ = is-successor-is-nonzero-ℕᵉ npᵉ
      pred-secondᵉ : ℕᵉ
      pred-secondᵉ = pr1ᵉ is-successor-second-point-min-repeatingᵉ
      equality-pred-secondᵉ : Idᵉ second-point-min-repeatingᵉ (succ-ℕᵉ pred-secondᵉ)
      equality-pred-secondᵉ = pr2ᵉ is-successor-second-point-min-repeatingᵉ

  has-finite-orbits-permutation'ᵉ :
    is-decidableᵉ (Idᵉ second-point-min-repeatingᵉ zero-ℕᵉ) →
    Σᵉ ℕᵉ (λ kᵉ → (is-nonzero-ℕᵉ kᵉ) ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ fᵉ) aᵉ) aᵉ)
  pr1ᵉ (has-finite-orbits-permutation'ᵉ (inlᵉ pᵉ)) = first-point-min-repeatingᵉ
  pr1ᵉ (pr2ᵉ (has-finite-orbits-permutation'ᵉ (inlᵉ pᵉ))) =
    is-nonzero-le-ℕᵉ
      second-point-min-repeatingᵉ
      first-point-min-repeatingᵉ
      le-min-reportingᵉ
  pr2ᵉ (pr2ᵉ (has-finite-orbits-permutation'ᵉ (inlᵉ pᵉ))) =
    trᵉ
      ( λ xᵉ →
        Idᵉ
          ( iterateᵉ first-point-min-repeatingᵉ (map-equivᵉ fᵉ) aᵉ)
          ( iterateᵉ xᵉ (map-equivᵉ fᵉ) aᵉ))
      ( pᵉ)
      ( same-image-iterate-min-reportingᵉ)
  has-finite-orbits-permutation'ᵉ (inrᵉ npᵉ) =
    ex-falsoᵉ (not-not-eq-second-point-zero-min-reportingᵉ npᵉ)
    where
    is-successor-first-point-min-repeatingᵉ :
      is-successor-ℕᵉ first-point-min-repeatingᵉ
    is-successor-first-point-min-repeatingᵉ =
      is-successor-is-nonzero-ℕᵉ
        ( is-nonzero-le-ℕᵉ
            second-point-min-repeatingᵉ
            first-point-min-repeatingᵉ
            le-min-reportingᵉ)
    pred-firstᵉ : ℕᵉ
    pred-firstᵉ = pr1ᵉ is-successor-first-point-min-repeatingᵉ
    equality-pred-firstᵉ : Idᵉ first-point-min-repeatingᵉ (succ-ℕᵉ pred-firstᵉ)
    equality-pred-firstᵉ = pr2ᵉ is-successor-first-point-min-repeatingᵉ
    is-successor-second-point-min-repeatingᵉ :
      is-successor-ℕᵉ second-point-min-repeatingᵉ
    is-successor-second-point-min-repeatingᵉ = is-successor-is-nonzero-ℕᵉ npᵉ
    pred-secondᵉ : ℕᵉ
    pred-secondᵉ = pr1ᵉ is-successor-second-point-min-repeatingᵉ
    equality-pred-secondᵉ : Idᵉ second-point-min-repeatingᵉ (succ-ℕᵉ pred-secondᵉ)
    equality-pred-secondᵉ = pr2ᵉ is-successor-second-point-min-repeatingᵉ

  has-finite-orbits-permutationᵉ :
    Σᵉ ℕᵉ (λ kᵉ → (is-nonzero-ℕᵉ kᵉ) ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ fᵉ) aᵉ) aᵉ)
  has-finite-orbits-permutationᵉ =
    has-finite-orbits-permutation'ᵉ
      ( has-decidable-equality-ℕᵉ second-point-min-repeatingᵉ zero-ℕᵉ)

  leq-has-finite-orbits-permutation-number-elementsᵉ :
    ( pr1ᵉ has-finite-orbits-permutationᵉ) ≤-ℕᵉ (number-of-elements-countᵉ eXᵉ)
  leq-has-finite-orbits-permutation-number-elementsᵉ =
    cases-second-pointᵉ
      ( has-decidable-equality-ℕᵉ second-point-min-repeatingᵉ zero-ℕᵉ)
    where
    cases-second-pointᵉ :
      is-decidableᵉ (Idᵉ second-point-min-repeatingᵉ zero-ℕᵉ) →
      (pr1ᵉ has-finite-orbits-permutationᵉ) ≤-ℕᵉ (number-of-elements-countᵉ eXᵉ)
    cases-second-pointᵉ (inlᵉ pᵉ) =
      trᵉ
        ( λ xᵉ →
          ( pr1ᵉ (has-finite-orbits-permutation'ᵉ xᵉ)) ≤-ℕᵉ
          ( number-of-elements-countᵉ eXᵉ))
        { xᵉ = inlᵉ pᵉ}
        { yᵉ = has-decidable-equality-ℕᵉ second-point-min-repeatingᵉ zero-ℕᵉ}
        ( eq-is-propᵉ
          ( is-prop-type-Propᵉ
            ( is-decidable-Propᵉ
              ( Id-Propᵉ ℕ-Setᵉ second-point-min-repeatingᵉ zero-ℕᵉ))))
        ( leq-first-point-min-reporting-succ-number-elementsᵉ)
    cases-second-pointᵉ (inrᵉ npᵉ) =
      ex-falsoᵉ (not-not-eq-second-point-zero-min-reportingᵉ npᵉ)

  mult-has-finite-orbits-permutationᵉ :
    (kᵉ : ℕᵉ) →
    Idᵉ (iterateᵉ (kᵉ *ℕᵉ (pr1ᵉ has-finite-orbits-permutationᵉ)) (map-equivᵉ fᵉ) aᵉ) aᵉ
  mult-has-finite-orbits-permutationᵉ zero-ℕᵉ = reflᵉ
  mult-has-finite-orbits-permutationᵉ (succ-ℕᵉ kᵉ) =
    ( iterate-add-ℕᵉ
      ( kᵉ *ℕᵉ (pr1ᵉ has-finite-orbits-permutationᵉ))
      ( pr1ᵉ has-finite-orbits-permutationᵉ)
      ( map-equivᵉ fᵉ)
      ( aᵉ)) ∙ᵉ
    ( ( apᵉ
        ( iterateᵉ (kᵉ *ℕᵉ (pr1ᵉ has-finite-orbits-permutationᵉ)) (map-equivᵉ fᵉ))
        ( pr2ᵉ (pr2ᵉ has-finite-orbits-permutationᵉ))) ∙ᵉ
      ( mult-has-finite-orbits-permutationᵉ kᵉ))
```

### For finite types, the number of orbits-permutation of a permutation is finite

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ) (fᵉ : Autᵉ (type-UU-Finᵉ nᵉ Xᵉ))
  where

  same-orbits-permutationᵉ : equivalence-relationᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)
  (pr1ᵉ same-orbits-permutationᵉ) aᵉ bᵉ =
    trunc-Propᵉ (Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ fᵉ) aᵉ) bᵉ))
  pr1ᵉ (pr2ᵉ same-orbits-permutationᵉ) _ = unit-trunc-Propᵉ (0ᵉ ,ᵉ reflᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ same-orbits-permutationᵉ)) aᵉ bᵉ Pᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Pᵉ)
      ( pr1ᵉ same-orbits-permutationᵉ bᵉ aᵉ)
      ( λ (kᵉ ,ᵉ pᵉ) →
        apply-universal-property-trunc-Propᵉ
          ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)
          ( pr1ᵉ same-orbits-permutationᵉ bᵉ aᵉ)
          ( λ hᵉ →
            unit-trunc-Propᵉ
              (pairᵉ
                ( pr1ᵉ (lemmaᵉ hᵉ kᵉ))
                ( ( apᵉ (iterateᵉ (pr1ᵉ (lemmaᵉ hᵉ kᵉ)) (map-equivᵉ fᵉ)) (invᵉ pᵉ)) ∙ᵉ
                  ( ( invᵉ (iterate-add-ℕᵉ (pr1ᵉ (lemmaᵉ hᵉ kᵉ)) kᵉ (map-equivᵉ fᵉ) aᵉ)) ∙ᵉ
                    ( ( apᵉ
                        ( λ xᵉ → iterateᵉ xᵉ (map-equivᵉ fᵉ) aᵉ)
                        ( pr2ᵉ (lemmaᵉ hᵉ kᵉ))) ∙ᵉ
                      ( mult-has-finite-orbits-permutationᵉ
                        ( type-UU-Finᵉ nᵉ Xᵉ)
                        ( pairᵉ nᵉ hᵉ)
                        ( fᵉ)
                        ( aᵉ)
                        ( kᵉ))))))))
    where
    has-finite-orbits-permutation-aᵉ :
      (hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      Σᵉ ℕᵉ (λ lᵉ → (is-nonzero-ℕᵉ lᵉ) ×ᵉ Idᵉ (iterateᵉ lᵉ (map-equivᵉ fᵉ) aᵉ) aᵉ)
    has-finite-orbits-permutation-aᵉ hᵉ =
      has-finite-orbits-permutationᵉ (type-UU-Finᵉ nᵉ Xᵉ) (pairᵉ nᵉ hᵉ) fᵉ aᵉ
    lemmaᵉ :
      (hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) (kᵉ : ℕᵉ) →
      Σᵉ ( ℕᵉ)
        ( λ jᵉ →
          Idᵉ (jᵉ +ℕᵉ kᵉ) (kᵉ *ℕᵉ (pr1ᵉ (has-finite-orbits-permutation-aᵉ hᵉ))))
    lemmaᵉ hᵉ kᵉ =
      subtraction-leq-ℕᵉ
        ( kᵉ)
        ( kᵉ *ℕᵉ (pr1ᵉ (has-finite-orbits-permutation-aᵉ hᵉ)))
        ( leq-mul-is-nonzero-ℕᵉ
          ( pr1ᵉ (has-finite-orbits-permutation-aᵉ hᵉ))
          ( kᵉ)
          ( pr1ᵉ (pr2ᵉ (has-finite-orbits-permutation-aᵉ hᵉ))))
  pr2ᵉ (pr2ᵉ (pr2ᵉ same-orbits-permutationᵉ)) aᵉ bᵉ cᵉ Qᵉ Pᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Pᵉ)
      ( pr1ᵉ same-orbits-permutationᵉ aᵉ cᵉ)
      ( λ (k1ᵉ ,ᵉ pᵉ) →
        apply-universal-property-trunc-Propᵉ
          ( Qᵉ)
          ( pr1ᵉ same-orbits-permutationᵉ aᵉ cᵉ)
          ( λ (k2ᵉ ,ᵉ qᵉ) →
            unit-trunc-Propᵉ
              ( ( k2ᵉ +ℕᵉ k1ᵉ) ,ᵉ
                ( ( iterate-add-ℕᵉ k2ᵉ k1ᵉ (map-equivᵉ fᵉ) aᵉ) ∙ᵉ
                  ( apᵉ (iterateᵉ k2ᵉ (map-equivᵉ fᵉ)) pᵉ ∙ᵉ qᵉ)))))

  abstract
    is-decidable-same-orbits-permutationᵉ :
      ( aᵉ bᵉ : type-UU-Finᵉ nᵉ Xᵉ) →
      is-decidableᵉ (sim-equivalence-relationᵉ same-orbits-permutationᵉ aᵉ bᵉ)
    is-decidable-same-orbits-permutationᵉ aᵉ bᵉ =
      apply-universal-property-trunc-Propᵉ
        ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)
        ( is-decidable-Propᵉ
          ( prop-equivalence-relationᵉ same-orbits-permutationᵉ aᵉ bᵉ))
        ( λ hᵉ →
          is-decidable-trunc-Prop-is-merely-decidableᵉ
            ( Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ fᵉ) aᵉ) bᵉ))
            ( unit-trunc-Propᵉ
              ( is-decidable-iterate-is-decidable-boundedᵉ hᵉ aᵉ bᵉ
                ( is-decidable-bounded-Σ-ℕᵉ nᵉ
                  ( λ zᵉ → zᵉ ≤-ℕᵉ nᵉ)
                  ( λ zᵉ → Idᵉ (iterateᵉ zᵉ (map-equivᵉ fᵉ) aᵉ) bᵉ)
                  ( λ zᵉ → is-decidable-leq-ℕᵉ zᵉ nᵉ)
                  ( λ zᵉ →
                    has-decidable-equality-equivᵉ
                      ( inv-equivᵉ hᵉ)
                      ( has-decidable-equality-Finᵉ nᵉ)
                      ( iterateᵉ zᵉ (map-equivᵉ fᵉ) aᵉ)
                      ( bᵉ))
                  ( λ mᵉ pᵉ → pᵉ)))))
      where
      is-decidable-iterate-is-decidable-boundedᵉ :
        ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) (aᵉ bᵉ : type-UU-Finᵉ nᵉ Xᵉ) →
        is-decidableᵉ
          ( Σᵉ ℕᵉ (λ mᵉ → (mᵉ ≤-ℕᵉ nᵉ) ×ᵉ (Idᵉ (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ) bᵉ))) →
        is-decidableᵉ (Σᵉ ℕᵉ (λ mᵉ → Idᵉ (iterateᵉ mᵉ (map-equivᵉ fᵉ) aᵉ) bᵉ))
      is-decidable-iterate-is-decidable-boundedᵉ hᵉ aᵉ bᵉ (inlᵉ pᵉ) =
        inlᵉ (pairᵉ (pr1ᵉ pᵉ) (pr2ᵉ (pr2ᵉ pᵉ)))
      is-decidable-iterate-is-decidable-boundedᵉ hᵉ aᵉ bᵉ (inrᵉ npᵉ) =
        inrᵉ
          ( λ pᵉ →
            npᵉ
              ( pairᵉ
                ( remainder-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))
                ( pairᵉ
                  ( leq-le-ℕᵉ
                    ( remainder-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))
                    ( nᵉ)
                    ( concatenate-le-leq-ℕᵉ
                      { yᵉ = mᵉ}
                      ( strict-upper-bound-remainder-euclidean-division-ℕᵉ
                        ( mᵉ)
                        ( pr1ᵉ pᵉ)
                        ( pr1ᵉ
                          ( pr2ᵉ
                            ( has-finite-orbits-permutationᵉ
                              ( type-UU-Finᵉ nᵉ Xᵉ)
                              ( pairᵉ nᵉ hᵉ)
                              ( fᵉ)
                              ( aᵉ)))))
                      ( leq-has-finite-orbits-permutation-number-elementsᵉ
                        ( type-UU-Finᵉ nᵉ Xᵉ)
                        ( pairᵉ nᵉ hᵉ)
                        ( fᵉ)
                        ( aᵉ))))
                  ( ( apᵉ
                      ( iterateᵉ
                        ( remainder-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))
                        ( map-equivᵉ fᵉ))
                      ( invᵉ
                        ( mult-has-finite-orbits-permutationᵉ
                          ( type-UU-Finᵉ nᵉ Xᵉ)
                          ( pairᵉ nᵉ hᵉ)
                          ( fᵉ)
                          ( aᵉ)
                          ( quotient-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))))) ∙ᵉ
                    ( ( invᵉ
                        ( iterate-add-ℕᵉ
                          ( remainder-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))
                          ( (quotient-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ)) *ℕᵉ mᵉ)
                          ( map-equivᵉ fᵉ)
                          ( aᵉ))) ∙ᵉ
                      ( ( apᵉ
                          ( λ xᵉ → iterateᵉ xᵉ (map-equivᵉ fᵉ) aᵉ)
                          ( ( commutative-add-ℕᵉ
                              ( remainder-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ))
                              ( quotient-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ) *ℕᵉ mᵉ)) ∙ᵉ
                            ( eq-euclidean-division-ℕᵉ mᵉ (pr1ᵉ pᵉ)))) ∙ᵉ
                        ( pr2ᵉ pᵉ)))))))
        where
        mᵉ : ℕᵉ
        mᵉ = pr1ᵉ
            ( has-finite-orbits-permutationᵉ
              ( type-UU-Finᵉ nᵉ Xᵉ)
              ( pairᵉ nᵉ hᵉ)
              ( fᵉ)
              ( aᵉ))

  abstract
    is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ :
      (Tᵉ : equivalence-classᵉ same-orbits-permutationᵉ) →
      (aᵉ : type-UU-Finᵉ nᵉ Xᵉ) →
      is-decidableᵉ (is-in-equivalence-classᵉ same-orbits-permutationᵉ Tᵉ aᵉ)
    is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ Tᵉ aᵉ =
      is-decidable-is-in-equivalence-class-is-decidableᵉ
        ( same-orbits-permutationᵉ)
        ( is-decidable-same-orbits-permutationᵉ)
        ( Tᵉ)
        ( aᵉ)

  abstract
    has-finite-number-orbits-permutationᵉ :
      is-finiteᵉ (equivalence-classᵉ same-orbits-permutationᵉ)
    has-finite-number-orbits-permutationᵉ =
      is-finite-codomainᵉ
        ( is-finite-type-UU-Finᵉ nᵉ Xᵉ)
        ( is-surjective-classᵉ same-orbits-permutationᵉ)
        ( apply-universal-property-trunc-Propᵉ
          ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)
          ( pairᵉ
            ( has-decidable-equalityᵉ
              ( equivalence-classᵉ same-orbits-permutationᵉ))
            ( is-prop-has-decidable-equalityᵉ))
        ( λ hᵉ T1ᵉ T2ᵉ →
          apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ T1ᵉ)
          ( is-decidable-Propᵉ
            ( Id-Propᵉ (equivalence-class-Setᵉ same-orbits-permutationᵉ) T1ᵉ T2ᵉ))
          ( λ (pairᵉ t1ᵉ p1ᵉ) →
            cases-decidable-equalityᵉ T1ᵉ T2ᵉ t1ᵉ
              ( eq-pair-Σᵉ
                ( apᵉ
                  ( subtype-equivalence-classᵉ
                    same-orbits-permutationᵉ)
                  ( eq-has-same-elements-equivalence-classᵉ
                    same-orbits-permutationᵉ T1ᵉ
                      ( classᵉ same-orbits-permutationᵉ t1ᵉ) p1ᵉ))
                ( all-elements-equal-type-trunc-Propᵉ _ _))
              ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                T2ᵉ t1ᵉ))))
      where
      cases-decidable-equalityᵉ :
        (T1ᵉ T2ᵉ : equivalence-classᵉ same-orbits-permutationᵉ)
        (t1ᵉ : type-UU-Finᵉ nᵉ Xᵉ) →
        Idᵉ T1ᵉ (classᵉ same-orbits-permutationᵉ t1ᵉ) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ same-orbits-permutationᵉ T2ᵉ t1ᵉ) →
        is-decidableᵉ (Idᵉ T1ᵉ T2ᵉ)
      cases-decidable-equalityᵉ T1ᵉ T2ᵉ t1ᵉ p1ᵉ (inlᵉ pᵉ) =
        inlᵉ
          ( ( p1ᵉ) ∙ᵉ
            ( map-inv-is-equivᵉ
              ( is-equiv-is-in-equivalence-class-eq-equivalence-classᵉ
                  same-orbits-permutationᵉ t1ᵉ T2ᵉ)
              ( pᵉ)))
      cases-decidable-equalityᵉ T1ᵉ T2ᵉ t1ᵉ p1ᵉ (inrᵉ npᵉ) =
        inrᵉ
          ( λ pᵉ →
            npᵉ
              ( is-in-equivalence-class-eq-equivalence-classᵉ
                same-orbits-permutationᵉ t1ᵉ T2ᵉ (invᵉ p1ᵉ ∙ᵉ pᵉ)))

  number-of-orbits-permutationᵉ : ℕᵉ
  number-of-orbits-permutationᵉ =
    number-of-elements-is-finiteᵉ has-finite-number-orbits-permutationᵉ

  sign-permutation-orbitᵉ : Finᵉ 2
  sign-permutation-orbitᵉ =
    iterateᵉ (nᵉ +ℕᵉ number-of-orbits-permutationᵉ) (succ-Finᵉ 2ᵉ) (zero-Finᵉ 1ᵉ)
```

```agda
module _
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (eXᵉ : countᵉ Xᵉ) (aᵉ bᵉ : Xᵉ) (npᵉ : aᵉ ≠ᵉ bᵉ)
  where

  composition-transposition-a-bᵉ : (Xᵉ ≃ᵉ Xᵉ) → (Xᵉ ≃ᵉ Xᵉ)
  composition-transposition-a-bᵉ gᵉ =
    ( standard-transpositionᵉ (has-decidable-equality-countᵉ eXᵉ) npᵉ) ∘eᵉ gᵉ

  composition-transposition-a-b-involutionᵉ :
    ( gᵉ : Xᵉ ≃ᵉ Xᵉ) →
    htpy-equivᵉ
      ( composition-transposition-a-bᵉ (composition-transposition-a-bᵉ gᵉ))
      ( gᵉ)
  composition-transposition-a-b-involutionᵉ gᵉ xᵉ =
    is-involution-map-transpositionᵉ
      ( standard-2-Element-Decidable-Subtypeᵉ
        ( has-decidable-equality-countᵉ eXᵉ)
        ( npᵉ))
      ( map-equivᵉ gᵉ xᵉ)

  same-orbits-permutation-countᵉ : (Xᵉ ≃ᵉ Xᵉ) → equivalence-relationᵉ l1ᵉ Xᵉ
  same-orbits-permutation-countᵉ =
    same-orbits-permutationᵉ
      ( number-of-elements-countᵉ eXᵉ)
      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))

  abstract
    minimal-element-iterateᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) (xᵉ yᵉ : Xᵉ) → Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ) →
      minimal-element-ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)
    minimal-element-iterateᵉ gᵉ xᵉ yᵉ =
      well-ordering-principle-ℕᵉ
        ( λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)
        ( λ kᵉ → has-decidable-equality-countᵉ eXᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)

  abstract
    minimal-element-iterate-nonzeroᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) (xᵉ yᵉ : Xᵉ) →
      Σᵉ ℕᵉ (λ kᵉ → is-nonzero-ℕᵉ kᵉ ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ) →
      minimal-element-ℕᵉ
        ( λ kᵉ → is-nonzero-ℕᵉ kᵉ ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)
    minimal-element-iterate-nonzeroᵉ gᵉ xᵉ yᵉ =
      well-ordering-principle-ℕᵉ
        ( λ kᵉ → is-nonzero-ℕᵉ kᵉ ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)
        ( λ kᵉ →
          is-decidable-productᵉ
            ( is-decidable-negᵉ (has-decidable-equality-ℕᵉ kᵉ zero-ℕᵉ))
            ( has-decidable-equality-countᵉ eXᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ))

  abstract
    minimal-element-iterate-2ᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) (xᵉ yᵉ zᵉ : Xᵉ) →
      Σᵉ ( ℕᵉ)
        ( λ kᵉ →
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ) +ᵉ
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) zᵉ)) →
      minimal-element-ℕᵉ
        ( λ kᵉ →
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ) +ᵉ
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) zᵉ))
    minimal-element-iterate-2ᵉ gᵉ xᵉ yᵉ zᵉ pᵉ =
      well-ordering-principle-ℕᵉ
        ( λ kᵉ →
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ) +ᵉ
          ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) zᵉ))
        ( λ kᵉ →
          is-decidable-coproductᵉ
          ( has-decidable-equality-countᵉ eXᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) yᵉ)
          ( has-decidable-equality-countᵉ eXᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) zᵉ))
        ( pᵉ)

  abstract
    equal-iterate-transpositionᵉ :
      {l2ᵉ : Level} (xᵉ : Xᵉ) (gᵉ : Xᵉ ≃ᵉ Xᵉ) (Cᵉ : ℕᵉ → UUᵉ l2ᵉ)
      ( Fᵉ :
        (kᵉ : ℕᵉ) → Cᵉ kᵉ →
        ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ ≠ᵉ aᵉ) ×ᵉ
        ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ ≠ᵉ bᵉ))
      ( Indᵉ :
        (nᵉ : ℕᵉ) → Cᵉ (succ-ℕᵉ nᵉ) → is-nonzero-ℕᵉ nᵉ → Cᵉ nᵉ) →
      (kᵉ : ℕᵉ) → (is-zero-ℕᵉ kᵉ +ᵉ Cᵉ kᵉ) →
      Idᵉ
        ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
        ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ)
    equal-iterate-transpositionᵉ xᵉ gᵉ Cᵉ Fᵉ Indᵉ zero-ℕᵉ pᵉ = reflᵉ
    equal-iterate-transpositionᵉ xᵉ gᵉ Cᵉ Fᵉ Indᵉ (succ-ℕᵉ kᵉ) (inlᵉ pᵉ) =
      ex-falsoᵉ (is-nonzero-succ-ℕᵉ kᵉ pᵉ)
    equal-iterate-transpositionᵉ xᵉ gᵉ Cᵉ Fᵉ Indᵉ (succ-ℕᵉ kᵉ) (inrᵉ pᵉ) =
      cases-equal-iterate-transpositionᵉ
        ( has-decidable-equality-countᵉ eXᵉ
          ( iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ)
          ( aᵉ))
        ( has-decidable-equality-countᵉ eXᵉ
          ( iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ)
          ( bᵉ))
      where
      induction-cases-equal-iterate-transpositionᵉ :
        is-decidableᵉ (Idᵉ kᵉ zero-ℕᵉ) →
        Idᵉ
          ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
          ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ)
      induction-cases-equal-iterate-transpositionᵉ (inlᵉ sᵉ) =
        trᵉ
          ( λ kᵉ →
            Idᵉ (iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
            (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ))
          ( invᵉ sᵉ)
          ( reflᵉ)
      induction-cases-equal-iterate-transpositionᵉ (inrᵉ sᵉ) =
        equal-iterate-transpositionᵉ xᵉ gᵉ Cᵉ Fᵉ Indᵉ kᵉ (inrᵉ (Indᵉ kᵉ pᵉ sᵉ))
      cases-equal-iterate-transpositionᵉ :
        is-decidableᵉ (Idᵉ (iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ) aᵉ) →
        is-decidableᵉ (Idᵉ (iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ) bᵉ) →
        Idᵉ
          ( iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
          ( iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ)
      cases-equal-iterate-transpositionᵉ (inlᵉ qᵉ) rᵉ =
        ex-falsoᵉ (pr1ᵉ (Fᵉ (succ-ℕᵉ kᵉ) pᵉ) qᵉ)
      cases-equal-iterate-transpositionᵉ (inrᵉ qᵉ) (inlᵉ rᵉ) =
        ex-falsoᵉ (pr2ᵉ (Fᵉ (succ-ℕᵉ kᵉ) pᵉ) rᵉ)
      cases-equal-iterate-transpositionᵉ (inrᵉ qᵉ) (inrᵉ rᵉ) =
        ( apᵉ
          ( λ nᵉ →
            iterateᵉ nᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
          ( commutative-add-ℕᵉ kᵉ (succ-ℕᵉ zero-ℕᵉ))) ∙ᵉ
        ( ( iterate-add-ℕᵉ
            ( succ-ℕᵉ zero-ℕᵉ)
            ( kᵉ)
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)) ∙ᵉ
          ( ( apᵉ
              ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
              ( induction-cases-equal-iterate-transpositionᵉ
                ( has-decidable-equality-ℕᵉ kᵉ zero-ℕᵉ))) ∙ᵉ
            ( is-fixed-point-standard-transpositionᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( npᵉ)
              ( iterateᵉ (succ-ℕᵉ kᵉ) (map-equivᵉ gᵉ) xᵉ)
              ( λ q'ᵉ → qᵉ (invᵉ q'ᵉ))
              ( λ r'ᵉ → rᵉ (invᵉ r'ᵉ)))))

  abstract
    conserves-other-orbits-transpositionᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) (xᵉ yᵉ : Xᵉ) →
      ¬ᵉ (sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ aᵉ) →
      ¬ᵉ (sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ bᵉ) →
      ( ( sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ yᵉ) ≃ᵉ
        ( sim-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( xᵉ)
          ( yᵉ)))
    conserves-other-orbits-transpositionᵉ gᵉ xᵉ yᵉ NAᵉ NBᵉ =
      pairᵉ
        ( λ P'ᵉ → apply-universal-property-trunc-Propᵉ P'ᵉ
          ( prop-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)
            ( yᵉ))
          ( λ (pairᵉ kᵉ pᵉ) → unit-trunc-Propᵉ
            (pairᵉ kᵉ
              ( (equal-iterate-transposition-other-orbitsᵉ kᵉ) ∙ᵉ
                ( pᵉ)))))
        ( is-equiv-has-converse-is-propᵉ
          ( is-prop-type-trunc-Propᵉ)
          ( is-prop-type-trunc-Propᵉ)
          ( λ P'ᵉ →
            apply-universal-property-trunc-Propᵉ P'ᵉ
              ( prop-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ yᵉ)
              ( λ (pairᵉ kᵉ pᵉ) →
                unit-trunc-Propᵉ
                  ( ( kᵉ) ,ᵉ
                    ( (invᵉ (equal-iterate-transposition-other-orbitsᵉ kᵉ)) ∙ᵉ
                      ( pᵉ))))))
      where
      equal-iterate-transposition-other-orbitsᵉ :
        (kᵉ : ℕᵉ) →
        Idᵉ
          ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
          ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ)
      equal-iterate-transposition-other-orbitsᵉ kᵉ =
        equal-iterate-transpositionᵉ xᵉ gᵉ (λ k'ᵉ → unitᵉ)
          (λ k'ᵉ _ →
            pairᵉ
              ( λ qᵉ → NAᵉ (unit-trunc-Propᵉ (pairᵉ k'ᵉ qᵉ)))
              ( λ rᵉ → NBᵉ (unit-trunc-Propᵉ (pairᵉ k'ᵉ rᵉ))))
          (λ _ _ _ → starᵉ) kᵉ (inrᵉ starᵉ)

  conserves-other-orbits-transposition-quotientᵉ :
    (gᵉ : Xᵉ ≃ᵉ Xᵉ)
    (Tᵉ : equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ)) →
    ¬ᵉ (is-in-equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ) Tᵉ aᵉ) →
    ¬ᵉ (is-in-equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ) Tᵉ bᵉ) →
    equivalence-classᵉ
      ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
  pr1ᵉ (conserves-other-orbits-transposition-quotientᵉ gᵉ Tᵉ nqᵉ nrᵉ) = pr1ᵉ Tᵉ
  pr2ᵉ (conserves-other-orbits-transposition-quotientᵉ gᵉ (pairᵉ T1ᵉ T2ᵉ) nqᵉ nrᵉ) =
    apply-universal-property-trunc-Propᵉ
      ( T2ᵉ)
      ( is-equivalence-class-Propᵉ
        ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
        ( T1ᵉ))
      ( λ (pairᵉ xᵉ Qᵉ) →
        unit-trunc-Propᵉ
          ( pairᵉ xᵉ
            ( λ yᵉ →
              iff-equivᵉ
                ( ( conserves-other-orbits-transpositionᵉ gᵉ xᵉ yᵉ
                    ( nqᵉ ∘ᵉ backward-implicationᵉ (Qᵉ aᵉ))
                    ( nrᵉ ∘ᵉ backward-implicationᵉ (Qᵉ bᵉ))) ∘eᵉ
                  ( equiv-iff'ᵉ
                    ( T1ᵉ yᵉ)
                    ( prop-equivalence-relationᵉ
                      ( same-orbits-permutation-countᵉ gᵉ)
                      ( xᵉ)
                      ( yᵉ))
                    ( Qᵉ yᵉ))))))

  abstract
    not-same-orbits-transposition-same-orbitsᵉ :
      ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
      ( Pᵉ :
        ( sim-equivalence-relationᵉ
          ( same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ))
          ( aᵉ)
          ( bᵉ))) →
      ¬ᵉ ( sim-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( aᵉ)
          ( bᵉ))
    not-same-orbits-transposition-same-orbitsᵉ gᵉ Pᵉ Qᵉ =
      apply-universal-property-trunc-Propᵉ Qᵉ empty-Propᵉ
        ( λ (pairᵉ k2ᵉ qᵉ) →
          ( apply-universal-property-trunc-Propᵉ Pᵉ empty-Propᵉ
            ( λ pᵉ → lemma3ᵉ pᵉ k2ᵉ qᵉ)))
      where
      neq-iterate-nonzero-le-minimal-elementᵉ :
        ( paᵉ : Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ))
        ( kᵉ : ℕᵉ) →
        ( is-nonzero-ℕᵉ kᵉ ×ᵉ le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))) →
        ( iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ ≠ᵉ aᵉ) ×ᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ ≠ᵉ bᵉ)
      pr1ᵉ (neq-iterate-nonzero-le-minimal-elementᵉ paᵉ kᵉ (pairᵉ nzᵉ ineqᵉ)) qᵉ =
        contradiction-le-ℕᵉ
          ( pr1ᵉ pair-k2ᵉ)
          ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
          ( le-subtraction-ℕᵉ
            ( pr1ᵉ (pair-k2ᵉ))
            ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( kᵉ)
            ( nzᵉ)
            ( commutative-add-ℕᵉ kᵉ (pr1ᵉ (pair-k2ᵉ)) ∙ᵉ pr2ᵉ (pr2ᵉ pair-k2ᵉ)))
          ( pr2ᵉ
            ( pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( pr1ᵉ pair-k2ᵉ)
            ( ( apᵉ (iterateᵉ (pr1ᵉ pair-k2ᵉ) (map-equivᵉ gᵉ)) (invᵉ qᵉ)) ∙ᵉ
              ( (invᵉ (iterate-add-ℕᵉ (pr1ᵉ pair-k2ᵉ) kᵉ (map-equivᵉ gᵉ) aᵉ)) ∙ᵉ
                ( apᵉ
                  ( λ nᵉ → iterateᵉ nᵉ (map-equivᵉ gᵉ) aᵉ)
                  ( pr2ᵉ (pr2ᵉ pair-k2ᵉ)) ∙ᵉ
                  pr1ᵉ (pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))))))
        where
        pair-k2ᵉ :
          Σᵉ ( ℕᵉ)
            ( λ lᵉ →
              is-nonzero-ℕᵉ lᵉ ×ᵉ
              Idᵉ (lᵉ +ℕᵉ kᵉ) (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
        pair-k2ᵉ =
          (subtraction-le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)) ineqᵉ)
      pr2ᵉ (neq-iterate-nonzero-le-minimal-elementᵉ paᵉ kᵉ (pairᵉ nzᵉ ineqᵉ)) rᵉ =
        ex-falsoᵉ
          ( contradiction-le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ineqᵉ (pr2ᵉ (pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)) kᵉ rᵉ))
      equal-iterate-transposition-aᵉ :
        (paᵉ : Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)) (kᵉ : ℕᵉ) →
        le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)) →
        ( Idᵉ
          ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ)
          ( iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ))
      equal-iterate-transposition-aᵉ paᵉ kᵉ ineqᵉ =
        equal-iterate-transpositionᵉ aᵉ gᵉ
          ( λ k'ᵉ →
            ( is-nonzero-ℕᵉ k'ᵉ) ×ᵉ
            ( le-ℕᵉ k'ᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))))
          ( neq-iterate-nonzero-le-minimal-elementᵉ paᵉ)
          ( λ nᵉ (pairᵉ _ sᵉ) nzᵉ →
            pairᵉ
              ( nzᵉ)
              ( transitive-le-ℕᵉ nᵉ
                ( succ-ℕᵉ nᵉ)
                ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
                ( succ-le-ℕᵉ nᵉ) sᵉ))
          ( kᵉ)
          ( cases-equal-iterate-transposition-aᵉ
            ( has-decidable-equality-ℕᵉ kᵉ zero-ℕᵉ))
        where
        cases-equal-iterate-transposition-aᵉ :
          is-decidableᵉ (is-zero-ℕᵉ kᵉ) →
          ( is-zero-ℕᵉ kᵉ) +ᵉ
          ( is-nonzero-ℕᵉ kᵉ ×ᵉ le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
        cases-equal-iterate-transposition-aᵉ (inlᵉ sᵉ) = inlᵉ sᵉ
        cases-equal-iterate-transposition-aᵉ (inrᵉ sᵉ) = inrᵉ (pairᵉ sᵉ ineqᵉ)
      lemma2ᵉ :
        ( paᵉ : Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)) →
        is-decidableᵉ (Idᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)) zero-ℕᵉ) →
        Idᵉ
          ( iterateᵉ
            ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
            ( aᵉ))
          ( aᵉ)
      lemma2ᵉ paᵉ (inlᵉ pᵉ) =
        ex-falsoᵉ
          ( npᵉ
            ( trᵉ
              ( λ vᵉ → Idᵉ (iterateᵉ vᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)
              ( pᵉ)
              ( pr1ᵉ (pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))))
      lemma2ᵉ paᵉ (inrᵉ pᵉ) =
        ( apᵉ
          ( λ nᵉ → iterateᵉ nᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ)
          ( pr2ᵉ (is-successor-k1ᵉ) ∙ᵉ
            commutative-add-ℕᵉ (pr1ᵉ is-successor-k1ᵉ) (succ-ℕᵉ zero-ℕᵉ))) ∙ᵉ
          ( ( iterate-add-ℕᵉ
              ( succ-ℕᵉ zero-ℕᵉ)
              ( pr1ᵉ is-successor-k1ᵉ)
              ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ) ∙ᵉ
            ( ( apᵉ
                ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                ( equal-iterate-transposition-aᵉ paᵉ (pr1ᵉ is-successor-k1ᵉ)
                  ( trᵉ
                    ( le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ))
                    ( invᵉ (pr2ᵉ is-successor-k1ᵉ))
                    ( succ-le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ))))) ∙ᵉ
              ( ( apᵉ
                  ( λ nᵉ →
                    map-standard-transpositionᵉ
                      ( has-decidable-equality-countᵉ eXᵉ)
                      ( npᵉ)
                      ( iterateᵉ nᵉ (map-equivᵉ gᵉ) aᵉ))
                  ( invᵉ (pr2ᵉ is-successor-k1ᵉ))) ∙ᵉ
                ( ( apᵉ
                    ( map-standard-transpositionᵉ
                      ( has-decidable-equality-countᵉ eXᵉ) npᵉ)
                    ( pr1ᵉ (pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))) ∙ᵉ
                  ( right-computation-standard-transpositionᵉ
                    ( has-decidable-equality-countᵉ eXᵉ)
                    ( npᵉ))))))
        where
        is-successor-k1ᵉ :
          is-successor-ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
        is-successor-k1ᵉ = is-successor-is-nonzero-ℕᵉ pᵉ
      mult-lemma2ᵉ :
        ( paᵉ : Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)) (kᵉ : ℕᵉ) →
        Idᵉ
          ( iterateᵉ
            ( kᵉ *ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
            ( aᵉ))
          ( aᵉ)
      mult-lemma2ᵉ paᵉ zero-ℕᵉ = reflᵉ
      mult-lemma2ᵉ paᵉ (succ-ℕᵉ kᵉ) =
        ( iterate-add-ℕᵉ
          ( kᵉ *ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
          ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
          ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ) ∙ᵉ
        ( apᵉ
          ( iterateᵉ
            ( kᵉ *ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ)))
          ( lemma2ᵉ
            ( paᵉ)
            ( has-decidable-equality-ℕᵉ
              ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
              ( zero-ℕᵉ))) ∙ᵉ
          ( mult-lemma2ᵉ paᵉ kᵉ))
      lemma3ᵉ :
        ( paᵉ : Σᵉ ℕᵉ (λ kᵉ → Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)) (kᵉ : ℕᵉ) →
        iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ ≠ᵉ bᵉ
      lemma3ᵉ paᵉ kᵉ qᵉ =
        contradiction-le-ℕᵉ
          ( rᵉ)
          ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
          ( ineqᵉ)
          ( pr2ᵉ
            ( pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( rᵉ)
            ( invᵉ (equal-iterate-transposition-aᵉ paᵉ rᵉ ineqᵉ) ∙ᵉ
              ( ( apᵉ
                  ( iterateᵉ rᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)))
                  ( invᵉ (mult-lemma2ᵉ paᵉ quoᵉ))) ∙ᵉ
                ( (invᵉ
                    ( iterate-add-ℕᵉ
                      ( rᵉ)
                      ( quoᵉ *ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))
                      ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ)) ∙ᵉ
                  ( ( apᵉ
                      ( λ nᵉ →
                        iterateᵉ
                          ( nᵉ)
                          ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                          ( aᵉ))
                      ( commutative-add-ℕᵉ
                        ( rᵉ)
                        ( quoᵉ *ℕᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))) ∙ᵉ
                        ( eq-euclidean-division-ℕᵉ
                          ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
                          ( kᵉ)))) ∙ᵉ
                    ( qᵉ))))))
        where
        rᵉ : ℕᵉ
        rᵉ =
          remainder-euclidean-division-ℕᵉ
            ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( kᵉ)
        quoᵉ : ℕᵉ
        quoᵉ =
          quotient-euclidean-division-ℕᵉ
            ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( kᵉ)
        ineqᵉ : le-ℕᵉ rᵉ (pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
        ineqᵉ =
          strict-upper-bound-remainder-euclidean-division-ℕᵉ
            ( pr1ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ))
            ( kᵉ)
            ( λ pᵉ →
              npᵉ
              ( trᵉ
                ( λ vᵉ → Idᵉ (iterateᵉ vᵉ (map-equivᵉ gᵉ) aᵉ) bᵉ)
                ( pᵉ)
                ( pr1ᵉ (pr2ᵉ (minimal-element-iterateᵉ gᵉ aᵉ bᵉ paᵉ)))))

  coproduct-sim-equivalence-relation-a-b-Propᵉ :
    ( gᵉ : Xᵉ ≃ᵉ Xᵉ) →
    ( Pᵉ :
      sim-equivalence-relationᵉ
        ( same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))
        ( aᵉ)
        ( bᵉ))
    (xᵉ : Xᵉ) → Propᵉ l1ᵉ
  coproduct-sim-equivalence-relation-a-b-Propᵉ gᵉ Pᵉ xᵉ =
    coproduct-Propᵉ
      ( prop-equivalence-relationᵉ
        (same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ aᵉ)
      ( prop-equivalence-relationᵉ
        (same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ bᵉ)
      ( λ T1ᵉ T2ᵉ → not-same-orbits-transposition-same-orbitsᵉ gᵉ Pᵉ
        ( transitive-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( _)
          ( _)
          ( _)
          ( T2ᵉ)
          ( symmetric-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( _)
            ( _)
            ( T1ᵉ))))

  abstract
    split-orbits-a-b-transpositionᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) →
      (Pᵉ :
        sim-equivalence-relationᵉ
          ( same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ))
          ( aᵉ)
          ( bᵉ))
      (xᵉ : Xᵉ) →
      ( ( sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ aᵉ) ≃ᵉ
        ( ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)
            ( aᵉ)) +ᵉ
          ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)
            ( bᵉ))))
    split-orbits-a-b-transpositionᵉ gᵉ Pᵉ xᵉ =
      pairᵉ
        ( λ Tᵉ →
          apply-universal-property-trunc-Propᵉ Tᵉ
            ( coproduct-sim-equivalence-relation-a-b-Propᵉ gᵉ Pᵉ xᵉ)
            (λ paᵉ → lemma2ᵉ gᵉ (pairᵉ (pr1ᵉ paᵉ) (inlᵉ (pr2ᵉ paᵉ)))))
        ( is-equiv-has-converse-is-propᵉ is-prop-type-trunc-Propᵉ
          ( is-prop-type-Propᵉ
            ( coproduct-sim-equivalence-relation-a-b-Propᵉ gᵉ Pᵉ xᵉ))
          ( λ where
            ( inlᵉ Tᵉ) →
              apply-universal-property-trunc-Propᵉ Tᵉ
                ( prop-equivalence-relationᵉ
                  ( same-orbits-permutation-countᵉ gᵉ) xᵉ aᵉ)
                ( λ paᵉ →
                  lemma3ᵉ
                    ( lemma2ᵉ
                      ( composition-transposition-a-bᵉ gᵉ)
                      ( pairᵉ (pr1ᵉ paᵉ) (inlᵉ (pr2ᵉ paᵉ)))))
            ( inrᵉ Tᵉ) →
              apply-universal-property-trunc-Propᵉ Tᵉ
                ( prop-equivalence-relationᵉ
                  ( same-orbits-permutation-countᵉ gᵉ) xᵉ aᵉ)
                ( λ paᵉ →
                  lemma3ᵉ
                    ( lemma2ᵉ
                      ( composition-transposition-a-bᵉ gᵉ)
                      ( (pr1ᵉ paᵉ) ,ᵉ (inrᵉ (pr2ᵉ paᵉ)))))))
      where
      minimal-element-iterate-2-a-bᵉ :
        ( gᵉ : Xᵉ ≃ᵉ Xᵉ) →
        ( Σᵉ ( ℕᵉ)
            ( λ kᵉ →
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) aᵉ) +ᵉ
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) bᵉ))) →
        minimal-element-ℕᵉ
          ( λ kᵉ →
            ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) aᵉ) +ᵉ
            ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) bᵉ))
      minimal-element-iterate-2-a-bᵉ gᵉ = minimal-element-iterate-2ᵉ gᵉ xᵉ aᵉ bᵉ
      equal-iterate-transposition-same-orbitsᵉ :
        ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
        ( paᵉ :
          Σᵉ ( ℕᵉ)
            ( λ kᵉ →
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) aᵉ) +ᵉ
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) bᵉ)))
        ( kᵉ : ℕᵉ) →
        ( le-ℕᵉ kᵉ (pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))) →
        Idᵉ
          ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
          ( iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ)
      equal-iterate-transposition-same-orbitsᵉ gᵉ paᵉ kᵉ ineqᵉ =
        equal-iterate-transpositionᵉ xᵉ gᵉ
          ( λ k'ᵉ → le-ℕᵉ k'ᵉ (pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ)))
          ( λ k'ᵉ pᵉ →
            pairᵉ
              ( λ qᵉ →
                contradiction-le-ℕᵉ k'ᵉ
                  ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
                  ( pᵉ)
                  ( pr2ᵉ (pr2ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ)) k'ᵉ (inlᵉ qᵉ)))
              ( λ rᵉ →
                contradiction-le-ℕᵉ k'ᵉ
                  ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
                  ( pᵉ)
                  ( pr2ᵉ (pr2ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ)) k'ᵉ (inrᵉ rᵉ))))
          ( λ k'ᵉ ineq'ᵉ _ →
            transitive-le-ℕᵉ k'ᵉ
              ( succ-ℕᵉ k'ᵉ)
              ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
              ( succ-le-ℕᵉ k'ᵉ)
              ( ineq'ᵉ))
          kᵉ (inrᵉ ineqᵉ)
      lemma2ᵉ :
        ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
        ( paᵉ :
          Σᵉ ( ℕᵉ)
            (λ kᵉ →
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) aᵉ) +ᵉ
              ( Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) xᵉ) bᵉ))) →
        ( sim-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( xᵉ)
          ( aᵉ)) +ᵉ
        ( sim-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( xᵉ)
          ( bᵉ))
      lemma2ᵉ gᵉ paᵉ =
        cases-lemma2ᵉ
          ( has-decidable-equality-ℕᵉ
            ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
            ( zero-ℕᵉ))
          ( pr1ᵉ (pr2ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ)))
          ( reflᵉ)
        where
        cases-lemma2ᵉ :
          is-decidableᵉ (Idᵉ (pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ)) zero-ℕᵉ) →
          (cᵉ :
            ( Idᵉ
              ( iterateᵉ
                ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
                ( map-equivᵉ gᵉ)
                ( xᵉ))
              ( aᵉ)) +ᵉ
            ( Idᵉ
              ( iterateᵉ
                ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
                ( map-equivᵉ gᵉ)
                ( xᵉ))
              ( bᵉ))) →
          Idᵉ cᵉ (pr1ᵉ (pr2ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))) →
          ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)
            ( aᵉ)) +ᵉ
          ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( xᵉ)
            ( bᵉ))
        cases-lemma2ᵉ (inlᵉ qᵉ) (inlᵉ cᵉ) rᵉ =
          inlᵉ
            ( unit-trunc-Propᵉ
              ( pairᵉ zero-ℕᵉ (trᵉ (λ zᵉ → Idᵉ (iterateᵉ zᵉ (map-equivᵉ gᵉ) xᵉ) aᵉ) qᵉ cᵉ)))
        cases-lemma2ᵉ (inlᵉ qᵉ) (inrᵉ cᵉ) rᵉ =
          inrᵉ
            ( unit-trunc-Propᵉ
              ( pairᵉ zero-ℕᵉ (trᵉ (λ zᵉ → Idᵉ (iterateᵉ zᵉ (map-equivᵉ gᵉ) xᵉ) bᵉ) qᵉ cᵉ)))
        cases-lemma2ᵉ (inrᵉ qᵉ) (inlᵉ cᵉ) rᵉ =
          inrᵉ (unit-trunc-Propᵉ
            ( pairᵉ
              ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
              ( apᵉ
                ( λ nᵉ →
                  iterateᵉ nᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
                ( pr2ᵉ (is-successor-k1ᵉ) ∙ᵉ
                  commutative-add-ℕᵉ (pr1ᵉ is-successor-k1ᵉ) (succ-ℕᵉ zero-ℕᵉ)) ∙ᵉ
                ( iterate-add-ℕᵉ
                  ( succ-ℕᵉ zero-ℕᵉ)
                  ( pr1ᵉ is-successor-k1ᵉ)
                  ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                  ( xᵉ) ∙ᵉ
                  ( apᵉ
                    ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                    ( equal-iterate-transposition-same-orbitsᵉ
                      ( gᵉ)
                      ( paᵉ)
                      ( pr1ᵉ is-successor-k1ᵉ)
                      ( trᵉ
                        ( le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ))
                        ( invᵉ (pr2ᵉ is-successor-k1ᵉ))
                        ( succ-le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ)))) ∙ᵉ
                    ( apᵉ
                      ( λ nᵉ →
                        map-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ)
                          ( iterateᵉ nᵉ (map-equivᵉ gᵉ) xᵉ))
                      ( invᵉ (pr2ᵉ is-successor-k1ᵉ)) ∙ᵉ
                      ( apᵉ
                        ( map-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ))
                        ( cᵉ) ∙ᵉ
                        left-computation-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ))))))))
          where
          is-successor-k1ᵉ :
            is-successor-ℕᵉ (pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
          is-successor-k1ᵉ = is-successor-is-nonzero-ℕᵉ qᵉ
        cases-lemma2ᵉ (inrᵉ qᵉ) (inrᵉ cᵉ) rᵉ = inlᵉ (unit-trunc-Propᵉ
          ( pairᵉ
            ( pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
            ( apᵉ
              ( λ nᵉ → iterateᵉ nᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) xᵉ)
              ( pr2ᵉ (is-successor-k1ᵉ) ∙ᵉ
                commutative-add-ℕᵉ (pr1ᵉ is-successor-k1ᵉ) (succ-ℕᵉ zero-ℕᵉ)) ∙ᵉ
              ( (iterate-add-ℕᵉ
                  ( succ-ℕᵉ zero-ℕᵉ)
                  ( pr1ᵉ is-successor-k1ᵉ)
                  ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                  ( xᵉ)) ∙ᵉ
                ( apᵉ
                  ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
                  ( equal-iterate-transposition-same-orbitsᵉ
                    ( gᵉ)
                    ( paᵉ)
                    ( pr1ᵉ is-successor-k1ᵉ)
                    ( trᵉ
                      ( le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ))
                      ( invᵉ (pr2ᵉ is-successor-k1ᵉ))
                      ( succ-le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ)))) ∙ᵉ
                  ( apᵉ
                    ( λ nᵉ →
                      map-standard-transpositionᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ)
                        ( iterateᵉ nᵉ (map-equivᵉ gᵉ) xᵉ))
                    ( invᵉ (pr2ᵉ is-successor-k1ᵉ)) ∙ᵉ
                    ( ( apᵉ
                        ( map-standard-transpositionᵉ
                          ( has-decidable-equality-countᵉ eXᵉ)
                          ( npᵉ))
                        ( cᵉ)) ∙ᵉ
                      right-computation-standard-transpositionᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ))))))))
          where
          is-successor-k1ᵉ :
            is-successor-ℕᵉ (pr1ᵉ (minimal-element-iterate-2-a-bᵉ gᵉ paᵉ))
          is-successor-k1ᵉ = is-successor-is-nonzero-ℕᵉ qᵉ
      lemma3ᵉ :
        ( ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ
                ( composition-transposition-a-bᵉ gᵉ)))
            ( xᵉ)
            ( aᵉ)) +ᵉ
          ( sim-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ
                ( composition-transposition-a-bᵉ gᵉ)))
            ( xᵉ)
            ( bᵉ))) →
          sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ aᵉ
      lemma3ᵉ (inlᵉ Tᵉ) =
        trᵉ
          (λ fᵉ → sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ fᵉ) xᵉ aᵉ)
          { xᵉ = composition-transposition-a-bᵉ (composition-transposition-a-bᵉ gᵉ)}
          {yᵉ = gᵉ}
          ( eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ))
          ( Tᵉ)
      lemma3ᵉ (inrᵉ Tᵉ) =
        transitive-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ gᵉ)
          ( _)
          ( _)
          ( _)
          ( symmetric-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ gᵉ) _ _ Pᵉ)
          ( trᵉ
            ( λ gᵉ →
              sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) xᵉ bᵉ)
            { xᵉ =
              composition-transposition-a-bᵉ (composition-transposition-a-bᵉ gᵉ)}
            {yᵉ = gᵉ}
            ( eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ))
            ( Tᵉ))

  private
    module _
      ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
      ( Pᵉ :
        sim-equivalence-relationᵉ
          ( same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ))
          ( aᵉ)
          ( bᵉ))
      ( hᵉ :
        countᵉ
          ( equivalence-classᵉ
            ( same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ))))
      where

      h'-inlᵉ :
        ( kᵉ : Finᵉ (number-of-elements-countᵉ hᵉ))
        ( Tᵉ : equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ)) →
        Idᵉ (map-equiv-countᵉ hᵉ kᵉ) Tᵉ →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ) Tᵉ aᵉ) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ) Tᵉ bᵉ) →
        equivalence-classᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
      h'-inlᵉ kᵉ Tᵉ pᵉ (inlᵉ qᵉ) rᵉ =
        classᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( aᵉ)
      h'-inlᵉ kᵉ Tᵉ pᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) =
        ex-falsoᵉ
          ( nqᵉ
            ( transitive-is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ gᵉ)
              ( Tᵉ)
              ( bᵉ)
              ( aᵉ)
              ( rᵉ)
              ( symmetric-equivalence-relationᵉ
                ( same-orbits-permutation-countᵉ gᵉ) _ _ Pᵉ)))
      h'-inlᵉ kᵉ Tᵉ pᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) =
        conserves-other-orbits-transposition-quotientᵉ gᵉ Tᵉ nqᵉ nrᵉ
      h'ᵉ :
        Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ hᵉ)) →
        equivalence-classᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))

      h'ᵉ (inlᵉ kᵉ) = h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ
        ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ)
          ( map-equiv-countᵉ hᵉ kᵉ)
          ( aᵉ))
        ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ)
          ( map-equiv-countᵉ hᵉ kᵉ)
          ( bᵉ))
      h'ᵉ (inrᵉ kᵉ) =
        classᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( bᵉ)

      cases-inv-h'ᵉ :
        ( Tᵉ :
          equivalence-classᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( Tᵉ)
            ( aᵉ)) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( Tᵉ)
            ( bᵉ)) →
        Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ hᵉ))
      cases-inv-h'ᵉ Tᵉ (inlᵉ Qᵉ) Rᵉ =
        inlᵉ
          ( map-inv-equiv-countᵉ hᵉ (classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
      cases-inv-h'ᵉ Tᵉ (inrᵉ NQᵉ) (inlᵉ Rᵉ) = inrᵉ starᵉ
      cases-inv-h'ᵉ Tᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ) =
        inlᵉ
          ( map-inv-equiv-countᵉ hᵉ
            ( pairᵉ
              ( pr1ᵉ Tᵉ)
              ( trᵉ
                ( λ fᵉ →
                  is-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ fᵉ)
                    ( pr1ᵉ Tᵉ))
                { xᵉ =
                  composition-transposition-a-bᵉ
                    ( composition-transposition-a-bᵉ gᵉ)}
                { yᵉ = gᵉ}
                ( eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ))
                ( pr2ᵉ
                  ( conserves-other-orbits-transposition-quotientᵉ
                    (composition-transposition-a-bᵉ gᵉ) Tᵉ NQᵉ NRᵉ)))))

      inv-h'ᵉ :
        ( Tᵉ :
          equivalence-classᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ gᵉ))) →
        Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ hᵉ))
      inv-h'ᵉ Tᵉ =
        cases-inv-h'ᵉ Tᵉ
          ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)
            ( Tᵉ)
            ( aᵉ))
          ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)
            ( Tᵉ)
            ( bᵉ))
      H-conservesᵉ :
        ( Tᵉ :
          equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ)))
        ( NQᵉ :
          ¬ᵉ ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( Tᵉ)
              ( aᵉ)))
        ( NRᵉ :
          ¬ᵉ ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( Tᵉ)
              ( bᵉ))) →
        is-equivalence-classᵉ (same-orbits-permutation-countᵉ gᵉ) (pr1ᵉ Tᵉ)
      H-conservesᵉ Tᵉ NQᵉ NRᵉ =
        trᵉ
          ( λ fᵉ →
            is-equivalence-classᵉ (same-orbits-permutation-countᵉ fᵉ) (pr1ᵉ Tᵉ))
          { xᵉ = composition-transposition-a-bᵉ (composition-transposition-a-bᵉ gᵉ)}
          { yᵉ = gᵉ}
          ( eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ))
          ( pr2ᵉ
            ( conserves-other-orbits-transposition-quotientᵉ
              (composition-transposition-a-bᵉ gᵉ) Tᵉ NQᵉ NRᵉ))

      retraction-h'-inr-inrᵉ :
        ( Tᵉ :
          equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ)))
        ( NQᵉ :
          ¬ᵉ ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( Tᵉ)
              ( aᵉ)))
        ( NRᵉ :
          ¬ᵉ ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( Tᵉ)
              ( bᵉ))) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ gᵉ)
            ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
            ( aᵉ)) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ gᵉ)
            ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
            ( bᵉ)) →
        Idᵉ
          ( h'ᵉ (inlᵉ (map-inv-equiv-countᵉ hᵉ
            ( pairᵉ
              ( pr1ᵉ Tᵉ)
              ( trᵉ
                ( λ fᵉ →
                  is-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ fᵉ)
                    ( pr1ᵉ Tᵉ))
                { xᵉ =
                  composition-transposition-a-bᵉ
                    (composition-transposition-a-bᵉ gᵉ)}
                {yᵉ = gᵉ}
                ( eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ))
                ( pr2ᵉ
                  ( conserves-other-orbits-transposition-quotientᵉ
                    (composition-transposition-a-bᵉ gᵉ) Tᵉ NQᵉ NRᵉ)))))))
          ( Tᵉ)
      retraction-h'-inr-inrᵉ Tᵉ NQᵉ NRᵉ (inlᵉ Q'ᵉ) R'ᵉ = ex-falsoᵉ (NQᵉ Q'ᵉ)
      retraction-h'-inr-inrᵉ Tᵉ NQᵉ NRᵉ (inrᵉ NQ'ᵉ) (inlᵉ R'ᵉ) = ex-falsoᵉ (NRᵉ R'ᵉ)
      retraction-h'-inr-inrᵉ Tᵉ NQᵉ NRᵉ (inrᵉ NQ'ᵉ) (inrᵉ NR'ᵉ) =
        ( apᵉ
          ( λ wᵉ →
            h'-inlᵉ
              ( map-inv-equiv-countᵉ hᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
              ( map-equivᵉ (pr1ᵉ wᵉ) (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
              ( pr2ᵉ wᵉ)
              ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( gᵉ)
                  ( map-equivᵉ (pr1ᵉ wᵉ) (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                  ( aᵉ))
              ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( gᵉ)
                  ( map-equivᵉ (pr1ᵉ wᵉ) (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                  ( bᵉ)))
          { xᵉ = pairᵉ ((equiv-countᵉ hᵉ) ∘eᵉ (inv-equiv-countᵉ hᵉ)) reflᵉ}
          { yᵉ = pairᵉ
            id-equivᵉ
              ( apᵉ
                ( λ fᵉ → map-equivᵉ fᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))}
          ( eq-pair-Σᵉ
            ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ))
            ( eq-is-propᵉ
              ( is-prop-type-Propᵉ
                ( Id-Propᵉ
                  ( equivalence-class-Setᵉ (same-orbits-permutation-countᵉ gᵉ))
                  ( map-equiv-countᵉ
                    ( hᵉ)
                    ( map-inv-equiv-countᵉ
                      ( hᵉ)
                      ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))))
                  ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))))))) ∙ᵉ
          ( apᵉ
            (λ wᵉ →
              h'-inlᵉ
                ( map-inv-equiv-countᵉ hᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                ( apᵉ
                  ( λ fᵉ → map-equivᵉ fᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                  ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))
                ( wᵉ)
                ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( gᵉ)
                  ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                  ( bᵉ)))
            { xᵉ =
              is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( gᵉ)
                ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                ( aᵉ)}
            { yᵉ = inrᵉ NQ'ᵉ}
            ( eq-is-propᵉ
              ( is-prop-is-decidableᵉ
                ( is-prop-is-in-equivalence-classᵉ
                  ( same-orbits-permutation-countᵉ gᵉ)
                  ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                  ( aᵉ)))) ∙ᵉ
            ( (apᵉ
              ( λ wᵉ →
                h'-inlᵉ
                  ( map-inv-equiv-countᵉ hᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                  ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                  ( apᵉ
                    ( λ fᵉ → map-equivᵉ fᵉ (pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)))
                    ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))
                  ( inrᵉ NQ'ᵉ)
                  ( wᵉ))
              { xᵉ =
                is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                  ( number-of-elements-countᵉ eXᵉ)
                  ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                  ( gᵉ)
                  ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                  ( bᵉ)}
              { yᵉ = inrᵉ NR'ᵉ}
              ( eq-is-propᵉ
                ( is-prop-is-decidableᵉ
                  ( is-prop-is-in-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ gᵉ)
                    ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
                    ( bᵉ)))) ∙ᵉ
              ( eq-pair-eq-fiberᵉ ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))
      retraction-h'ᵉ :
        (Tᵉ :
          equivalence-classᵉ
            ( same-orbits-permutation-countᵉ
              ( composition-transposition-a-bᵉ gᵉ))) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( Tᵉ)
            ( aᵉ)) →
        is-decidableᵉ
          ( is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( Tᵉ)
            ( bᵉ)) →
        Idᵉ (h'ᵉ (inv-h'ᵉ Tᵉ)) Tᵉ
      retraction-h'ᵉ Tᵉ (inlᵉ Qᵉ) Rᵉ =
        trᵉ
          (λ wᵉ →
            Idᵉ
              ( h'ᵉ
                ( cases-inv-h'ᵉ Tᵉ wᵉ
                  ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                    ( number-of-elements-countᵉ eXᵉ)
                    ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                    ( composition-transposition-a-bᵉ gᵉ)
                    ( Tᵉ)
                    ( bᵉ))))
            ( Tᵉ))
          { xᵉ = inlᵉ Qᵉ}
          { yᵉ =
            is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)
              ( Tᵉ)
              ( aᵉ)}
          ( eq-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-prop-is-in-equivalence-classᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( Tᵉ)
                ( aᵉ))))
          ( apᵉ
            ( λ wᵉ →
              h'-inlᵉ
                ( map-inv-equiv-countᵉ hᵉ
                  ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                ( map-equivᵉ
                  ( pr1ᵉ wᵉ)
                  ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                (pr2ᵉ wᵉ)
                ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                    ( number-of-elements-countᵉ eXᵉ)
                    ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                    ( gᵉ)
                    ( map-equivᵉ
                      ( pr1ᵉ wᵉ)
                      ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                    ( aᵉ))
                ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                    ( number-of-elements-countᵉ eXᵉ)
                    ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))) gᵉ
                    ( map-equivᵉ
                      ( pr1ᵉ wᵉ)
                      ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                    ( bᵉ)))
            { xᵉ = pairᵉ ((equiv-countᵉ hᵉ) ∘eᵉ (inv-equiv-countᵉ hᵉ)) reflᵉ}
            { yᵉ =
              pairᵉ
                ( id-equivᵉ)
                ( apᵉ
                  ( λ fᵉ →
                    map-equivᵉ fᵉ (classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                  ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))}
            ( eq-pair-Σᵉ
              ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ))
              ( eq-is-propᵉ
                ( is-prop-type-Propᵉ
                  ( Id-Propᵉ
                    ( equivalence-class-Setᵉ (same-orbits-permutation-countᵉ gᵉ))
                    ( map-equiv-countᵉ hᵉ
                      ( map-inv-equiv-countᵉ hᵉ
                        ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ)))
                    ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))))) ∙ᵉ
            ( apᵉ
              ( λ wᵉ →
                h'-inlᵉ
                  ( map-inv-equiv-countᵉ
                    ( hᵉ)
                    ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                  ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ)
                  ( apᵉ
                    ( λ fᵉ →
                      map-equivᵉ fᵉ (classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                    ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))
                  ( wᵉ)
                  ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                      ( number-of-elements-countᵉ eXᵉ)
                      ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                      ( gᵉ)
                      (classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ)
                      ( bᵉ)))
              { xᵉ =
                is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( gᵉ)
                ( map-equivᵉ id-equivᵉ
                  ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
                ( aᵉ)}
              { yᵉ =
                inlᵉ
                  ( is-in-equivalence-class-eq-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ gᵉ)
                    ( aᵉ)
                    ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ)
                    ( reflᵉ))}
              ( eq-is-propᵉ
                ( is-prop-is-decidableᵉ
                  ( is-prop-is-in-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ gᵉ)
                    ( classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ) aᵉ))) ∙ᵉ
              ( eq-effective-quotient'ᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( aᵉ)
                ( Tᵉ)
                ( Qᵉ))))
      retraction-h'ᵉ Tᵉ (inrᵉ NQᵉ) (inlᵉ Rᵉ) =
        trᵉ
          (λ wᵉ → Idᵉ (h'ᵉ (cases-inv-h'ᵉ Tᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ))) Tᵉ)
          {xᵉ = pairᵉ (inrᵉ NQᵉ) (inlᵉ Rᵉ)}
          {yᵉ = pairᵉ
            (is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)
              ( Tᵉ)
              ( aᵉ))
            ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)
              ( Tᵉ)
              ( bᵉ))}
          ( eq-is-propᵉ
            ( is-prop-Σᵉ
              ( is-prop-is-decidableᵉ
                ( is-prop-is-in-equivalence-classᵉ
                  ( same-orbits-permutation-countᵉ
                    ( composition-transposition-a-bᵉ gᵉ))
                  ( Tᵉ)
                  ( aᵉ)))
              ( λ _ →
                is-prop-is-decidableᵉ
                  ( is-prop-is-in-equivalence-classᵉ
                    ( same-orbits-permutation-countᵉ
                      ( composition-transposition-a-bᵉ gᵉ))
                    ( Tᵉ)
                    ( bᵉ)))))
          ( eq-effective-quotient'ᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( bᵉ)
            ( Tᵉ)
            ( Rᵉ))
      retraction-h'ᵉ Tᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ) =
        trᵉ
          (λ wᵉ → Idᵉ (h'ᵉ (cases-inv-h'ᵉ Tᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ))) Tᵉ)
          {xᵉ = pairᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ)}
          {yᵉ = pairᵉ
            (is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)
              ( Tᵉ)
              ( aᵉ))
            (is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)
              ( Tᵉ)
              ( bᵉ))}
          ( eq-is-propᵉ
            ( is-prop-Σᵉ
              ( is-prop-is-decidableᵉ
                ( is-prop-is-in-equivalence-classᵉ
                  ( same-orbits-permutation-countᵉ
                    ( composition-transposition-a-bᵉ gᵉ))
                  ( Tᵉ)
                  ( aᵉ)))
              ( λ _ →
                is-prop-is-decidableᵉ
                ( is-prop-is-in-equivalence-classᵉ
                  ( same-orbits-permutation-countᵉ
                    ( composition-transposition-a-bᵉ gᵉ))
                  ( Tᵉ)
                  ( bᵉ)))))
          ( retraction-h'-inr-inrᵉ Tᵉ NQᵉ NRᵉ
            ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ)
              ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ))
              ( aᵉ))
            ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ)
              ( pairᵉ (pr1ᵉ Tᵉ) (H-conservesᵉ Tᵉ NQᵉ NRᵉ)) bᵉ))
      section-h'-inlᵉ :
        ( kᵉ : Finᵉ (number-of-elements-countᵉ hᵉ))
        ( Qᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ gᵉ)
              ( map-equiv-countᵉ hᵉ kᵉ)
              ( aᵉ)))
        ( Rᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ gᵉ)
              ( map-equiv-countᵉ hᵉ kᵉ)
              ( bᵉ)))
        ( Q'ᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ Qᵉ Rᵉ)
              ( aᵉ)))
        ( R'ᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ Qᵉ Rᵉ)
              ( bᵉ))) →
        Idᵉ
          ( cases-inv-h'ᵉ (h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ Qᵉ Rᵉ) Q'ᵉ R'ᵉ)
          ( inlᵉ kᵉ)
      section-h'-inlᵉ kᵉ (inlᵉ Qᵉ) Rᵉ (inlᵉ Q'ᵉ) R'ᵉ =
        apᵉ inlᵉ
          ( is-injective-equivᵉ (equiv-countᵉ hᵉ)
            ( apᵉ
              ( λ fᵉ → map-equivᵉ fᵉ (classᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ))
              ( right-inverse-law-equivᵉ (equiv-countᵉ hᵉ)) ∙ᵉ
              ( eq-effective-quotient'ᵉ
                ( same-orbits-permutation-countᵉ gᵉ)
                ( aᵉ)
                ( map-equiv-countᵉ hᵉ kᵉ)
                ( Qᵉ))))
      section-h'-inlᵉ kᵉ (inlᵉ Qᵉ) Rᵉ (inrᵉ NQ'ᵉ) R'ᵉ =
        ex-falsoᵉ
          ( NQ'ᵉ
            ( is-in-equivalence-class-eq-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( aᵉ)
              ( classᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( aᵉ))
              ( reflᵉ)))
      section-h'-inlᵉ kᵉ (inrᵉ NQᵉ) (inlᵉ Rᵉ) Q'ᵉ R'ᵉ =
        ex-falsoᵉ
        ( NQᵉ
          ( transitive-is-in-equivalence-classᵉ
            ( same-orbits-permutation-countᵉ gᵉ)
            ( map-equiv-countᵉ hᵉ kᵉ)
            ( bᵉ)
            ( aᵉ)
            ( Rᵉ)
            ( symmetric-equivalence-relationᵉ
              ( same-orbits-permutation-countᵉ gᵉ) _ _ Pᵉ)))
      section-h'-inlᵉ kᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ) (inlᵉ Q'ᵉ) R'ᵉ = ex-falsoᵉ (NQᵉ Q'ᵉ)
      section-h'-inlᵉ kᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ) (inrᵉ NQ'ᵉ) (inlᵉ R'ᵉ) = ex-falsoᵉ (NRᵉ R'ᵉ)
      section-h'-inlᵉ kᵉ (inrᵉ NQᵉ) (inrᵉ NRᵉ) (inrᵉ NQ'ᵉ) (inrᵉ NR'ᵉ) =
        apᵉ
          ( inlᵉ)
          ( apᵉ
            ( map-inv-equiv-countᵉ hᵉ)
            ( eq-pair-eq-fiberᵉ
              ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)) ∙ᵉ
            apᵉ (λ fᵉ → map-equivᵉ fᵉ kᵉ) (left-inverse-law-equivᵉ (equiv-countᵉ hᵉ)))
      section-h'-inrᵉ :
        ( Qᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( classᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( bᵉ))
              ( aᵉ))) →
        ( Rᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( classᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( bᵉ))
              ( bᵉ))) →
        Idᵉ
          ( cases-inv-h'ᵉ
            ( classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( bᵉ))
            ( Qᵉ)
            ( Rᵉ))
          ( inrᵉ starᵉ)
      section-h'-inrᵉ (inlᵉ Qᵉ) Rᵉ =
        ex-falsoᵉ (not-same-orbits-transposition-same-orbitsᵉ gᵉ Pᵉ
          ( symmetric-equivalence-relationᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            _ _
            ( Qᵉ)))
      section-h'-inrᵉ (inrᵉ Qᵉ) (inlᵉ Rᵉ) = reflᵉ
      section-h'-inrᵉ (inrᵉ Qᵉ) (inrᵉ NRᵉ) =
        ex-falsoᵉ
          ( NRᵉ
            ( is-in-equivalence-class-eq-equivalence-classᵉ
              ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
              ( bᵉ)
              ( classᵉ
                ( same-orbits-permutation-countᵉ
                  ( composition-transposition-a-bᵉ gᵉ))
                ( bᵉ))
              ( reflᵉ)))
      section-h'ᵉ :
        (kᵉ : Finᵉ (succ-ℕᵉ (number-of-elements-countᵉ hᵉ))) → Idᵉ (inv-h'ᵉ (h'ᵉ kᵉ)) kᵉ
      section-h'ᵉ (inlᵉ kᵉ) =
        section-h'-inlᵉ kᵉ Qᵉ Rᵉ
          ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)
            ( h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ Qᵉ Rᵉ)
            ( aᵉ))
          ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)
            ( h'-inlᵉ kᵉ (map-equiv-countᵉ hᵉ kᵉ) reflᵉ Qᵉ Rᵉ)
            ( bᵉ))
        where
        Qᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                (pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( gᵉ))
              ( map-equiv-countᵉ hᵉ kᵉ)
              ( aᵉ))
        Qᵉ =
          is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ)
            ( map-equiv-countᵉ hᵉ kᵉ)
            ( aᵉ)
        Rᵉ :
          is-decidableᵉ
            ( is-in-equivalence-classᵉ
              ( same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( gᵉ))
              ( map-equiv-countᵉ hᵉ kᵉ)
              ( bᵉ))
        Rᵉ =
          is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ)
            ( map-equiv-countᵉ hᵉ kᵉ)
            ( bᵉ)
      section-h'ᵉ (inrᵉ starᵉ) =
        section-h'-inrᵉ
        ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( composition-transposition-a-bᵉ gᵉ)
          ( classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( bᵉ))
          ( aᵉ))
        ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( composition-transposition-a-bᵉ gᵉ)
          ( classᵉ
            ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
            ( bᵉ))
          ( bᵉ))

  transf-same-orbits-countᵉ :
    ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
    ( Pᵉ :
      sim-equivalence-relationᵉ
        ( same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))
        ( aᵉ)
        ( bᵉ)) →
    countᵉ
      ( equivalence-classᵉ
        ( same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))) →
      countᵉ
        ( equivalence-classᵉ
          ( same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)))
  transf-same-orbits-countᵉ gᵉ Pᵉ hᵉ =
    pairᵉ
      ( succ-ℕᵉ (number-of-elements-countᵉ hᵉ))
      ( pairᵉ
        ( h'ᵉ gᵉ Pᵉ hᵉ)
        ( is-equiv-is-invertibleᵉ
          ( inv-h'ᵉ gᵉ Pᵉ hᵉ)
          ( λ Tᵉ →
            retraction-h'ᵉ
              ( gᵉ)
              ( Pᵉ)
              ( hᵉ)
              ( Tᵉ)
              ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( composition-transposition-a-bᵉ gᵉ)
                ( Tᵉ)
                ( aᵉ))
              ( is-decidable-is-in-equivalence-class-same-orbits-permutationᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( composition-transposition-a-bᵉ gᵉ)
                ( Tᵉ)
                ( bᵉ)))
          ( section-h'ᵉ gᵉ Pᵉ hᵉ)))

  abstract
    number-orbits-composition-transpositionᵉ :
      ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
      ( Pᵉ :
        sim-equivalence-relationᵉ
          ( same-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ))
          ( aᵉ)
          ( bᵉ)) →
      Idᵉ
        ( succ-ℕᵉ
          ( number-of-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ)))
        ( number-of-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( composition-transposition-a-bᵉ gᵉ))
    number-orbits-composition-transpositionᵉ gᵉ Pᵉ =
      apply-universal-property-trunc-Propᵉ
        ( has-finite-number-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))
        ( Id-Propᵉ
          ( ℕ-Setᵉ)
          ( succ-ℕᵉ
            ( number-of-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ)))
          ( number-of-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)))
        ( λ hᵉ →
          ( apᵉ
            ( succ-ℕᵉ ∘ᵉ number-of-elements-is-finiteᵉ)
            ( eq-is-propᵉ is-prop-type-trunc-Propᵉ) ∙ᵉ
            ( apᵉ
              ( succ-ℕᵉ ∘ᵉ pr1ᵉ)
              ( all-elements-equal-has-finite-cardinalityᵉ
                ( has-finite-cardinality-is-finiteᵉ (unit-trunc-Propᵉ hᵉ))
                ( has-finite-cardinality-countᵉ hᵉ)) ∙ᵉ
              ( apᵉ
                ( pr1ᵉ)
                ( all-elements-equal-has-finite-cardinalityᵉ
                  ( has-finite-cardinality-countᵉ
                    ( transf-same-orbits-countᵉ gᵉ Pᵉ hᵉ))
                  ( has-finite-cardinality-is-finiteᵉ
                    ( unit-trunc-Propᵉ (transf-same-orbits-countᵉ gᵉ Pᵉ hᵉ)))) ∙ᵉ
                apᵉ
                  ( number-of-elements-is-finiteᵉ)
                  ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)))))

  abstract
    same-orbits-transposition-not-same-orbitsᵉ :
      ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
      ( NPᵉ :
        ¬ᵉ (sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ bᵉ)) →
        sim-equivalence-relationᵉ
          ( same-orbits-permutation-countᵉ (composition-transposition-a-bᵉ gᵉ))
          ( aᵉ)
          ( bᵉ)
    same-orbits-transposition-not-same-orbitsᵉ gᵉ NPᵉ =
      unit-trunc-Propᵉ (pairᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ) lemmaᵉ)
      where
      minimal-element-iterate-repeatingᵉ :
        minimal-element-ℕᵉ
          ( λ kᵉ → is-nonzero-ℕᵉ kᵉ ×ᵉ Idᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ) aᵉ)
      minimal-element-iterate-repeatingᵉ =
        minimal-element-iterate-nonzeroᵉ
          ( gᵉ)
          ( aᵉ)
          ( aᵉ)
          ( has-finite-orbits-permutationᵉ Xᵉ eXᵉ gᵉ aᵉ)
      neq-iterate-nonzero-le-minimal-elementᵉ :
        (kᵉ : ℕᵉ) →
        is-nonzero-ℕᵉ kᵉ ×ᵉ le-ℕᵉ kᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ) →
        (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ ≠ᵉ aᵉ) ×ᵉ (iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ ≠ᵉ bᵉ)
      pr1ᵉ (neq-iterate-nonzero-le-minimal-elementᵉ kᵉ (pairᵉ nzᵉ ineqᵉ)) Qᵉ =
        contradiction-le-ℕᵉ kᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ) ineqᵉ
          (pr2ᵉ (pr2ᵉ minimal-element-iterate-repeatingᵉ) kᵉ (pairᵉ nzᵉ Qᵉ))
      pr2ᵉ (neq-iterate-nonzero-le-minimal-elementᵉ kᵉ (pairᵉ nzᵉ ineqᵉ)) Rᵉ =
        NPᵉ (unit-trunc-Propᵉ (pairᵉ kᵉ Rᵉ))
      equal-iterate-transposition-aᵉ :
        (kᵉ : ℕᵉ) → le-ℕᵉ kᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ) →
        Idᵉ
          ( iterateᵉ kᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ)
          ( iterateᵉ kᵉ (map-equivᵉ gᵉ) aᵉ)
      equal-iterate-transposition-aᵉ kᵉ ineqᵉ =
        equal-iterate-transpositionᵉ aᵉ gᵉ
          ( λ k'ᵉ →
            ( is-nonzero-ℕᵉ k'ᵉ) ×ᵉ
            ( le-ℕᵉ k'ᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ)))
          ( neq-iterate-nonzero-le-minimal-elementᵉ)
          ( λ nᵉ (pairᵉ _ sᵉ) nzᵉ →
            pairᵉ
              ( nzᵉ)
              ( transitive-le-ℕᵉ nᵉ
                ( succ-ℕᵉ nᵉ)
                ( pr1ᵉ minimal-element-iterate-repeatingᵉ)
                ( succ-le-ℕᵉ nᵉ)
                ( sᵉ)))
          ( kᵉ)
          ( cases-equal-iterate-transposition-aᵉ
            ( has-decidable-equality-ℕᵉ kᵉ zero-ℕᵉ))
        where
        cases-equal-iterate-transposition-aᵉ :
          is-decidableᵉ (is-zero-ℕᵉ kᵉ) →
          ( is-zero-ℕᵉ kᵉ) +ᵉ
          ( is-nonzero-ℕᵉ kᵉ ×ᵉ le-ℕᵉ kᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ))
        cases-equal-iterate-transposition-aᵉ (inlᵉ sᵉ) = inlᵉ sᵉ
        cases-equal-iterate-transposition-aᵉ (inrᵉ sᵉ) = inrᵉ (pairᵉ sᵉ ineqᵉ)
      lemmaᵉ :
        Idᵉ
          ( iterateᵉ
            ( pr1ᵉ minimal-element-iterate-repeatingᵉ)
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
            ( aᵉ))
          ( bᵉ)
      lemmaᵉ =
        ( apᵉ
          ( λ nᵉ → iterateᵉ nᵉ (map-equivᵉ (composition-transposition-a-bᵉ gᵉ)) aᵉ)
          ( pr2ᵉ (is-successor-k1ᵉ) ∙ᵉ
            commutative-add-ℕᵉ (pr1ᵉ is-successor-k1ᵉ) (succ-ℕᵉ zero-ℕᵉ))) ∙ᵉ
        ( iterate-add-ℕᵉ
          ( succ-ℕᵉ zero-ℕᵉ)
          ( pr1ᵉ is-successor-k1ᵉ)
          ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
          ( aᵉ) ∙ᵉ
          ( apᵉ
            ( map-equivᵉ (composition-transposition-a-bᵉ gᵉ))
            ( equal-iterate-transposition-aᵉ
              ( pr1ᵉ is-successor-k1ᵉ)
              ( trᵉ
                ( le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ))
                ( invᵉ (pr2ᵉ is-successor-k1ᵉ))
                ( succ-le-ℕᵉ (pr1ᵉ is-successor-k1ᵉ)))) ∙ᵉ
            ( apᵉ
              ( λ nᵉ →
                map-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ)
                  ( iterateᵉ nᵉ (map-equivᵉ gᵉ) aᵉ))
              ( invᵉ (pr2ᵉ is-successor-k1ᵉ)) ∙ᵉ
              ( apᵉ
                ( map-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ))
                ( pr2ᵉ (pr1ᵉ (pr2ᵉ minimal-element-iterate-repeatingᵉ))) ∙ᵉ
                ( left-computation-standard-transpositionᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( npᵉ))))))
        where
        is-successor-k1ᵉ : is-successor-ℕᵉ (pr1ᵉ minimal-element-iterate-repeatingᵉ)
        is-successor-k1ᵉ =
          is-successor-is-nonzero-ℕᵉ
            ( pr1ᵉ (pr1ᵉ (pr2ᵉ minimal-element-iterate-repeatingᵉ)))

  abstract
    number-orbits-composition-transposition'ᵉ :
      ( gᵉ : Xᵉ ≃ᵉ Xᵉ)
      (NPᵉ :
        ¬ᵉ ( sim-equivalence-relationᵉ
            ( same-orbits-permutationᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ))
            ( aᵉ)
            ( bᵉ))) →
      Idᵉ
        ( number-of-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))
        ( succ-ℕᵉ
          ( number-of-orbits-permutationᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)))
    number-orbits-composition-transposition'ᵉ gᵉ NPᵉ =
      ( apᵉ
        ( number-of-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ))))
        ( invᵉ (eq-htpy-equivᵉ (composition-transposition-a-b-involutionᵉ gᵉ)))) ∙ᵉ
        ( invᵉ
          ( number-orbits-composition-transpositionᵉ
            ( composition-transposition-a-bᵉ gᵉ)
            ( same-orbits-transposition-not-same-orbitsᵉ gᵉ NPᵉ)))

  abstract
    opposite-sign-composition-transposition-countᵉ :
      (gᵉ : Xᵉ ≃ᵉ Xᵉ) →
      Idᵉ
        ( sign-permutation-orbitᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ))
        ( succ-Finᵉ
          ( 2ᵉ)
          ( sign-permutation-orbitᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( composition-transposition-a-bᵉ gᵉ)))
    opposite-sign-composition-transposition-countᵉ gᵉ =
      cases-opposite-sign-composition-transpositionᵉ
        ( is-decidable-same-orbits-permutationᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( gᵉ)
          ( aᵉ)
          ( bᵉ))
      where
      cases-opposite-sign-composition-transpositionᵉ :
        is-decidableᵉ
          ( sim-equivalence-relationᵉ (same-orbits-permutation-countᵉ gᵉ) aᵉ bᵉ) →
        Idᵉ
          ( sign-permutation-orbitᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( gᵉ))
          ( succ-Finᵉ
            ( 2ᵉ)
            ( sign-permutation-orbitᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( composition-transposition-a-bᵉ gᵉ)))
      cases-opposite-sign-composition-transpositionᵉ (inlᵉ Pᵉ) =
        invᵉ
          ( is-involution-aut-Fin-two-ℕᵉ
            ( equiv-succ-Finᵉ 2ᵉ)
            ( sign-permutation-orbitᵉ
              ( number-of-elements-countᵉ eXᵉ)
              ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
              ( gᵉ))) ∙ᵉ
        apᵉ
          ( λ kᵉ →
            succ-Finᵉ
              ( 2ᵉ)
              ( iterateᵉ
                ( (number-of-elements-countᵉ eXᵉ) +ℕᵉ kᵉ)
                ( succ-Finᵉ 2ᵉ)
                ( zero-Finᵉ 1ᵉ)))
          ( number-orbits-composition-transpositionᵉ gᵉ Pᵉ)
      cases-opposite-sign-composition-transpositionᵉ (inrᵉ NPᵉ) =
        apᵉ
          ( λ kᵉ →
            iterateᵉ
              ( (number-of-elements-countᵉ eXᵉ) +ℕᵉ kᵉ)
              ( succ-Finᵉ 2ᵉ)
              ( zero-Finᵉ 1ᵉ))
          ( number-orbits-composition-transposition'ᵉ gᵉ NPᵉ)

module _
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) (eXᵉ : countᵉ Xᵉ)
  where

  abstract
    sign-list-transpositions-countᵉ :
      ( liᵉ :
        listᵉ
          ( Σᵉ ( Xᵉ → Decidable-Propᵉ lᵉ)
              ( λ Pᵉ →
                has-cardinalityᵉ 2 (Σᵉ Xᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))) →
      Idᵉ
        ( iterateᵉ
          ( length-listᵉ liᵉ)
          ( succ-Finᵉ 2ᵉ)
          ( sign-permutation-orbitᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( id-equivᵉ)))
        ( sign-permutation-orbitᵉ
          ( number-of-elements-countᵉ eXᵉ)
          ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
          ( permutation-list-transpositionsᵉ liᵉ))
    sign-list-transpositions-countᵉ nilᵉ = reflᵉ
    sign-list-transpositions-countᵉ (consᵉ tᵉ liᵉ) =
      apᵉ (succ-Finᵉ 2ᵉ)
        ( sign-list-transpositions-countᵉ liᵉ ∙ᵉ
          opposite-sign-composition-transposition-countᵉ
            ( Xᵉ)
            ( eXᵉ)
            ( pr1ᵉ two-elements-tᵉ)
            ( pr1ᵉ (pr2ᵉ two-elements-tᵉ))
            ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-tᵉ)))
            ( permutation-list-transpositionsᵉ liᵉ)) ∙ᵉ
        ( is-involution-aut-Fin-two-ℕᵉ
          ( equiv-succ-Finᵉ 2ᵉ)
          ( sign-permutation-orbitᵉ
            ( number-of-elements-countᵉ eXᵉ)
            ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
            ( permutation-list-transpositionsᵉ
              ( consᵉ
                ( standard-2-Element-Decidable-Subtypeᵉ
                  ( has-decidable-equality-countᵉ eXᵉ)
                  ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-tᵉ))))
                ( liᵉ)))) ∙ᵉ
          ( apᵉ
            ( λ gᵉ →
              sign-permutation-orbitᵉ
                ( number-of-elements-countᵉ eXᵉ)
                ( pairᵉ Xᵉ (unit-trunc-Propᵉ (equiv-countᵉ eXᵉ)))
                ( permutation-list-transpositionsᵉ (consᵉ gᵉ liᵉ)))
            { xᵉ =
              standard-2-Element-Decidable-Subtypeᵉ
                ( has-decidable-equality-countᵉ eXᵉ)
                ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-tᵉ)))}
            { yᵉ = tᵉ}
            ( pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-tᵉ)))))
      where
      two-elements-tᵉ :
        Σᵉ ( Xᵉ)
          ( λ xᵉ →
            Σᵉ ( Xᵉ)
              ( λ yᵉ →
                Σᵉ ( xᵉ ≠ᵉ yᵉ)
                  ( λ npᵉ →
                    Idᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( has-decidable-equality-countᵉ eXᵉ)
                        ( npᵉ))
                      ( tᵉ))))
      two-elements-tᵉ = two-elements-transpositionᵉ eXᵉ tᵉ
```