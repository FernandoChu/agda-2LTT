# Transpositions

```agda
module finite-group-theory.transpositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-standard-finite-typesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.involutionsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Transpositions**ᵉ areᵉ [permutations](finite-group-theory.permutations.mdᵉ) thatᵉ
swapᵉ twoᵉ elements.ᵉ

## Definitions

### Transpositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)
  where

  map-transposition''ᵉ :
    Σᵉ Xᵉ (λ xᵉ → is-decidableᵉ (is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)) →
    Σᵉ Xᵉ (λ xᵉ → is-decidableᵉ (is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ))
  pr1ᵉ (map-transposition''ᵉ (pairᵉ xᵉ (inlᵉ pᵉ))) =
    pr1ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ))
  pr2ᵉ (map-transposition''ᵉ (pairᵉ xᵉ (inlᵉ pᵉ))) =
    inlᵉ (pr2ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ)))
  pr1ᵉ (map-transposition''ᵉ (pairᵉ xᵉ (inrᵉ npᵉ))) = xᵉ
  pr2ᵉ (map-transposition''ᵉ (pairᵉ xᵉ (inrᵉ npᵉ))) = inrᵉ npᵉ

  map-transposition'ᵉ :
    (xᵉ : Xᵉ) (dᵉ : is-decidableᵉ (is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)) → Xᵉ
  map-transposition'ᵉ xᵉ (inlᵉ pᵉ) =
    pr1ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ))
  map-transposition'ᵉ xᵉ (inrᵉ npᵉ) = xᵉ

  map-transpositionᵉ : Xᵉ → Xᵉ
  map-transpositionᵉ xᵉ =
    map-transposition'ᵉ xᵉ
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)

  preserves-subtype-map-transpositionᵉ :
    (xᵉ : Xᵉ) → is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ →
    is-in-2-Element-Decidable-Subtypeᵉ Pᵉ (map-transpositionᵉ xᵉ)
  preserves-subtype-map-transpositionᵉ xᵉ pᵉ =
    trᵉ
      ( λ Rᵉ → is-in-2-Element-Decidable-Subtypeᵉ Pᵉ (map-transposition'ᵉ xᵉ Rᵉ))
      { xᵉ = inlᵉ pᵉ}
      { yᵉ = is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ}
      ( eq-is-propᵉ
        ( is-prop-is-decidableᵉ
          ( is-prop-is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)))
      ( pr2ᵉ
        ( map-swap-2-Element-Typeᵉ
          ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
          ( pairᵉ xᵉ pᵉ)))

  is-involution-map-transposition'ᵉ :
    (xᵉ : Xᵉ) (dᵉ : is-decidableᵉ (is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ))
    (d'ᵉ : is-decidableᵉ
          ( is-in-2-Element-Decidable-Subtypeᵉ Pᵉ (map-transposition'ᵉ xᵉ dᵉ))) →
    Idᵉ (map-transposition'ᵉ (map-transposition'ᵉ xᵉ dᵉ) d'ᵉ) xᵉ
  is-involution-map-transposition'ᵉ xᵉ (inlᵉ pᵉ) (inlᵉ p'ᵉ) =
    ( apᵉ
      ( λ yᵉ → map-transposition'ᵉ (map-transposition'ᵉ xᵉ (inlᵉ pᵉ)) (inlᵉ yᵉ))
      ( eq-is-in-2-Element-Decidable-Subtypeᵉ Pᵉ)) ∙ᵉ
    ( apᵉ
      ( pr1ᵉ)
      ( is-involution-aut-2-element-typeᵉ
        ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
        ( swap-2-Element-Decidable-Subtypeᵉ Pᵉ)
        ( pairᵉ xᵉ pᵉ)))
  is-involution-map-transposition'ᵉ xᵉ (inlᵉ pᵉ) (inrᵉ np'ᵉ) =
    ex-falsoᵉ (np'ᵉ (pr2ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ))))
  is-involution-map-transposition'ᵉ xᵉ (inrᵉ npᵉ) (inlᵉ p'ᵉ) = ex-falsoᵉ (npᵉ p'ᵉ)
  is-involution-map-transposition'ᵉ xᵉ (inrᵉ npᵉ) (inrᵉ np'ᵉ) = reflᵉ

  is-involution-map-transpositionᵉ : is-involutionᵉ map-transpositionᵉ
  is-involution-map-transpositionᵉ xᵉ =
    is-involution-map-transposition'ᵉ xᵉ
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)
      ( is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ
        ( map-transposition'ᵉ xᵉ
          ( is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)))

  is-equiv-map-transpositionᵉ : is-equivᵉ map-transpositionᵉ
  is-equiv-map-transpositionᵉ =
    is-equiv-is-involutionᵉ is-involution-map-transpositionᵉ

  transpositionᵉ : Xᵉ ≃ᵉ Xᵉ
  pr1ᵉ transpositionᵉ = map-transpositionᵉ
  pr2ᵉ transpositionᵉ = is-equiv-map-transpositionᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  is-transposition-permutation-Propᵉ : Xᵉ ≃ᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-transposition-permutation-Propᵉ fᵉ =
    trunc-Propᵉ (fiberᵉ (transpositionᵉ {l2ᵉ = l2ᵉ}) fᵉ)

  is-transposition-permutationᵉ : Xᵉ ≃ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-transposition-permutationᵉ fᵉ =
    type-Propᵉ (is-transposition-permutation-Propᵉ fᵉ)

  is-prop-is-transposition-permutationᵉ :
    (fᵉ : Xᵉ ≃ᵉ Xᵉ) → is-propᵉ (is-transposition-permutationᵉ fᵉ)
  is-prop-is-transposition-permutationᵉ fᵉ =
    is-prop-type-Propᵉ (is-transposition-permutation-Propᵉ fᵉ)
```

### The standard transposition obtained from a pair of distinct points

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : has-decidable-equalityᵉ Xᵉ)
  {xᵉ yᵉ : Xᵉ} (pᵉ : xᵉ ≠ᵉ yᵉ)
  where

  standard-transpositionᵉ : Autᵉ Xᵉ
  standard-transpositionᵉ =
    transpositionᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ)

  map-standard-transpositionᵉ : Xᵉ → Xᵉ
  map-standard-transpositionᵉ = map-equivᵉ standard-transpositionᵉ

  abstract
    left-computation-standard-transpositionᵉ :
      Idᵉ (map-standard-transpositionᵉ xᵉ) yᵉ
    left-computation-standard-transpositionᵉ
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ xᵉ
    ... | inlᵉ ppᵉ =
      apᵉ
        pr1ᵉ
        ( compute-swap-2-Element-Typeᵉ
          ( 2-element-type-standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ)
          ( pairᵉ xᵉ ppᵉ)
          ( pairᵉ yᵉ (inrᵉ reflᵉ))
          ( λ qᵉ → pᵉ (apᵉ pr1ᵉ qᵉ)))
    ... | inrᵉ npᵉ = ex-falsoᵉ (npᵉ (inlᵉ reflᵉ))

  abstract
    right-computation-standard-transpositionᵉ :
      Idᵉ (map-standard-transpositionᵉ yᵉ) xᵉ
    right-computation-standard-transpositionᵉ
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ yᵉ
    ... | inlᵉ ppᵉ =
      apᵉ
        pr1ᵉ
        ( compute-swap-2-Element-Typeᵉ
          ( 2-element-type-standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ)
          ( pairᵉ yᵉ ppᵉ)
          ( pairᵉ xᵉ (inlᵉ reflᵉ))
          ( λ qᵉ → pᵉ (apᵉ pr1ᵉ (invᵉ qᵉ))))
    ... | inrᵉ npᵉ = ex-falsoᵉ (npᵉ (inrᵉ reflᵉ))

  abstract
    is-fixed-point-standard-transpositionᵉ :
      (zᵉ : Xᵉ) → xᵉ ≠ᵉ zᵉ → yᵉ ≠ᵉ zᵉ →
      map-standard-transpositionᵉ zᵉ ＝ᵉ zᵉ
    is-fixed-point-standard-transpositionᵉ zᵉ qᵉ rᵉ
      with is-decidable-type-prop-standard-2-Element-Decidable-Subtypeᵉ Hᵉ pᵉ zᵉ
    ... | inlᵉ (inlᵉ hᵉ) = ex-falsoᵉ (qᵉ hᵉ)
    ... | inlᵉ (inrᵉ hᵉ) = ex-falsoᵉ (rᵉ hᵉ)
    ... | inrᵉ npᵉ = reflᵉ
```

### The permutation obtained from a list of transpositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  where

  permutation-list-transpositionsᵉ :
    ( listᵉ (2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)) → Autᵉ Xᵉ
  permutation-list-transpositionsᵉ =
    fold-listᵉ id-equivᵉ (λ Pᵉ eᵉ → (transpositionᵉ Pᵉ) ∘eᵉ eᵉ)

  --ᵉ !!ᵉ Whyᵉ notᵉ aᵉ homotopy?ᵉ
  eq-concat-permutation-list-transpositionsᵉ :
    (lᵉ l'ᵉ : listᵉ (2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)) →
    Idᵉ
      ( ( permutation-list-transpositionsᵉ lᵉ) ∘eᵉ
        ( permutation-list-transpositionsᵉ l'ᵉ))
      ( permutation-list-transpositionsᵉ (concat-listᵉ lᵉ l'ᵉ))
  eq-concat-permutation-list-transpositionsᵉ nilᵉ l'ᵉ = eq-htpy-equivᵉ refl-htpyᵉ
  eq-concat-permutation-list-transpositionsᵉ (consᵉ Pᵉ lᵉ) l'ᵉ =
    eq-htpy-equivᵉ
      ( λ xᵉ →
        apᵉ
          ( map-equivᵉ (transpositionᵉ Pᵉ))
          ( htpy-eq-equivᵉ (eq-concat-permutation-list-transpositionsᵉ lᵉ l'ᵉ) xᵉ))
```

## Properties

### A transposition is not the identity equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Decidable-Subtypeᵉ l2ᵉ Xᵉ)
  where

  abstract
    is-not-identity-map-transpositionᵉ : Idᵉ (map-transpositionᵉ Pᵉ) idᵉ → emptyᵉ
    is-not-identity-map-transpositionᵉ fᵉ =
      is-not-identity-swap-2-Element-Typeᵉ
        ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
        ( eq-htpy-equivᵉ
          ( λ (xᵉ ,ᵉ pᵉ) →
            eq-pair-Σᵉ
              ( ( apᵉ
                  ( map-transposition'ᵉ Pᵉ xᵉ)
                  ( eq-is-propᵉ
                    ( is-prop-is-decidableᵉ
                      ( is-prop-is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ))
                      { yᵉ =
                        is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ
                          ( Pᵉ)
                          ( xᵉ)})) ∙ᵉ
                ( htpy-eqᵉ fᵉ xᵉ))
              ( eq-is-in-2-Element-Decidable-Subtypeᵉ Pᵉ)))
```

### Any transposition on a type equipped with a counting is a standard transposition

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eXᵉ : countᵉ Xᵉ)
  (Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)
  where

  element-is-not-identity-map-transpositionᵉ :
    Σᵉ Xᵉ (λ xᵉ → map-transpositionᵉ Yᵉ xᵉ ≠ᵉ xᵉ)
  element-is-not-identity-map-transpositionᵉ =
    exists-not-not-for-all-countᵉ
      ( λ zᵉ → Idᵉ (map-transpositionᵉ Yᵉ zᵉ) zᵉ)
      ( λ xᵉ → has-decidable-equality-countᵉ eXᵉ (map-transpositionᵉ Yᵉ xᵉ) xᵉ)
      ( eXᵉ)
      ( λ Hᵉ → is-not-identity-map-transpositionᵉ Yᵉ (eq-htpyᵉ Hᵉ))

  two-elements-transpositionᵉ :
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
                  ( Yᵉ))))
  pr1ᵉ two-elements-transpositionᵉ =
    pr1ᵉ element-is-not-identity-map-transpositionᵉ
  pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ) =
    map-transpositionᵉ Yᵉ (pr1ᵉ element-is-not-identity-map-transpositionᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)) pᵉ =
    pr2ᵉ element-is-not-identity-map-transpositionᵉ (invᵉ pᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)) =
    eq-pair-Σᵉ
      ( eq-htpyᵉ
        ( λ xᵉ → eq-pair-Σᵉ
          ( apᵉ pr1ᵉ
            { xᵉ =
              subtype-standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)))
              ( xᵉ)}
            { yᵉ = subtype-2-Element-Decidable-Subtypeᵉ Yᵉ xᵉ}
            ( eq-iffᵉ
              (type-t-coproduct-idᵉ xᵉ)
              (coproduct-id-type-tᵉ xᵉ)))
          ( eq-pair-Σᵉ
            ( eq-is-propᵉ (is-prop-is-propᵉ (pr1ᵉ (pr1ᵉ Yᵉ xᵉ))))
            ( eq-is-propᵉ (is-prop-is-decidableᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ Yᵉ xᵉ))))))))
      ( eq-is-propᵉ
        ( pr2ᵉ
          ( has-cardinality-Propᵉ 2
            ( Σᵉ Xᵉ (λ xᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))))))
    where
    type-decidable-prop-pr1-two-elements-transpositionᵉ :
      is-in-2-Element-Decidable-Subtypeᵉ Yᵉ (pr1ᵉ two-elements-transpositionᵉ)
    type-decidable-prop-pr1-two-elements-transpositionᵉ =
      cases-type-decidable-prop-pr1-two-elements-transpositionᵉ
        ( is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Yᵉ
          ( pr1ᵉ two-elements-transpositionᵉ))
      where
      cases-type-decidable-prop-pr1-two-elements-transpositionᵉ :
        is-decidableᵉ
          ( is-in-2-Element-Decidable-Subtypeᵉ Yᵉ
            ( pr1ᵉ two-elements-transpositionᵉ)) →
        is-in-2-Element-Decidable-Subtypeᵉ Yᵉ (pr1ᵉ two-elements-transpositionᵉ)
      cases-type-decidable-prop-pr1-two-elements-transpositionᵉ (inlᵉ Qᵉ) = Qᵉ
      cases-type-decidable-prop-pr1-two-elements-transpositionᵉ (inrᵉ NQᵉ) =
        ex-falsoᵉ
          ( pr2ᵉ element-is-not-identity-map-transpositionᵉ
            ( apᵉ
              ( λ Rᵉ →
                map-transposition'ᵉ Yᵉ (pr1ᵉ (two-elements-transpositionᵉ)) Rᵉ)
            { xᵉ =
              is-decidable-subtype-subtype-2-Element-Decidable-Subtypeᵉ Yᵉ
                ( pr1ᵉ two-elements-transpositionᵉ)}
            { yᵉ = inrᵉ NQᵉ}
            ( eq-is-propᵉ
              ( is-prop-is-decidableᵉ
                ( is-prop-is-in-2-Element-Decidable-Subtypeᵉ Yᵉ
                  ( pr1ᵉ two-elements-transpositionᵉ))))))
    type-decidable-prop-pr1-pr2-two-elements-transpositionᵉ :
      is-in-2-Element-Decidable-Subtypeᵉ Yᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
    type-decidable-prop-pr1-pr2-two-elements-transpositionᵉ =
      preserves-subtype-map-transpositionᵉ Yᵉ (pr1ᵉ two-elements-transpositionᵉ)
        ( type-decidable-prop-pr1-two-elements-transpositionᵉ)
    type-t-coproduct-idᵉ :
      (xᵉ : Xᵉ) →
      ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) +ᵉ
      ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ) →
      type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ)
    type-t-coproduct-idᵉ xᵉ (inlᵉ Qᵉ) =
      trᵉ
        ( is-in-2-Element-Decidable-Subtypeᵉ Yᵉ)
        ( Qᵉ)
        ( type-decidable-prop-pr1-two-elements-transpositionᵉ)
    type-t-coproduct-idᵉ xᵉ (inrᵉ Qᵉ) =
      trᵉ
        ( is-in-2-Element-Decidable-Subtypeᵉ Yᵉ)
        ( Qᵉ)
        ( type-decidable-prop-pr1-pr2-two-elements-transpositionᵉ)
    cases-coproduct-id-type-tᵉ :
      (xᵉ : Xᵉ) (pᵉ : is-in-2-Element-Decidable-Subtypeᵉ Yᵉ xᵉ) →
      (hᵉ : Finᵉ 2 ≃ᵉ type-2-Element-Decidable-Subtypeᵉ Yᵉ) →
      (k1ᵉ k2ᵉ k3ᵉ : Finᵉ 2ᵉ) →
      Idᵉ ( map-inv-equivᵉ hᵉ (pairᵉ xᵉ pᵉ)) k1ᵉ →
      Idᵉ
        ( map-inv-equivᵉ hᵉ
          ( pairᵉ
            ( pr1ᵉ two-elements-transpositionᵉ)
            ( type-decidable-prop-pr1-two-elements-transpositionᵉ)))
        ( k2ᵉ) →
      Idᵉ
        ( map-inv-equivᵉ hᵉ
          ( pairᵉ
            ( pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
            ( type-decidable-prop-pr1-pr2-two-elements-transpositionᵉ)))
        ( k3ᵉ) →
      ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) +ᵉ
      ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ)
    cases-coproduct-id-type-tᵉ
      xᵉ pᵉ hᵉ (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) k3ᵉ K1ᵉ K2ᵉ K3ᵉ =
      inlᵉ (apᵉ pr1ᵉ (is-injective-equivᵉ (inv-equivᵉ hᵉ) (K2ᵉ ∙ᵉ invᵉ K1ᵉ)))
    cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ
      (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) K1ᵉ K2ᵉ K3ᵉ =
      inrᵉ (apᵉ pr1ᵉ (is-injective-equivᵉ (inv-equivᵉ hᵉ) (K3ᵉ ∙ᵉ invᵉ K1ᵉ)))
    cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ
      (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) (inrᵉ starᵉ) K1ᵉ K2ᵉ K3ᵉ =
      ex-falsoᵉ
        ( pr2ᵉ element-is-not-identity-map-transpositionᵉ
        ( invᵉ
          ( apᵉ pr1ᵉ
            ( is-injective-equivᵉ (inv-equivᵉ hᵉ) (K2ᵉ ∙ᵉ invᵉ K3ᵉ)))))
    cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ
      (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ)) K1ᵉ K2ᵉ K3ᵉ =
      ex-falsoᵉ
        ( pr2ᵉ element-is-not-identity-map-transpositionᵉ
        ( invᵉ
          ( apᵉ pr1ᵉ
            ( is-injective-equivᵉ (inv-equivᵉ hᵉ) (K2ᵉ ∙ᵉ invᵉ K3ᵉ)))))
    cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ
      (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ) K1ᵉ K2ᵉ K3ᵉ =
      inrᵉ (apᵉ pr1ᵉ (is-injective-equivᵉ (inv-equivᵉ hᵉ) (K3ᵉ ∙ᵉ invᵉ K1ᵉ)))
    cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) k3ᵉ K1ᵉ K2ᵉ K3ᵉ =
      inlᵉ (apᵉ pr1ᵉ (is-injective-equivᵉ (inv-equivᵉ hᵉ) (K2ᵉ ∙ᵉ invᵉ K1ᵉ)))
    coproduct-id-type-tᵉ :
      (xᵉ : Xᵉ) → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ) →
      ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) +ᵉ
      ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ)
    coproduct-id-type-tᵉ xᵉ pᵉ =
      apply-universal-property-trunc-Propᵉ (pr2ᵉ Yᵉ)
        ( coproduct-Propᵉ
          ( Id-Propᵉ
            ( pairᵉ Xᵉ (is-set-countᵉ eXᵉ))
            ( pr1ᵉ two-elements-transpositionᵉ)
            ( xᵉ))
          ( Id-Propᵉ
            ( pairᵉ Xᵉ (is-set-countᵉ eXᵉ))
            ( pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
            ( xᵉ))
          ( λ qᵉ rᵉ →
            pr2ᵉ element-is-not-identity-map-transpositionᵉ (invᵉ (qᵉ ∙ᵉ invᵉ rᵉ))))
        ( λ hᵉ →
          cases-coproduct-id-type-tᵉ xᵉ pᵉ hᵉ
            ( map-inv-equivᵉ hᵉ (pairᵉ xᵉ pᵉ))
            ( map-inv-equivᵉ hᵉ
              ( pairᵉ
                ( pr1ᵉ two-elements-transpositionᵉ)
                ( type-decidable-prop-pr1-two-elements-transpositionᵉ)))
            ( map-inv-equivᵉ hᵉ
              ( pairᵉ
                ( pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
                ( type-decidable-prop-pr1-pr2-two-elements-transpositionᵉ)))
            ( reflᵉ)
            ( reflᵉ)
            ( reflᵉ))

  element-two-elements-transpositionᵉ : Xᵉ
  element-two-elements-transpositionᵉ =
    pr1ᵉ (two-elements-transpositionᵉ)

  other-element-two-elements-transpositionᵉ : Xᵉ
  other-element-two-elements-transpositionᵉ =
    pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)

  neq-elements-two-elements-transpositionᵉ :
    element-two-elements-transpositionᵉ ≠ᵉ
    other-element-two-elements-transpositionᵉ
  neq-elements-two-elements-transpositionᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))

  abstract
    cases-eq-two-elements-transpositionᵉ :
      (xᵉ yᵉ : Xᵉ) (npᵉ : xᵉ ≠ᵉ yᵉ) →
      type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ) →
      type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ two-elements-transpositionᵉ) yᵉ) →
      is-decidableᵉ (Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) yᵉ) →
      ( ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) yᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) yᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ))
    cases-eq-two-elements-transpositionᵉ xᵉ yᵉ npᵉ p1ᵉ p2ᵉ (inlᵉ qᵉ) rᵉ sᵉ (inlᵉ uᵉ) =
      inlᵉ (pairᵉ qᵉ uᵉ)
    cases-eq-two-elements-transpositionᵉ xᵉ yᵉ npᵉ p1ᵉ p2ᵉ (inlᵉ qᵉ) rᵉ sᵉ (inrᵉ nuᵉ) =
      ex-falsoᵉ
        ( contradiction-3-distinct-element-2-Element-Typeᵉ
          ( 2-element-type-2-Element-Decidable-Subtypeᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)))))
          ( pairᵉ (pr1ᵉ two-elements-transpositionᵉ) (inlᵉ reflᵉ))
          ( pairᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) (inrᵉ reflᵉ))
          ( pairᵉ
            ( yᵉ)
            ( trᵉ
              ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
              ( invᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))))
              ( p2ᵉ)))
          ( λ pᵉ →
            pr1ᵉ
              ( pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))
              ( pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → nuᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → npᵉ (invᵉ qᵉ ∙ᵉ pr1ᵉ (pair-eq-Σᵉ pᵉ))))
    cases-eq-two-elements-transpositionᵉ
      xᵉ yᵉ npᵉ p1ᵉ p2ᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inlᵉ sᵉ) uᵉ =
      inrᵉ (pairᵉ sᵉ rᵉ)
    cases-eq-two-elements-transpositionᵉ
      xᵉ yᵉ npᵉ p1ᵉ p2ᵉ (inrᵉ nqᵉ) (inlᵉ rᵉ) (inrᵉ nsᵉ) uᵉ =
      ex-falsoᵉ
        ( contradiction-3-distinct-element-2-Element-Typeᵉ
          ( 2-element-type-2-Element-Decidable-Subtypeᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)))))
          ( pairᵉ (pr1ᵉ two-elements-transpositionᵉ) (inlᵉ reflᵉ))
          ( pairᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) (inrᵉ reflᵉ))
          ( pairᵉ
            ( yᵉ)
            ( trᵉ
              ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ))
              ( invᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))))
              ( p2ᵉ)))
          ( λ pᵉ →
            pr1ᵉ
              ( pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))
              ( pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → npᵉ (invᵉ rᵉ ∙ᵉ pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → nsᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ))))
    cases-eq-two-elements-transpositionᵉ xᵉ yᵉ npᵉ p1ᵉ p2ᵉ (inrᵉ nqᵉ) (inrᵉ nrᵉ) sᵉ uᵉ =
      ex-falsoᵉ
        ( contradiction-3-distinct-element-2-Element-Typeᵉ
          ( 2-element-type-2-Element-Decidable-Subtypeᵉ
            ( standard-2-Element-Decidable-Subtypeᵉ
              ( has-decidable-equality-countᵉ eXᵉ)
              ( pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ)))))
          ( pairᵉ (pr1ᵉ two-elements-transpositionᵉ) (inlᵉ reflᵉ))
          ( pairᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) (inrᵉ reflᵉ))
          ( pairᵉ
            ( xᵉ)
            ( trᵉ
              ( λ Yᵉ → type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ))
              ( invᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))))
              ( p1ᵉ)))
          ( λ pᵉ →
            pr1ᵉ
              ( pr2ᵉ (pr2ᵉ two-elements-transpositionᵉ))
              ( pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → nrᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ)))
          ( λ pᵉ → nqᵉ (pr1ᵉ (pair-eq-Σᵉ pᵉ))))

    eq-two-elements-transpositionᵉ :
      (xᵉ yᵉ : Xᵉ) (npᵉ : xᵉ ≠ᵉ yᵉ) →
      type-Decidable-Propᵉ (pr1ᵉ Yᵉ xᵉ) →
      type-Decidable-Propᵉ (pr1ᵉ Yᵉ yᵉ) →
      ( ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) yᵉ)) +ᵉ
      ( ( Idᵉ (pr1ᵉ two-elements-transpositionᵉ) yᵉ) ×ᵉ
        ( Idᵉ (pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ)) xᵉ))
    eq-two-elements-transpositionᵉ xᵉ yᵉ npᵉ p1ᵉ p2ᵉ =
      cases-eq-two-elements-transpositionᵉ xᵉ yᵉ npᵉ p1ᵉ p2ᵉ
        ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ two-elements-transpositionᵉ) xᵉ)
        ( has-decidable-equality-countᵉ
          ( eXᵉ)
          ( pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
          ( xᵉ))
        ( has-decidable-equality-countᵉ eXᵉ (pr1ᵉ two-elements-transpositionᵉ) yᵉ)
        ( has-decidable-equality-countᵉ
          ( eXᵉ)
          ( pr1ᵉ (pr2ᵉ two-elements-transpositionᵉ))
          ( yᵉ))
```

#### The case of `Fin n`

```agda
module _
  {nᵉ : ℕᵉ}
  (Yᵉ : 2-Element-Decidable-Subtypeᵉ (lzeroᵉ) (Finᵉ nᵉ))
  where

  two-elements-transposition-Finᵉ :
    Σᵉ ( Finᵉ nᵉ)
      ( λ xᵉ →
        Σᵉ ( Finᵉ nᵉ)
          ( λ yᵉ →
            Σᵉ ( xᵉ ≠ᵉ yᵉ)
              ( λ npᵉ →
                Idᵉ
                  ( standard-2-Element-Decidable-Subtypeᵉ
                    ( has-decidable-equality-Finᵉ nᵉ)
                    ( npᵉ))
                  ( Yᵉ))))
  two-elements-transposition-Finᵉ =
    trᵉ
      ( λ pᵉ →
        Σᵉ ( Finᵉ nᵉ)
          ( λ xᵉ →
            Σᵉ ( Finᵉ nᵉ)
              ( λ yᵉ →
                Σᵉ ( xᵉ ≠ᵉ yᵉ)
                  ( λ npᵉ →
                    Idᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ
                        ( pᵉ)
                        ( npᵉ))
                      ( Yᵉ)))))
      ( eq-is-propᵉ (is-prop-has-decidable-equalityᵉ))
      ( two-elements-transpositionᵉ (count-Finᵉ nᵉ) Yᵉ)

  element-two-elements-transposition-Finᵉ : Finᵉ nᵉ
  element-two-elements-transposition-Finᵉ =
    pr1ᵉ (two-elements-transposition-Finᵉ)

  other-element-two-elements-transposition-Finᵉ : Finᵉ nᵉ
  other-element-two-elements-transposition-Finᵉ =
    pr1ᵉ (pr2ᵉ two-elements-transposition-Finᵉ)

  neq-elements-two-elements-transposition-Finᵉ :
    element-two-elements-transposition-Finᵉ ≠ᵉ
    other-element-two-elements-transposition-Finᵉ
  neq-elements-two-elements-transposition-Finᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ two-elements-transposition-Finᵉ))

  eq-standard-2-element-decidable-subtype-two-elements-transposition-Finᵉ :
    standard-2-Element-Decidable-Subtypeᵉ
      ( has-decidable-equality-Finᵉ nᵉ)
      ( neq-elements-two-elements-transposition-Finᵉ) ＝ᵉ
    Yᵉ
  eq-standard-2-element-decidable-subtype-two-elements-transposition-Finᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ two-elements-transposition-Finᵉ))

  htpy-two-elements-transpositon-Finᵉ :
    htpy-equivᵉ
      ( standard-transpositionᵉ
        ( has-decidable-equality-Finᵉ nᵉ)
        ( neq-elements-two-elements-transposition-Finᵉ))
      ( transpositionᵉ Yᵉ)
  htpy-two-elements-transpositon-Finᵉ =
    htpy-eqᵉ
      ( apᵉ
        map-transpositionᵉ
        eq-standard-2-element-decidable-subtype-two-elements-transposition-Finᵉ)
```

### Transpositions can be transported along equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : UUᵉ l2ᵉ) (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  transposition-conjugation-equivᵉ :
    ( Σᵉ
      ( Xᵉ → Decidable-Propᵉ l3ᵉ)
      ( λ Pᵉ →
        has-cardinalityᵉ
          ( 2ᵉ)
          ( Σᵉ Xᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))) →
      ( Σᵉ
        ( Yᵉ → Decidable-Propᵉ (l3ᵉ ⊔ l4ᵉ))
        ( λ Pᵉ →
          has-cardinalityᵉ 2
            ( Σᵉ Yᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
  pr1ᵉ (pr1ᵉ (transposition-conjugation-equivᵉ (pairᵉ Pᵉ Hᵉ)) xᵉ) =
    raiseᵉ l4ᵉ (type-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ)))
  pr1ᵉ (pr2ᵉ (pr1ᵉ (transposition-conjugation-equivᵉ (pairᵉ Pᵉ Hᵉ)) xᵉ)) =
    is-prop-all-elements-equalᵉ
      (λ p1ᵉ p2ᵉ →
        is-injective-equivᵉ
          ( inv-equivᵉ
            ( compute-raiseᵉ l4ᵉ (type-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ)))))
          ( eq-is-propᵉ (is-prop-type-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ)))))
  pr2ᵉ (pr2ᵉ (pr1ᵉ (transposition-conjugation-equivᵉ (pairᵉ Pᵉ Hᵉ)) xᵉ)) =
    is-decidable-raiseᵉ l4ᵉ
      ( type-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ)))
      ( is-decidable-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ)))
  pr2ᵉ (transposition-conjugation-equivᵉ (pairᵉ Pᵉ Hᵉ)) =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ)
      ( has-cardinality-Propᵉ 2
        ( Σᵉ Yᵉ (λ xᵉ → raiseᵉ l4ᵉ (type-Decidable-Propᵉ (Pᵉ (map-inv-equivᵉ eᵉ xᵉ))))))
      λ hᵉ →
      unit-trunc-Propᵉ
        ( pairᵉ
          ( λ xᵉ →
            pairᵉ
              ( map-equivᵉ eᵉ (pr1ᵉ (map-equivᵉ hᵉ xᵉ)))
              ( trᵉ
                ( λ gᵉ →
                  raiseᵉ l4ᵉ
                    ( type-Decidable-Propᵉ
                      ( Pᵉ (map-equivᵉ gᵉ (pr1ᵉ (map-equivᵉ hᵉ xᵉ))))))
                ( invᵉ (left-inverse-law-equivᵉ eᵉ))
                ( map-raiseᵉ (pr2ᵉ (map-equivᵉ hᵉ xᵉ)))))
          ( is-equiv-is-invertibleᵉ
            ( λ (pairᵉ xᵉ pᵉ) →
              map-inv-equivᵉ hᵉ ( pairᵉ (map-inv-equivᵉ eᵉ xᵉ) (map-inv-raiseᵉ pᵉ)))
            ( λ (pairᵉ xᵉ pᵉ) →
              eq-pair-Σᵉ
                ( ( apᵉ
                    ( λ gᵉ →
                      map-equivᵉ
                        ( eᵉ)
                        ( pr1ᵉ
                          ( map-equivᵉ
                            ( gᵉ)
                            ( pairᵉ (map-inv-equivᵉ eᵉ xᵉ) (map-inv-raiseᵉ pᵉ)))))
                    ( right-inverse-law-equivᵉ hᵉ)) ∙ᵉ
                  ( apᵉ (λ gᵉ → map-equivᵉ gᵉ xᵉ) (right-inverse-law-equivᵉ eᵉ)))
                ( eq-is-propᵉ
                  ( pr1ᵉ
                    ( pr2ᵉ
                      ( pr1ᵉ
                        ( transposition-conjugation-equivᵉ (pairᵉ Pᵉ Hᵉ))
                        ( xᵉ))))))
            ( λ bᵉ →
              ( apᵉ
                ( λ wᵉ →
                  map-inv-equivᵉ
                    ( hᵉ)
                    ( pairᵉ (map-equivᵉ (pr1ᵉ wᵉ) (pr1ᵉ (map-equivᵉ hᵉ bᵉ))) (pr2ᵉ wᵉ)))
                { yᵉ = pairᵉ id-equivᵉ (pr2ᵉ (map-equivᵉ hᵉ bᵉ))}
                ( eq-pair-Σᵉ
                  ( left-inverse-law-equivᵉ eᵉ)
                  ( eq-is-propᵉ
                    ( is-prop-type-Decidable-Propᵉ
                      ( Pᵉ (pr1ᵉ (map-equivᵉ hᵉ bᵉ)))))) ∙ᵉ
                ( apᵉ (λ gᵉ → map-equivᵉ gᵉ bᵉ) (left-inverse-law-equivᵉ hᵉ))))))

  abstract
    correct-transposition-conjugation-equivᵉ :
      (tᵉ : Σᵉ
        ( Xᵉ → Decidable-Propᵉ l3ᵉ)
        ( λ Pᵉ → has-cardinalityᵉ 2 (Σᵉ Xᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))) →
      htpy-equivᵉ
        ( transpositionᵉ
          (transposition-conjugation-equivᵉ tᵉ))
        ( (eᵉ ∘eᵉ (transpositionᵉ tᵉ)) ∘eᵉ (inv-equivᵉ eᵉ))
    correct-transposition-conjugation-equivᵉ tᵉ xᵉ =
      cases-correct-transposition-conjugation-equivᵉ
        ( is-decidable-Decidable-Propᵉ (pr1ᵉ tᵉ (map-inv-equivᵉ eᵉ xᵉ)))
      where
      cases-correct-transposition-conjugation-equivᵉ :
        (Qᵉ : is-decidableᵉ (type-Decidable-Propᵉ (pr1ᵉ tᵉ (map-inv-equivᵉ eᵉ xᵉ)))) →
        Idᵉ
          ( map-transposition'ᵉ
            (transposition-conjugation-equivᵉ tᵉ)
            ( xᵉ)
            ( is-decidable-raiseᵉ
              ( l4ᵉ)
              ( type-Decidable-Propᵉ (pr1ᵉ tᵉ (map-inv-equivᵉ eᵉ xᵉ)))
              ( Qᵉ)))
          ( map-equivᵉ eᵉ
            ( map-transposition'ᵉ tᵉ (map-inv-equivᵉ eᵉ xᵉ) Qᵉ))
      cases-correct-transposition-conjugation-equivᵉ (inlᵉ pᵉ) =
        apᵉ
          ( pr1ᵉ)
          ( compute-swap-2-Element-Typeᵉ
            ( pairᵉ
              ( Σᵉ Yᵉ (λ yᵉ → pr1ᵉ (pr1ᵉ (transposition-conjugation-equivᵉ tᵉ) yᵉ)))
              ( pr2ᵉ (transposition-conjugation-equivᵉ tᵉ)))
            ( pairᵉ xᵉ (map-raiseᵉ pᵉ))
            ( pairᵉ
              ( map-equivᵉ eᵉ (pr1ᵉ second-pair-Xᵉ))
              ( map-raiseᵉ
                ( trᵉ
                  ( λ gᵉ →
                    type-Decidable-Propᵉ
                      ( pr1ᵉ tᵉ (map-equivᵉ gᵉ (pr1ᵉ second-pair-Xᵉ))))
                  ( invᵉ (left-inverse-law-equivᵉ eᵉ))
                  ( pr2ᵉ second-pair-Xᵉ))))
            λ qᵉ →
              has-no-fixed-points-swap-2-Element-Typeᵉ
                ( pairᵉ (Σᵉ Xᵉ (λ yᵉ → type-Decidable-Propᵉ (pr1ᵉ tᵉ yᵉ))) (pr2ᵉ tᵉ))
                { pairᵉ (map-inv-equivᵉ eᵉ xᵉ) pᵉ}
                ( eq-pair-Σᵉ
                  ( is-injective-equivᵉ
                    ( eᵉ)
                    ( invᵉ (pr1ᵉ (pair-eq-Σᵉ qᵉ)) ∙ᵉ
                      apᵉ
                        ( λ gᵉ → map-equivᵉ gᵉ xᵉ)
                        ( invᵉ (right-inverse-law-equivᵉ eᵉ))))
                  ( eq-is-propᵉ
                    ( is-prop-type-Decidable-Propᵉ
                      ( pr1ᵉ tᵉ (map-inv-equivᵉ eᵉ xᵉ))))))
        where
        second-pair-Xᵉ : Σᵉ Xᵉ (λ yᵉ → type-Decidable-Propᵉ (pr1ᵉ tᵉ yᵉ))
        second-pair-Xᵉ =
          map-swap-2-Element-Typeᵉ
            (pairᵉ (Σᵉ Xᵉ (λ yᵉ → type-Decidable-Propᵉ (pr1ᵉ tᵉ yᵉ))) (pr2ᵉ tᵉ))
            (pairᵉ (map-inv-equivᵉ eᵉ xᵉ) pᵉ)
      cases-correct-transposition-conjugation-equivᵉ (inrᵉ npᵉ) =
        apᵉ (λ gᵉ → map-equivᵉ gᵉ xᵉ) (invᵉ (right-inverse-law-equivᵉ eᵉ))

    correct-transposition-conjugation-equiv-listᵉ :
      (liᵉ : listᵉ
        ( Σᵉ
          ( Xᵉ → Decidable-Propᵉ l3ᵉ)
          ( λ Pᵉ →
            has-cardinalityᵉ 2 (Σᵉ Xᵉ (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))) →
      htpy-equivᵉ
        ( permutation-list-transpositionsᵉ
          ( map-listᵉ transposition-conjugation-equivᵉ liᵉ))
        ( (eᵉ ∘eᵉ (permutation-list-transpositionsᵉ liᵉ)) ∘eᵉ (inv-equivᵉ eᵉ))
    correct-transposition-conjugation-equiv-listᵉ nilᵉ xᵉ =
      apᵉ (λ gᵉ → map-equivᵉ gᵉ xᵉ) (invᵉ (right-inverse-law-equivᵉ eᵉ))
    correct-transposition-conjugation-equiv-listᵉ (consᵉ tᵉ liᵉ) xᵉ =
      ( correct-transposition-conjugation-equivᵉ
        ( tᵉ)
        (map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( map-listᵉ transposition-conjugation-equivᵉ liᵉ))
          ( xᵉ))) ∙ᵉ
        ( ( apᵉ
          ( map-equivᵉ ((eᵉ ∘eᵉ transpositionᵉ tᵉ) ∘eᵉ inv-equivᵉ eᵉ))
          ( correct-transposition-conjugation-equiv-listᵉ liᵉ xᵉ)) ∙ᵉ
          ( apᵉ
            ( λ gᵉ →
              map-equivᵉ
                ( ( ( (eᵉ ∘eᵉ transpositionᵉ tᵉ) ∘eᵉ gᵉ) ∘eᵉ
                    ( permutation-list-transpositionsᵉ liᵉ)) ∘eᵉ
                  ( inv-equivᵉ eᵉ))
                ( xᵉ))
            ( left-inverse-law-equivᵉ eᵉ)))
```

### For all `n : ℕ` and for each transposition of `Fin n`, there exists a matching transposition in `Fin (succ-ℕ n)`

```agda
Fin-succ-Fin-transpositionᵉ :
  (nᵉ : ℕᵉ) →
  ( Σᵉ
    ( Finᵉ nᵉ → Decidable-Propᵉ lzero)
    ( λ Pᵉ → has-cardinalityᵉ 2 (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))) →
    ( Σᵉ
      ( Finᵉ (succ-ℕᵉ nᵉ) → Decidable-Propᵉ lzero)
      ( λ Pᵉ →
        has-cardinalityᵉ 2
          ( Σᵉ (Finᵉ (succ-ℕᵉ nᵉ)) (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)) (inlᵉ xᵉ) = Pᵉ xᵉ
pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)) (inrᵉ xᵉ) =
  pairᵉ emptyᵉ (pairᵉ is-prop-emptyᵉ is-decidable-emptyᵉ)
pr2ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)) =
  apply-universal-property-trunc-Propᵉ
    ( Hᵉ)
    ( has-cardinality-Propᵉ 2
      ( Σᵉ
        ( Finᵉ (succ-ℕᵉ nᵉ))
        ( type-Decidable-Propᵉ ∘ᵉ pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)))))
    ( λ hᵉ →
      unit-trunc-Propᵉ
        ( ( pairᵉ fᵉ (is-equiv-is-invertibleᵉ inv-fᵉ retraction-fᵉ section-fᵉ)) ∘eᵉ
          ( ( inv-right-unit-law-coproduct-is-emptyᵉ
              ( Σᵉ
                ( Finᵉ nᵉ)
                ( type-Decidable-Propᵉ ∘ᵉ Pᵉ))
              ( Σᵉ unitᵉ (λ _ → emptyᵉ))
              ( map-right-absorption-productᵉ)) ∘eᵉ
            ( hᵉ))))
  where
  fᵉ :
    ( Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)) +ᵉ (Σᵉ unitᵉ (λ _ → emptyᵉ)) →
    Σᵉ ( Finᵉ (succ-ℕᵉ nᵉ))
      ( λ xᵉ →
        type-Decidable-Propᵉ
        (pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)) xᵉ))
  fᵉ (inlᵉ (pairᵉ xᵉ pᵉ)) = pairᵉ (inlᵉ xᵉ) pᵉ
  inv-fᵉ :
    Σᵉ ( Finᵉ (succ-ℕᵉ nᵉ))
      ( λ xᵉ →
        type-Decidable-Propᵉ
        (pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ (pairᵉ Pᵉ Hᵉ)) xᵉ)) →
    (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)) +ᵉ (Σᵉ unitᵉ (λ _ → emptyᵉ))
  inv-fᵉ (pairᵉ (inlᵉ xᵉ) pᵉ) = inlᵉ (pairᵉ xᵉ pᵉ)
  retraction-fᵉ : (fᵉ ∘ᵉ inv-fᵉ) ~ᵉ idᵉ
  retraction-fᵉ (pairᵉ (inlᵉ xᵉ) pᵉ) = reflᵉ
  section-fᵉ : (inv-fᵉ ∘ᵉ fᵉ) ~ᵉ idᵉ
  section-fᵉ (inlᵉ (pairᵉ xᵉ pᵉ)) = reflᵉ

correct-Fin-succ-Fin-transpositionᵉ :
  (nᵉ : ℕᵉ) →
  (tᵉ : Σᵉ
    ( Finᵉ nᵉ → Decidable-Propᵉ lzero)
    ( λ Pᵉ → has-cardinalityᵉ 2 (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))) →
  htpy-equivᵉ
    ( transpositionᵉ (Fin-succ-Fin-transpositionᵉ nᵉ tᵉ))
    ( pr1ᵉ
      ( map-equivᵉ
        ( extend-equiv-Maybeᵉ (Fin-Setᵉ nᵉ))
        ( transpositionᵉ tᵉ)))
correct-Fin-succ-Fin-transpositionᵉ nᵉ tᵉ (inlᵉ xᵉ) with
  is-decidable-Decidable-Propᵉ (pr1ᵉ tᵉ xᵉ)
correct-Fin-succ-Fin-transpositionᵉ nᵉ tᵉ (inlᵉ xᵉ) | inlᵉ pᵉ =
    apᵉ
      ( pr1ᵉ)
      ( compute-swap-2-Element-Typeᵉ
        ( pairᵉ
          ( Σᵉ
            ( Finᵉ (succ-ℕᵉ nᵉ))
            ( type-Decidable-Propᵉ ∘ᵉ pr1ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ tᵉ)))
          ( pr2ᵉ (Fin-succ-Fin-transpositionᵉ nᵉ tᵉ)))
        ( pairᵉ (inlᵉ xᵉ) pᵉ)
        ( pairᵉ
          ( inlᵉ
            ( pr1ᵉ
              ( map-swap-2-Element-Typeᵉ
                ( pairᵉ
                  ( Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ pr1ᵉ tᵉ))
                  ( pr2ᵉ tᵉ))
                ( pairᵉ xᵉ pᵉ))))
          ( pr2ᵉ
            ( map-swap-2-Element-Typeᵉ
              ( pairᵉ
                ( Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ pr1ᵉ tᵉ))
                ( pr2ᵉ tᵉ))
              ( pairᵉ xᵉ pᵉ))))
        ( λ eqᵉ →
          has-no-fixed-points-swap-2-Element-Typeᵉ
            ( pairᵉ (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ pr1ᵉ tᵉ)) (pr2ᵉ tᵉ))
            { pairᵉ xᵉ pᵉ}
            ( eq-pair-Σᵉ
              ( is-injective-inlᵉ (invᵉ (pr1ᵉ (pair-eq-Σᵉ eqᵉ))))
              ( eq-is-propᵉ (is-prop-type-Decidable-Propᵉ (pr1ᵉ tᵉ xᵉ))))))
correct-Fin-succ-Fin-transpositionᵉ nᵉ tᵉ (inlᵉ xᵉ) | inrᵉ npᵉ = reflᵉ
correct-Fin-succ-Fin-transpositionᵉ nᵉ tᵉ (inrᵉ starᵉ) = reflᵉ

correct-Fin-succ-Fin-transposition-listᵉ :
  (nᵉ : ℕᵉ)
  (lᵉ : listᵉ
    ( Σᵉ
      ( Finᵉ nᵉ → Decidable-Propᵉ lzero)
      ( λ Pᵉ →
        has-cardinalityᵉ 2 (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))) →
  htpy-equivᵉ
    ( permutation-list-transpositionsᵉ
      ( map-listᵉ (Fin-succ-Fin-transpositionᵉ nᵉ) lᵉ))
    ( pr1ᵉ
      ( map-equivᵉ
        ( extend-equiv-Maybeᵉ (Fin-Setᵉ nᵉ))
        ( permutation-list-transpositionsᵉ lᵉ)))
correct-Fin-succ-Fin-transposition-listᵉ nᵉ nilᵉ =
  inv-htpyᵉ (id-map-coproductᵉ (Finᵉ nᵉ) unitᵉ)
correct-Fin-succ-Fin-transposition-listᵉ nᵉ (consᵉ tᵉ lᵉ) xᵉ =
  correct-Fin-succ-Fin-transpositionᵉ
    ( nᵉ)
    ( tᵉ)
    ( map-equivᵉ
      ( permutation-list-transpositionsᵉ
        ( map-listᵉ (Fin-succ-Fin-transpositionᵉ nᵉ) lᵉ))
      ( xᵉ)) ∙ᵉ
      ( (apᵉ
        ( map-equivᵉ
          ( pr1ᵉ
            ( map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ nᵉ)) (transpositionᵉ tᵉ))))
        ( correct-Fin-succ-Fin-transposition-listᵉ nᵉ lᵉ xᵉ)) ∙ᵉ
        ( invᵉ
          ( comp-extend-equiv-Maybeᵉ
            ( Fin-Setᵉ nᵉ)
            ( transpositionᵉ tᵉ)
            ( permutation-list-transpositionsᵉ lᵉ)
            ( xᵉ))))
```

```agda
eq-transposition-precomp-standard-2-Element-Decidable-Subtypeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : has-decidable-equalityᵉ Xᵉ) →
  {xᵉ yᵉ : Xᵉ} (npᵉ : xᵉ ≠ᵉ yᵉ) →
  Idᵉ
    ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
      ( standard-transpositionᵉ Hᵉ npᵉ)
      ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ))
    ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ)
eq-transposition-precomp-standard-2-Element-Decidable-Subtypeᵉ
  {lᵉ} {Xᵉ} Hᵉ {xᵉ} {yᵉ} npᵉ =
  eq-pair-Σᵉ
    ( eq-htpyᵉ
      ( λ zᵉ →
        eq-pair-Σᵉ
          ( eq-equivᵉ
            ( equiv-iffᵉ
              ( subtype-standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ
                ( map-inv-equivᵉ (standard-transpositionᵉ Hᵉ npᵉ) zᵉ))
              ( subtype-standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ zᵉ)
              ( fᵉ zᵉ)
              ( gᵉ zᵉ)))
          ( eq-pair-Σᵉ
            ( eq-is-propᵉ
              ( is-prop-is-propᵉ
                ( pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ) zᵉ))))
            ( eq-is-propᵉ
              ( is-prop-is-decidableᵉ
                ( pr1ᵉ
                  ( pr2ᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ)
                      ( zᵉ)))))))))
    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
  where
  fᵉ :
    (zᵉ : Xᵉ) →
    pr1ᵉ
      ( pr1ᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( standard-transpositionᵉ Hᵉ npᵉ)
          ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ)) zᵉ) →
    pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ) zᵉ)
  fᵉ zᵉ (inlᵉ pᵉ) =
    inrᵉ
      ( is-injective-equivᵉ
        ( standard-transpositionᵉ Hᵉ npᵉ)
        ( ( right-computation-standard-transpositionᵉ Hᵉ npᵉ) ∙ᵉ
          ( pᵉ)))
  fᵉ zᵉ (inrᵉ pᵉ) =
    inlᵉ
      ( is-injective-equivᵉ
        ( standard-transpositionᵉ Hᵉ npᵉ)
        ( ( left-computation-standard-transpositionᵉ Hᵉ npᵉ) ∙ᵉ
          ( pᵉ)))
  gᵉ :
    (zᵉ : Xᵉ) →
    pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ) zᵉ) →
    pr1ᵉ
      ( pr1ᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( standard-transpositionᵉ Hᵉ npᵉ)
          ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ npᵉ)) zᵉ)
  gᵉ zᵉ (inlᵉ pᵉ) =
    inrᵉ
      ( ( invᵉ
        ( left-computation-standard-transpositionᵉ Hᵉ npᵉ)) ∙ᵉ
        ( apᵉ (map-standard-transpositionᵉ Hᵉ npᵉ) pᵉ))
  gᵉ zᵉ (inrᵉ pᵉ) =
    inlᵉ
      ( ( invᵉ
        ( right-computation-standard-transpositionᵉ Hᵉ npᵉ)) ∙ᵉ
        ( apᵉ (map-standard-transpositionᵉ Hᵉ npᵉ) pᵉ))

eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtypeᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (Hᵉ : has-decidable-equalityᵉ Xᵉ) →
  {xᵉ yᵉ zᵉ wᵉ : Xᵉ} (npᵉ : xᵉ ≠ᵉ yᵉ) (np'ᵉ : zᵉ ≠ᵉ wᵉ) →
  xᵉ ≠ᵉ zᵉ → xᵉ ≠ᵉ wᵉ → yᵉ ≠ᵉ zᵉ → yᵉ ≠ᵉ wᵉ →
  Idᵉ
    ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
      ( standard-transpositionᵉ Hᵉ npᵉ)
      ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ))
    ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ)
eq-transposition-precomp-ineq-standard-2-Element-Decidable-Subtypeᵉ
  {lᵉ} {Xᵉ} Hᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} npᵉ np'ᵉ nq1ᵉ nq2ᵉ nq3ᵉ nq4ᵉ =
  eq-pair-Σᵉ
    ( eq-htpyᵉ
      ( λ uᵉ →
        eq-pair-Σᵉ
          ( eq-equivᵉ
            ( equiv-iffᵉ
              ( subtype-standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ
                ( map-inv-equivᵉ (standard-transpositionᵉ Hᵉ npᵉ) uᵉ))
              ( subtype-standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ uᵉ)
              ( fᵉ uᵉ)
              ( gᵉ uᵉ)))
          ( eq-pair-Σᵉ
            ( eq-is-propᵉ
              ( is-prop-is-propᵉ
                ( pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ) uᵉ))))
            ( eq-is-propᵉ
              ( is-prop-is-decidableᵉ
                ( pr1ᵉ
                  ( pr2ᵉ
                    ( pr1ᵉ
                      ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ)
                      ( uᵉ)))))))))
    ( eq-is-propᵉ is-prop-type-trunc-Propᵉ)
  where
  fᵉ :
    (uᵉ : Xᵉ) →
    pr1ᵉ
      ( pr1ᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( standard-transpositionᵉ Hᵉ npᵉ)
          ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ)) uᵉ) →
    pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ) uᵉ)
  fᵉ uᵉ (inlᵉ pᵉ) =
    inlᵉ
      ( is-injective-equivᵉ
        ( standard-transpositionᵉ Hᵉ npᵉ)
        ( ( is-fixed-point-standard-transpositionᵉ Hᵉ npᵉ zᵉ nq1ᵉ nq3ᵉ) ∙ᵉ
          ( pᵉ)))
  fᵉ uᵉ (inrᵉ pᵉ) =
    inrᵉ
      ( is-injective-equivᵉ
        ( standard-transpositionᵉ Hᵉ npᵉ)
        ( ( is-fixed-point-standard-transpositionᵉ Hᵉ npᵉ wᵉ nq2ᵉ nq4ᵉ) ∙ᵉ
          ( pᵉ)))
  gᵉ :
    (uᵉ : Xᵉ) →
    pr1ᵉ (pr1ᵉ (standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ) uᵉ) →
    pr1ᵉ
      ( pr1ᵉ
        ( precomp-equiv-2-Element-Decidable-Subtypeᵉ
          ( standard-transpositionᵉ Hᵉ npᵉ)
          ( standard-2-Element-Decidable-Subtypeᵉ Hᵉ np'ᵉ)) uᵉ)
  gᵉ uᵉ (inlᵉ pᵉ) =
    inlᵉ
      ( ( invᵉ
        ( is-fixed-point-standard-transpositionᵉ Hᵉ npᵉ zᵉ nq1ᵉ nq3ᵉ)) ∙ᵉ
        ( apᵉ (map-standard-transpositionᵉ Hᵉ npᵉ) pᵉ))
  gᵉ uᵉ (inrᵉ pᵉ) =
    inrᵉ
      ( ( invᵉ
        ( is-fixed-point-standard-transpositionᵉ Hᵉ npᵉ wᵉ nq2ᵉ nq4ᵉ)) ∙ᵉ
        ( apᵉ (map-standard-transpositionᵉ Hᵉ npᵉ) pᵉ))
```

```agda
module _
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (lᵉ l'ᵉ : Level)
  where

  cases-eq-equiv-universes-transpositionᵉ :
    ( Pᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) (xᵉ : Xᵉ) →
    ( dᵉ : is-decidableᵉ (is-in-2-Element-Decidable-Subtypeᵉ Pᵉ xᵉ)) →
    Idᵉ
      ( map-transposition'ᵉ Pᵉ xᵉ dᵉ)
      ( map-transpositionᵉ
        ( map-equivᵉ (equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ) Pᵉ)
        ( xᵉ))
  cases-eq-equiv-universes-transpositionᵉ Pᵉ xᵉ (inlᵉ pᵉ) =
    ( apᵉ pr1ᵉ
      ( invᵉ
        ( compute-swap-2-Element-Decidable-Subtypeᵉ
          ( map-equivᵉ (equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ) Pᵉ)
          ( pairᵉ xᵉ (pr1ᵉ (iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ (pr1ᵉ Pᵉ) xᵉ) pᵉ))
          ( pairᵉ
            ( pr1ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ)))
            ( pr1ᵉ
              ( iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ (pr1ᵉ Pᵉ)
                ( pr1ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ))))
              ( pr2ᵉ (map-swap-2-Element-Decidable-Subtypeᵉ Pᵉ (pairᵉ xᵉ pᵉ)))))
          ( λ qᵉ →
            has-no-fixed-points-swap-2-Element-Typeᵉ
              ( 2-element-type-2-Element-Decidable-Subtypeᵉ Pᵉ)
              ( eq-pair-Σᵉ
                ( pr1ᵉ (pair-eq-Σᵉ (invᵉ qᵉ)))
                ( eq-is-propᵉ (is-prop-type-Decidable-Propᵉ (pr1ᵉ Pᵉ xᵉ)))))))) ∙ᵉ
      apᵉ
      ( λ d'ᵉ →
        map-transposition'ᵉ
          ( map-equivᵉ
            ( equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ)
            ( Pᵉ))
          ( xᵉ)
          ( d'ᵉ))
      { xᵉ = inlᵉ (pr1ᵉ (iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ (pr1ᵉ Pᵉ) xᵉ) pᵉ)}
      { yᵉ =
        is-decidable-Decidable-Propᵉ
          ( map-equivᵉ (equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ) (pr1ᵉ Pᵉ) xᵉ)}
      ( eq-is-propᵉ
        ( is-prop-is-decidableᵉ
          ( is-prop-type-Decidable-Propᵉ
            (map-equivᵉ (equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ) (pr1ᵉ Pᵉ) xᵉ))))
  cases-eq-equiv-universes-transpositionᵉ Pᵉ xᵉ (inrᵉ npᵉ) =
    apᵉ
      ( λ d'ᵉ →
        map-transposition'ᵉ
          ( map-equivᵉ
            ( equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ)
            ( Pᵉ))
          ( xᵉ)
          ( d'ᵉ))
      { xᵉ = inrᵉ (npᵉ ∘ᵉ pr2ᵉ (iff-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ (pr1ᵉ Pᵉ) xᵉ))}
      { yᵉ =
        is-decidable-Decidable-Propᵉ
          ( map-equivᵉ (equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ) (pr1ᵉ Pᵉ) xᵉ)}
      ( eq-is-propᵉ
        ( is-prop-is-decidableᵉ
          ( is-prop-type-Decidable-Propᵉ
            (map-equivᵉ (equiv-universes-decidable-subtypeᵉ Xᵉ lᵉ l'ᵉ) (pr1ᵉ Pᵉ) xᵉ))))

  eq-equiv-universes-transpositionᵉ :
    ( Pᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ) →
    Idᵉ
      ( transpositionᵉ Pᵉ)
      ( transpositionᵉ
        ( map-equivᵉ (equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ) Pᵉ))
  eq-equiv-universes-transpositionᵉ Pᵉ =
    eq-htpy-equivᵉ
      ( λ xᵉ →
        cases-eq-equiv-universes-transpositionᵉ Pᵉ xᵉ
          ( is-decidable-Decidable-Propᵉ (pr1ᵉ Pᵉ xᵉ)))

  eq-equiv-universes-transposition-listᵉ :
    ( liᵉ : listᵉ (2-Element-Decidable-Subtypeᵉ lᵉ Xᵉ)) →
    Idᵉ
      ( permutation-list-transpositionsᵉ liᵉ)
      ( permutation-list-transpositionsᵉ
        ( map-listᵉ
          ( map-equivᵉ (equiv-universes-2-Element-Decidable-Subtypeᵉ Xᵉ lᵉ l'ᵉ))
          ( liᵉ)))
  eq-equiv-universes-transposition-listᵉ nilᵉ = reflᵉ
  eq-equiv-universes-transposition-listᵉ (consᵉ Pᵉ liᵉ) =
    ap-binaryᵉ
      ( _∘eᵉ_)
      ( eq-equiv-universes-transpositionᵉ Pᵉ)
      ( eq-equiv-universes-transposition-listᵉ liᵉ)
```

### Conjugate of a transposition is also a transposition

```agda
module _
  {l1ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ}
  (Hᵉ : has-decidable-equalityᵉ Xᵉ)
  {xᵉ yᵉ zᵉ : Xᵉ}
  (npxyᵉ : xᵉ ≠ᵉ yᵉ)
  (npyzᵉ : yᵉ ≠ᵉ zᵉ)
  (npxzᵉ : xᵉ ≠ᵉ zᵉ)
  where

  cases-htpy-conjugate-transpositionᵉ :
    (wᵉ : Xᵉ) →
    ( is-decidableᵉ (wᵉ ＝ᵉ xᵉ)) →
    ( is-decidableᵉ (wᵉ ＝ᵉ yᵉ)) →
    ( is-decidableᵉ (wᵉ ＝ᵉ zᵉ)) →
    Idᵉ
      ( map-equivᵉ
        ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ
          ( standard-transpositionᵉ Hᵉ npxyᵉ ∘eᵉ standard-transpositionᵉ Hᵉ npyzᵉ))
        wᵉ)
      ( map-equivᵉ ( standard-transpositionᵉ Hᵉ npxzᵉ) wᵉ)
  cases-htpy-conjugate-transpositionᵉ xᵉ (inlᵉ reflᵉ) _ _ =
    ( ( apᵉ
        ( λ wᵉ →
          map-equivᵉ
            ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ standard-transpositionᵉ Hᵉ npxyᵉ)
            ( wᵉ))
        ( is-fixed-point-standard-transpositionᵉ
          ( Hᵉ)
          ( npyzᵉ)
          ( xᵉ)
          ( npxyᵉ ∘ᵉ invᵉ)
          ( npxzᵉ ∘ᵉ invᵉ))) ∙ᵉ
      ( ( apᵉ
          ( λ wᵉ → map-equivᵉ (standard-transpositionᵉ Hᵉ npyzᵉ) wᵉ)
          ( left-computation-standard-transpositionᵉ Hᵉ npxyᵉ)) ∙ᵉ
        ( ( left-computation-standard-transpositionᵉ Hᵉ npyzᵉ) ∙ᵉ
          ( ( invᵉ (left-computation-standard-transpositionᵉ Hᵉ npxzᵉ))))))
  cases-htpy-conjugate-transpositionᵉ yᵉ (inrᵉ neqxᵉ) (inlᵉ reflᵉ) _ =
    ( ( apᵉ
        ( λ wᵉ →
          map-equivᵉ
            ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ standard-transpositionᵉ Hᵉ npxyᵉ)
            ( wᵉ))
        ( left-computation-standard-transpositionᵉ Hᵉ npyzᵉ)) ∙ᵉ
      ( ( apᵉ
          ( λ wᵉ → map-equivᵉ (standard-transpositionᵉ Hᵉ npyzᵉ) wᵉ)
          ( is-fixed-point-standard-transpositionᵉ Hᵉ npxyᵉ zᵉ npxzᵉ npyzᵉ)) ∙ᵉ
        ( ( right-computation-standard-transpositionᵉ Hᵉ npyzᵉ) ∙ᵉ
          ( invᵉ
            ( is-fixed-point-standard-transpositionᵉ
              ( Hᵉ)
              ( npxzᵉ)
              ( yᵉ)
              ( npxyᵉ)
              ( npyzᵉ ∘ᵉ invᵉ))))))
  cases-htpy-conjugate-transpositionᵉ zᵉ (inrᵉ neqxᵉ) (inrᵉ neqyᵉ) (inlᵉ reflᵉ) =
    ( ( apᵉ
        ( λ wᵉ →
          map-equivᵉ
            ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ standard-transpositionᵉ Hᵉ npxyᵉ)
            ( wᵉ))
        ( right-computation-standard-transpositionᵉ Hᵉ npyzᵉ)) ∙ᵉ
      ( ( apᵉ
          ( λ wᵉ → map-equivᵉ (standard-transpositionᵉ Hᵉ npyzᵉ) wᵉ)
          ( right-computation-standard-transpositionᵉ Hᵉ npxyᵉ)) ∙ᵉ
        ( ( is-fixed-point-standard-transpositionᵉ
            ( Hᵉ)
            ( npyzᵉ)
            ( xᵉ)
            ( npxyᵉ ∘ᵉ invᵉ)
            ( npxzᵉ ∘ᵉ invᵉ)) ∙ᵉ
          ( invᵉ (right-computation-standard-transpositionᵉ Hᵉ npxzᵉ)))))
  cases-htpy-conjugate-transpositionᵉ wᵉ (inrᵉ neqxᵉ) (inrᵉ neqyᵉ) (inrᵉ neqzᵉ) =
    ( ( apᵉ
        ( λ wᵉ →
          map-equivᵉ
            ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ standard-transpositionᵉ Hᵉ npxyᵉ)
            ( wᵉ))
        ( is-fixed-point-standard-transpositionᵉ
          ( Hᵉ)
          ( npyzᵉ)
          ( wᵉ)
          ( neqyᵉ ∘ᵉ invᵉ)
          ( neqzᵉ ∘ᵉ invᵉ))) ∙ᵉ
      ( ( apᵉ
          ( λ wᵉ → map-equivᵉ (standard-transpositionᵉ Hᵉ npyzᵉ) wᵉ)
          ( is-fixed-point-standard-transpositionᵉ
            ( Hᵉ)
            ( npxyᵉ)
            ( wᵉ)
            ( neqxᵉ ∘ᵉ invᵉ)
            ( neqyᵉ ∘ᵉ invᵉ))) ∙ᵉ
        ( ( is-fixed-point-standard-transpositionᵉ
            ( Hᵉ)
            ( npyzᵉ)
            ( wᵉ)
            ( neqyᵉ ∘ᵉ invᵉ)
            ( neqzᵉ ∘ᵉ invᵉ)) ∙ᵉ
          ( invᵉ
            ( is-fixed-point-standard-transpositionᵉ
              ( Hᵉ)
              ( npxzᵉ)
              ( wᵉ)
              ( neqxᵉ ∘ᵉ invᵉ)
              ( neqzᵉ ∘ᵉ invᵉ))))))

  htpy-conjugate-transpositionᵉ :
    htpy-equivᵉ
      ( standard-transpositionᵉ Hᵉ npyzᵉ ∘eᵉ
        ( standard-transpositionᵉ Hᵉ npxyᵉ ∘eᵉ
          standard-transpositionᵉ Hᵉ npyzᵉ))
      ( standard-transpositionᵉ Hᵉ npxzᵉ)
  htpy-conjugate-transpositionᵉ wᵉ =
    cases-htpy-conjugate-transpositionᵉ wᵉ ( Hᵉ wᵉ xᵉ) ( Hᵉ wᵉ yᵉ) ( Hᵉ wᵉ zᵉ)
```