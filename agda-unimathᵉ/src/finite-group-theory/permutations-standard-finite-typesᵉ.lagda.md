# Permutations of standard finite types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.permutations-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import lists.functoriality-listsᵉ
open import lists.listsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ permutationᵉ ofᵉ `Finᵉ n`ᵉ isᵉ anᵉ automorphismᵉ ofᵉ `Finᵉ n`.ᵉ

## Definitions

```agda
Permutationᵉ : (nᵉ : ℕᵉ) → UUᵉ lzero
Permutationᵉ nᵉ = Autᵉ (Finᵉ nᵉ)
```

## Properties

### Every permutation on `Fin n` can be described as a composite of transpositions

```agda
list-transpositions-permutation-Fin'ᵉ :
  (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ (succ-ℕᵉ nᵉ)) →
  (xᵉ : Finᵉ (succ-ℕᵉ nᵉ)) → Idᵉ (map-equivᵉ fᵉ (inrᵉ starᵉ)) xᵉ →
  ( listᵉ
    ( Σᵉ
      ( Finᵉ (succ-ℕᵉ nᵉ) → Decidable-Propᵉ lzero)
      ( λ Pᵉ →
        has-cardinalityᵉ 2
          ( Σᵉ (Finᵉ (succ-ℕᵉ nᵉ)) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))))
list-transpositions-permutation-Fin'ᵉ zero-ℕᵉ fᵉ xᵉ pᵉ = nilᵉ
list-transpositions-permutation-Fin'ᵉ (succ-ℕᵉ nᵉ) fᵉ (inlᵉ xᵉ) pᵉ =
  consᵉ
    ( tᵉ)
    ( map-listᵉ
      ( Fin-succ-Fin-transpositionᵉ (succ-ℕᵉ nᵉ))
      ( list-transpositions-permutation-Fin'ᵉ
        ( nᵉ)
        ( f'ᵉ)
        ( map-equivᵉ f'ᵉ (inrᵉ starᵉ))
        ( reflᵉ)))
  where
  tᵉ :
    Σᵉ ( Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → Decidable-Propᵉ lzero)
      ( λ Pᵉ →
        has-cardinalityᵉ 2
          ( Σᵉ (Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
  tᵉ = standard-2-Element-Decidable-Subtypeᵉ
      ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
      { inrᵉ starᵉ}
      { inlᵉ xᵉ}
      ( neq-inr-inlᵉ)
  f'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
  f'ᵉ =
    map-inv-equivᵉ
      ( extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ)))
      ( pairᵉ
        ( transpositionᵉ tᵉ ∘eᵉ fᵉ)
        ( ( apᵉ (λ yᵉ → map-transpositionᵉ tᵉ yᵉ) pᵉ) ∙ᵉ
          ( right-computation-standard-transpositionᵉ
            ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            { inrᵉ starᵉ}
            { inlᵉ xᵉ}
            ( neq-inr-inlᵉ))))
list-transpositions-permutation-Fin'ᵉ (succ-ℕᵉ nᵉ) fᵉ (inrᵉ starᵉ) pᵉ =
  map-listᵉ
    ( Fin-succ-Fin-transpositionᵉ (succ-ℕᵉ nᵉ))
    ( list-transpositions-permutation-Fin'ᵉ nᵉ f'ᵉ (map-equivᵉ f'ᵉ (inrᵉ starᵉ)) reflᵉ)
  where
  f'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
  f'ᵉ = map-inv-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) (pairᵉ fᵉ pᵉ)

list-transpositions-permutation-Finᵉ :
  (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ nᵉ) →
  ( listᵉ
    ( Σᵉ
      ( Finᵉ nᵉ → Decidable-Propᵉ lzero)
      ( λ Pᵉ → has-cardinalityᵉ 2 (Σᵉ (Finᵉ nᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))))
list-transpositions-permutation-Finᵉ zero-ℕᵉ fᵉ = nilᵉ
list-transpositions-permutation-Finᵉ (succ-ℕᵉ nᵉ) fᵉ =
  list-transpositions-permutation-Fin'ᵉ nᵉ fᵉ (map-equivᵉ fᵉ (inrᵉ starᵉ)) reflᵉ

abstract
  retraction-permutation-list-transpositions-Fin'ᵉ :
    (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ (succ-ℕᵉ nᵉ)) →
    (xᵉ : Finᵉ (succ-ℕᵉ nᵉ)) → Idᵉ (map-equivᵉ fᵉ (inrᵉ starᵉ)) xᵉ →
    (yᵉ zᵉ : Finᵉ (succ-ℕᵉ nᵉ)) → Idᵉ (map-equivᵉ fᵉ yᵉ) zᵉ →
    Idᵉ
      ( map-equivᵉ
        ( permutation-list-transpositionsᵉ
          ( list-transpositions-permutation-Finᵉ (succ-ℕᵉ nᵉ) fᵉ))
        ( yᵉ))
      ( map-equivᵉ fᵉ yᵉ)
  retraction-permutation-list-transpositions-Fin'ᵉ
    zero-ℕᵉ fᵉ (inrᵉ starᵉ) pᵉ (inrᵉ starᵉ) zᵉ qᵉ =
    invᵉ pᵉ
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inlᵉ xᵉ) pᵉ (inlᵉ yᵉ) (inlᵉ zᵉ) qᵉ =
    apᵉ
      (λ wᵉ →
        map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( list-transpositions-permutation-Fin'ᵉ
              (succ-ℕᵉ nᵉ) fᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)))
        ( inlᵉ yᵉ)) {yᵉ = pairᵉ (inlᵉ xᵉ) pᵉ}
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ
          ( is-set-type-Setᵉ
            ( Fin-Setᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            ( map-equivᵉ fᵉ (inrᵉ starᵉ))
            ( inlᵉ xᵉ)))) ∙ᵉ
      ( apᵉ
        ( map-equivᵉ (transpositionᵉ tᵉ))
        ( correct-Fin-succ-Fin-transposition-listᵉ
          ( succ-ℕᵉ nᵉ)
          ( list-transpositions-permutation-Fin'ᵉ
              nᵉ _ (map-equivᵉ F'ᵉ (inrᵉ starᵉ)) reflᵉ)
          ( inlᵉ yᵉ)) ∙ᵉ
        (apᵉ
          ( λ gᵉ →
            map-equivᵉ
              ( transpositionᵉ tᵉ)
              ( map-equivᵉ
                ( pr1ᵉ (map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) gᵉ))
                ( inlᵉ yᵉ)))
          { xᵉ =
            permutation-list-transpositionsᵉ
              ( list-transpositions-permutation-Finᵉ (succ-ℕᵉ nᵉ) _)}
          { yᵉ = F'ᵉ}
          ( eq-htpy-equivᵉ
            ( λ wᵉ → retraction-permutation-list-transpositions-Fin'ᵉ
              nᵉ _ (map-equivᵉ F'ᵉ (inrᵉ starᵉ)) reflᵉ wᵉ (map-equivᵉ F'ᵉ wᵉ) reflᵉ)) ∙ᵉ
            ( (apᵉ (map-equivᵉ (transpositionᵉ tᵉ)) lemmaᵉ) ∙ᵉ
              (lemma2ᵉ ∙ᵉ invᵉ qᵉ))))
    where
    tᵉ :
      Σᵉ ( Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → Decidable-Propᵉ lzero)
        ( λ Pᵉ →
          has-cardinalityᵉ 2
            ( Σᵉ (Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
    tᵉ =
      standard-2-Element-Decidable-Subtypeᵉ
        ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        { inrᵉ starᵉ}
        { inlᵉ xᵉ}
        ( neq-inr-inlᵉ)
    Pᵉ :
      Σᵉ ( Permutationᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        ( λ gᵉ → Idᵉ (map-equivᵉ gᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ))
    Pᵉ =
      pairᵉ
        ( transpositionᵉ tᵉ ∘eᵉ fᵉ)
        ( ( apᵉ (λ yᵉ → map-transpositionᵉ tᵉ yᵉ) pᵉ) ∙ᵉ
          ( right-computation-standard-transpositionᵉ
            ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            { inrᵉ starᵉ}
            { inlᵉ xᵉ}
            ( neq-inr-inlᵉ)))
    F'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
    F'ᵉ = map-inv-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) Pᵉ
    lemma2ᵉ : (map-equivᵉ (transpositionᵉ tᵉ) (inlᵉ zᵉ)) ＝ᵉ (inlᵉ zᵉ)
    lemma2ᵉ =
      is-fixed-point-standard-transpositionᵉ
        ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        { inrᵉ starᵉ}
        { inlᵉ xᵉ}
        ( neq-inr-inlᵉ)
        ( inlᵉ zᵉ)
        ( neq-inr-inlᵉ)
        ( λ rᵉ →
          neq-inr-inlᵉ
            ( is-injective-equivᵉ fᵉ (pᵉ ∙ᵉ (rᵉ ∙ᵉ invᵉ qᵉ))))
    lemmaᵉ :
      Idᵉ
        ( map-equivᵉ
          ( pr1ᵉ (map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) F'ᵉ))
          ( inlᵉ yᵉ))
        ( inlᵉ zᵉ)
    lemmaᵉ =
      ( apᵉ
        ( λ eᵉ → map-equivᵉ (pr1ᵉ (map-equivᵉ eᵉ Pᵉ)) (inlᵉ yᵉ))
        ( right-inverse-law-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
      ( apᵉ (map-equivᵉ (transpositionᵉ tᵉ)) qᵉ ∙ᵉ lemma2ᵉ)
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inlᵉ xᵉ) pᵉ (inlᵉ yᵉ) (inrᵉ starᵉ) qᵉ =
    apᵉ
      (λ wᵉ →
        map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( list-transpositions-permutation-Fin'ᵉ
              (succ-ℕᵉ nᵉ) fᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)))
        ( inlᵉ yᵉ)) {yᵉ = pairᵉ (inlᵉ xᵉ) pᵉ}
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ
          ( is-set-type-Setᵉ
            ( Fin-Setᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            ( map-equivᵉ fᵉ (inrᵉ starᵉ))
            ( inlᵉ xᵉ)))) ∙ᵉ
      ( apᵉ
        ( map-equivᵉ (transpositionᵉ tᵉ))
        ( correct-Fin-succ-Fin-transposition-listᵉ
          ( succ-ℕᵉ nᵉ)
          ( list-transpositions-permutation-Fin'ᵉ
              nᵉ _ (map-equivᵉ F'ᵉ (inrᵉ starᵉ)) reflᵉ)
          ( inlᵉ yᵉ)) ∙ᵉ
        (apᵉ
          ( λ gᵉ →
            map-equivᵉ
              ( transpositionᵉ tᵉ)
              ( map-equivᵉ
                ( pr1ᵉ (map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) gᵉ))
                ( inlᵉ yᵉ)))
          { xᵉ =
            permutation-list-transpositionsᵉ
              ( list-transpositions-permutation-Finᵉ (succ-ℕᵉ nᵉ) _)}
          { yᵉ = F'ᵉ}
          ( eq-htpy-equivᵉ
            ( λ wᵉ →
              retraction-permutation-list-transpositions-Fin'ᵉ
                nᵉ _ (map-equivᵉ F'ᵉ (inrᵉ starᵉ)) reflᵉ wᵉ (map-equivᵉ F'ᵉ wᵉ) reflᵉ)) ∙ᵉ
          ( ( apᵉ (map-equivᵉ (transpositionᵉ tᵉ)) lemmaᵉ) ∙ᵉ
            ( ( right-computation-standard-transpositionᵉ
                ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                { inrᵉ starᵉ}
                { inlᵉ xᵉ}
                ( neq-inr-inlᵉ)) ∙ᵉ
              ( invᵉ qᵉ)))))
    where
    tᵉ :
      Σᵉ ( Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → Decidable-Propᵉ lzero)
        ( λ Pᵉ →
          has-cardinalityᵉ 2
            ( Σᵉ (Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
    tᵉ =
      standard-2-Element-Decidable-Subtypeᵉ
        ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        { inrᵉ starᵉ}
        { inlᵉ xᵉ}
        ( neq-inr-inlᵉ)
    Pᵉ :
      Σᵉ ( Permutationᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        ( λ gᵉ → Idᵉ (map-equivᵉ gᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ))
    Pᵉ = pairᵉ
      ( transpositionᵉ tᵉ ∘eᵉ fᵉ)
      ( ( apᵉ (map-transpositionᵉ tᵉ) pᵉ) ∙ᵉ
        right-computation-standard-transpositionᵉ
          ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
          { inrᵉ starᵉ}
          { inlᵉ xᵉ}
          ( neq-inr-inlᵉ))
    F'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
    F'ᵉ = map-inv-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) Pᵉ
    lemmaᵉ :
      Idᵉ
        ( map-equivᵉ
          ( pr1ᵉ
            ( map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) F'ᵉ))
          ( inlᵉ yᵉ))
        (inlᵉ xᵉ)
    lemmaᵉ =
      ( apᵉ
        ( λ eᵉ → map-equivᵉ (pr1ᵉ (map-equivᵉ eᵉ Pᵉ)) (inlᵉ yᵉ))
        ( right-inverse-law-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
      ( apᵉ
        ( map-equivᵉ (transpositionᵉ tᵉ))
        ( qᵉ) ∙ᵉ
        ( left-computation-standard-transpositionᵉ
          ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
          { inrᵉ starᵉ}
          { inlᵉ xᵉ}
          ( neq-inr-inlᵉ)))
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inlᵉ xᵉ) pᵉ (inrᵉ starᵉ) zᵉ qᵉ =
    apᵉ
      (λ wᵉ →
        map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( list-transpositions-permutation-Fin'ᵉ
              (succ-ℕᵉ nᵉ) fᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)))
        ( inrᵉ starᵉ)) {yᵉ = pairᵉ (inlᵉ xᵉ) pᵉ}
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ
          ( is-set-type-Setᵉ
            ( Fin-Setᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            ( map-equivᵉ fᵉ (inrᵉ starᵉ))
            ( inlᵉ xᵉ)))) ∙ᵉ
      ( apᵉ
        ( map-equivᵉ (transpositionᵉ tᵉ))
        ( correct-Fin-succ-Fin-transposition-listᵉ
          ( succ-ℕᵉ nᵉ)
          ( list-transpositions-permutation-Fin'ᵉ
              nᵉ _ (map-equivᵉ F'ᵉ (inrᵉ starᵉ)) reflᵉ)
          ( inrᵉ starᵉ)) ∙ᵉ
        ( apᵉ
          ( map-equivᵉ (transpositionᵉ tᵉ))
          ( pr2ᵉ (map-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) F'ᵉ)) ∙ᵉ
          ( ( left-computation-standard-transpositionᵉ
              ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
              { inrᵉ starᵉ}
              { inlᵉ xᵉ}
              ( neq-inr-inlᵉ)) ∙ᵉ
            ( invᵉ pᵉ))))
    where
    tᵉ :
      Σᵉ ( Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → Decidable-Propᵉ lzero)
        ( λ Pᵉ →
          has-cardinalityᵉ 2
            ( Σᵉ (Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) (type-Decidable-Propᵉ ∘ᵉ Pᵉ)))
    tᵉ =
      standard-2-Element-Decidable-Subtypeᵉ
        ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        { inrᵉ starᵉ}
        { inlᵉ xᵉ}
        ( neq-inr-inlᵉ)
    F'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
    F'ᵉ =
      map-inv-equivᵉ
        ( extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ)))
        ( pairᵉ
          ( transpositionᵉ tᵉ ∘eᵉ fᵉ)
          ( ( apᵉ (map-transpositionᵉ tᵉ) pᵉ) ∙ᵉ
            right-computation-standard-transpositionᵉ
              ( has-decidable-equality-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
              { inrᵉ starᵉ}
              { inlᵉ xᵉ}
              ( neq-inr-inlᵉ)))
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inrᵉ starᵉ) pᵉ (inlᵉ yᵉ) (inlᵉ zᵉ) qᵉ =
    apᵉ
      ( λ wᵉ →
        map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( list-transpositions-permutation-Fin'ᵉ
              (succ-ℕᵉ nᵉ) fᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)))
        ( inlᵉ yᵉ))
      {yᵉ = pairᵉ (inrᵉ starᵉ) pᵉ}
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ
          ( is-set-type-Setᵉ
            ( Fin-Setᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            ( map-equivᵉ fᵉ (inrᵉ starᵉ))
            ( inrᵉ starᵉ)))) ∙ᵉ
      ( ( correct-Fin-succ-Fin-transposition-listᵉ
          ( succ-ℕᵉ nᵉ)
          ( list-transpositions-permutation-Fin'ᵉ
              nᵉ f'ᵉ (map-equivᵉ f'ᵉ (inrᵉ starᵉ)) reflᵉ)
          ( inlᵉ yᵉ)) ∙ᵉ
        ( ( apᵉ
            ( inlᵉ)
            ( retraction-permutation-list-transpositions-Fin'ᵉ
              nᵉ f'ᵉ (map-equivᵉ f'ᵉ (inrᵉ starᵉ)) reflᵉ yᵉ (map-equivᵉ f'ᵉ yᵉ) reflᵉ)) ∙ᵉ
          ( computation-inv-extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ)) fᵉ pᵉ yᵉ)))
    where
    f'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
    f'ᵉ = map-inv-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) (pairᵉ fᵉ pᵉ)
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inrᵉ starᵉ) pᵉ (inlᵉ yᵉ) (inrᵉ starᵉ) qᵉ =
    ex-falsoᵉ
      ( neq-inr-inlᵉ
        ( is-injective-equivᵉ fᵉ (pᵉ ∙ᵉ invᵉ qᵉ)))
  retraction-permutation-list-transpositions-Fin'ᵉ
    (succ-ℕᵉ nᵉ) fᵉ (inrᵉ starᵉ) pᵉ (inrᵉ starᵉ) zᵉ qᵉ =
    apᵉ
      (λ wᵉ →
        map-equivᵉ
          ( permutation-list-transpositionsᵉ
            ( list-transpositions-permutation-Fin'ᵉ
              (succ-ℕᵉ nᵉ) fᵉ (pr1ᵉ wᵉ) (pr2ᵉ wᵉ)))
        ( inrᵉ starᵉ)) {yᵉ = pairᵉ (inrᵉ starᵉ) pᵉ}
      ( eq-pair-Σᵉ
        ( pᵉ)
        ( eq-is-propᵉ
          ( is-set-type-Setᵉ
            ( Fin-Setᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
            ( map-equivᵉ fᵉ (inrᵉ starᵉ))
            ( inrᵉ starᵉ)))) ∙ᵉ
      ( ( correct-Fin-succ-Fin-transposition-listᵉ
          ( succ-ℕᵉ nᵉ)
          ( list-transpositions-permutation-Fin'ᵉ
              nᵉ f'ᵉ (map-equivᵉ f'ᵉ (inrᵉ starᵉ)) reflᵉ)
          ( inrᵉ starᵉ)) ∙ᵉ
        ( invᵉ pᵉ))
    where
    f'ᵉ : (Permutationᵉ (succ-ℕᵉ nᵉ))
    f'ᵉ = map-inv-equivᵉ (extend-equiv-Maybeᵉ (Fin-Setᵉ (succ-ℕᵉ nᵉ))) (pairᵉ fᵉ pᵉ)

  retraction-permutation-list-transpositions-Finᵉ :
    (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ nᵉ) →
    htpy-equivᵉ
      ( permutation-list-transpositionsᵉ
        ( list-transpositions-permutation-Finᵉ nᵉ fᵉ))
      ( fᵉ)
  retraction-permutation-list-transpositions-Finᵉ zero-ℕᵉ fᵉ ()
  retraction-permutation-list-transpositions-Finᵉ (succ-ℕᵉ nᵉ) fᵉ yᵉ =
    retraction-permutation-list-transpositions-Fin'ᵉ
      nᵉ fᵉ (map-equivᵉ fᵉ (inrᵉ starᵉ)) reflᵉ yᵉ (map-equivᵉ fᵉ yᵉ) reflᵉ
```

```agda
permutation-list-standard-transpositions-Finᵉ :
  (nᵉ : ℕᵉ) →
  listᵉ (Σᵉ (Finᵉ nᵉ ×ᵉ Finᵉ nᵉ) (λ (iᵉ ,ᵉ jᵉ) → iᵉ ≠ᵉ jᵉ)) →
  Permutationᵉ nᵉ
permutation-list-standard-transpositions-Finᵉ nᵉ =
  fold-listᵉ
    ( id-equivᵉ)
    ( λ (ᵉ_ ,ᵉ neqᵉ) pᵉ →
      standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ ∘eᵉ pᵉ)

list-standard-transpositions-permutation-Finᵉ :
  (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ nᵉ) →
  listᵉ (Σᵉ (Finᵉ nᵉ ×ᵉ Finᵉ nᵉ) (λ (iᵉ ,ᵉ jᵉ) → iᵉ ≠ᵉ jᵉ))
list-standard-transpositions-permutation-Finᵉ nᵉ fᵉ =
  map-listᵉ
    ( λ Pᵉ →
      ( element-two-elements-transposition-Finᵉ Pᵉ ,ᵉ
        other-element-two-elements-transposition-Finᵉ Pᵉ) ,ᵉ
      neq-elements-two-elements-transposition-Finᵉ Pᵉ)
    ( list-transpositions-permutation-Finᵉ nᵉ fᵉ)

private
  htpy-permutation-listᵉ :
    (nᵉ : ℕᵉ)
    (lᵉ : listᵉ
      (2-Element-Decidable-Subtypeᵉ lzero (Finᵉ (succ-ℕᵉ nᵉ)))) →
    htpy-equivᵉ
      ( permutation-list-standard-transpositions-Finᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-listᵉ
          ( λ Pᵉ →
            ( element-two-elements-transposition-Finᵉ Pᵉ ,ᵉ
              other-element-two-elements-transposition-Finᵉ Pᵉ) ,ᵉ
            neq-elements-two-elements-transposition-Finᵉ Pᵉ)
          ( lᵉ)))
      ( permutation-list-transpositionsᵉ lᵉ)
  htpy-permutation-listᵉ nᵉ nilᵉ = refl-htpyᵉ
  htpy-permutation-listᵉ nᵉ (consᵉ Pᵉ lᵉ) =
    ( htpy-two-elements-transpositon-Finᵉ Pᵉ ·rᵉ
      map-equivᵉ
        ( permutation-list-standard-transpositions-Finᵉ
          ( succ-ℕᵉ nᵉ)
          ( map-listᵉ
            ( λ Pᵉ →
              ( element-two-elements-transposition-Finᵉ Pᵉ ,ᵉ
                other-element-two-elements-transposition-Finᵉ Pᵉ) ,ᵉ
              neq-elements-two-elements-transposition-Finᵉ Pᵉ)
            ( lᵉ)))) ∙hᵉ
    ( map-transpositionᵉ Pᵉ ·lᵉ
      htpy-permutation-listᵉ nᵉ lᵉ)

retraction-permutation-list-standard-transpositions-Finᵉ :
  (nᵉ : ℕᵉ) (fᵉ : Permutationᵉ nᵉ) →
  htpy-equivᵉ
    ( permutation-list-standard-transpositions-Finᵉ
      ( nᵉ)
      ( list-standard-transpositions-permutation-Finᵉ nᵉ fᵉ))
    ( fᵉ)
retraction-permutation-list-standard-transpositions-Finᵉ 0 fᵉ ()
retraction-permutation-list-standard-transpositions-Finᵉ (succ-ℕᵉ nᵉ) fᵉ =
  htpy-permutation-listᵉ nᵉ (list-transpositions-permutation-Finᵉ (succ-ℕᵉ nᵉ) fᵉ) ∙hᵉ
  retraction-permutation-list-transpositions-Finᵉ (succ-ℕᵉ nᵉ) fᵉ
```