# The sign homomorphism

```agda
module finite-group-theory.sign-homomorphismᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutationsᵉ
open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.automorphismsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.symmetric-groupsᵉ

open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.listsᵉ

open import univalent-combinatorics.2-element-decidable-subtypesᵉ
open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ signᵉ ofᵉ aᵉ permutationᵉ isᵉ definedᵉ asᵉ theᵉ parityᵉ ofᵉ theᵉ lengthᵉ ofᵉ theᵉ
decompositionᵉ ofᵉ theᵉ permutationᵉ intoᵉ transpositions.ᵉ Weᵉ showᵉ thatᵉ eachᵉ suchᵉ
decompositionᵉ asᵉ theᵉ sameᵉ parity,ᵉ soᵉ theᵉ signᵉ mapᵉ isᵉ wellᵉ defined.ᵉ Weᵉ thenᵉ showᵉ
thatᵉ theᵉ signᵉ mapᵉ isᵉ aᵉ groupᵉ homomorphism.ᵉ

## Definitions

### The sign homomorphism into ℤ/2

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ)
  where

  sign-homomorphism-Fin-twoᵉ : Autᵉ (type-UU-Finᵉ nᵉ Xᵉ) → Finᵉ 2
  sign-homomorphism-Fin-twoᵉ fᵉ =
    pr1ᵉ (centerᵉ (is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ fᵉ))

  preserves-add-sign-homomorphism-Fin-twoᵉ :
    (fᵉ gᵉ : (type-UU-Finᵉ nᵉ Xᵉ) ≃ᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
    Idᵉ
      ( sign-homomorphism-Fin-twoᵉ (fᵉ ∘eᵉ gᵉ))
      ( add-Finᵉ 2 (sign-homomorphism-Fin-twoᵉ fᵉ) (sign-homomorphism-Fin-twoᵉ gᵉ))
  preserves-add-sign-homomorphism-Fin-twoᵉ fᵉ gᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)
      ( Id-Propᵉ
        ( Fin-Setᵉ 2ᵉ)
        ( sign-homomorphism-Fin-twoᵉ (fᵉ ∘eᵉ gᵉ))
        ( add-Finᵉ 2
          ( sign-homomorphism-Fin-twoᵉ fᵉ)
          ( sign-homomorphism-Fin-twoᵉ gᵉ)))
      ( λ hᵉ →
        ( apᵉ
          ( pr1ᵉ)
          ( eq-is-contrᵉ
            ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ (fᵉ ∘eᵉ gᵉ))
            { xᵉ =
              centerᵉ (is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ (fᵉ ∘eᵉ gᵉ))}
            { yᵉ =
              pairᵉ
                ( mod-two-ℕᵉ (length-listᵉ (list-comp-f-gᵉ hᵉ)))
                ( unit-trunc-Propᵉ
                  ( pairᵉ
                    ( list-comp-f-gᵉ hᵉ)
                    ( pairᵉ reflᵉ (eq-list-comp-f-gᵉ hᵉ))))})) ∙ᵉ
        ( ( apᵉ
            ( mod-two-ℕᵉ)
            ( length-concat-listᵉ (list-transᵉ fᵉ hᵉ) (list-transᵉ gᵉ hᵉ))) ∙ᵉ
          ( ( mod-succ-add-ℕᵉ 1
              ( length-listᵉ (list-transᵉ fᵉ hᵉ))
              ( length-listᵉ (list-transᵉ gᵉ hᵉ))) ∙ᵉ
            ( ( apᵉ
                ( λ Pᵉ →
                  add-Finᵉ 2 (pr1ᵉ Pᵉ)
                    ( mod-two-ℕᵉ (length-listᵉ (list-transᵉ gᵉ hᵉ))))
                { xᵉ =
                  pairᵉ
                    ( mod-two-ℕᵉ (length-listᵉ (list-transᵉ fᵉ hᵉ)))
                    ( unit-trunc-Propᵉ
                      ( pairᵉ
                        ( list-transᵉ fᵉ hᵉ)
                        ( pairᵉ
                          ( reflᵉ)
                          ( invᵉ
                            ( eq-htpy-equivᵉ
                              ( retraction-permutation-list-transpositions-countᵉ
                                ( type-UU-Finᵉ nᵉ Xᵉ)
                                ( pairᵉ nᵉ hᵉ)
                                ( fᵉ)))))))}
                { yᵉ = centerᵉ (is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ fᵉ)}
                ( eq-is-contrᵉ
                  ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ fᵉ))) ∙ᵉ
              ( apᵉ
                ( λ Pᵉ → add-Finᵉ 2 (sign-homomorphism-Fin-twoᵉ fᵉ) (pr1ᵉ Pᵉ))
                { xᵉ =
                  pairᵉ
                    ( mod-two-ℕᵉ (length-listᵉ (list-transᵉ gᵉ hᵉ)))
                    ( unit-trunc-Propᵉ
                      ( pairᵉ
                        ( list-transᵉ gᵉ hᵉ)
                        ( pairᵉ
                          ( reflᵉ)
                          ( invᵉ
                            ( eq-htpy-equivᵉ
                              ( retraction-permutation-list-transpositions-countᵉ
                                ( type-UU-Finᵉ nᵉ Xᵉ)
                                ( pairᵉ nᵉ hᵉ)
                                ( gᵉ)))))))}
                { yᵉ = centerᵉ (is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ gᵉ)}
                ( eq-is-contrᵉ
                  ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ gᵉ)))))))
    where
    list-transᵉ :
      ( f'ᵉ : (type-UU-Finᵉ nᵉ Xᵉ) ≃ᵉ (type-UU-Finᵉ nᵉ Xᵉ))
      ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      listᵉ
        ( Σᵉ ( type-UU-Finᵉ nᵉ Xᵉ → Decidable-Propᵉ lᵉ)
            ( λ Pᵉ →
              has-cardinalityᵉ 2
                ( Σᵉ (type-UU-Finᵉ nᵉ Xᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
    list-transᵉ f'ᵉ hᵉ =
      list-transpositions-permutation-countᵉ (type-UU-Finᵉ nᵉ Xᵉ) (pairᵉ nᵉ hᵉ) f'ᵉ
    list-comp-f-gᵉ :
      ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      listᵉ
        ( Σᵉ ( (type-UU-Finᵉ nᵉ Xᵉ) → Decidable-Propᵉ lᵉ)
            ( λ Pᵉ →
              has-cardinalityᵉ 2
                ( Σᵉ (type-UU-Finᵉ nᵉ Xᵉ) (type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
    list-comp-f-gᵉ hᵉ = concat-listᵉ (list-transᵉ fᵉ hᵉ) (list-transᵉ gᵉ hᵉ)
    eq-list-comp-f-gᵉ :
      ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      Idᵉ
        ( fᵉ ∘eᵉ gᵉ)
        ( permutation-list-transpositionsᵉ
          ( list-comp-f-gᵉ hᵉ))
    eq-list-comp-f-gᵉ hᵉ =
      eq-htpy-equivᵉ
        ( λ xᵉ →
          ( invᵉ
            ( retraction-permutation-list-transpositions-countᵉ
              ( type-UU-Finᵉ nᵉ Xᵉ)
              ( pairᵉ nᵉ hᵉ)
              ( fᵉ)
              ( map-equivᵉ gᵉ xᵉ))) ∙ᵉ
          ( apᵉ
            ( map-equivᵉ
              ( permutation-list-transpositionsᵉ
                ( list-transᵉ fᵉ hᵉ)))
            ( invᵉ
              ( retraction-permutation-list-transpositions-countᵉ
                ( type-UU-Finᵉ nᵉ Xᵉ)
                ( pairᵉ nᵉ hᵉ)
                ( gᵉ)
                ( xᵉ))))) ∙ᵉ
              ( eq-concat-permutation-list-transpositionsᵉ
                ( list-transᵉ fᵉ hᵉ)
                ( list-transᵉ gᵉ hᵉ))

  eq-sign-homomorphism-Fin-two-transpositionᵉ :
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
    Idᵉ
      ( sign-homomorphism-Fin-twoᵉ (transpositionᵉ Yᵉ))
      ( inrᵉ starᵉ)
  eq-sign-homomorphism-Fin-two-transpositionᵉ Yᵉ =
    apᵉ pr1ᵉ
      { xᵉ =
        centerᵉ
          ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ (transpositionᵉ Yᵉ))}
      { yᵉ =
        pairᵉ
          ( inrᵉ starᵉ)
          ( unit-trunc-Propᵉ
            ( pairᵉ
              ( unit-listᵉ Yᵉ)
              ( pairᵉ reflᵉ (invᵉ (right-unit-law-equivᵉ (transpositionᵉ Yᵉ))))))}
      ( eq-is-contrᵉ
        ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ (transpositionᵉ Yᵉ)))

module _
  {lᵉ l'ᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ) (Yᵉ : UU-Finᵉ l'ᵉ nᵉ)
  where

  preserves-conjugation-sign-homomorphism-Fin-twoᵉ :
    (fᵉ : (type-UU-Finᵉ nᵉ Xᵉ) ≃ᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
    (gᵉ : (type-UU-Finᵉ nᵉ Xᵉ) ≃ᵉ (type-UU-Finᵉ nᵉ Yᵉ)) →
    Idᵉ
      ( sign-homomorphism-Fin-twoᵉ nᵉ Yᵉ (gᵉ ∘eᵉ (fᵉ ∘eᵉ inv-equivᵉ gᵉ)))
      ( sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ fᵉ)
  preserves-conjugation-sign-homomorphism-Fin-twoᵉ fᵉ gᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-cardinality-type-UU-Finᵉ nᵉ Xᵉ)
      ( Id-Propᵉ
        ( Fin-Setᵉ 2ᵉ)
        ( sign-homomorphism-Fin-twoᵉ nᵉ Yᵉ (gᵉ ∘eᵉ (fᵉ ∘eᵉ inv-equivᵉ gᵉ)))
        ( sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ fᵉ))
      ( λ hᵉ →
        ( apᵉ
          ( pr1ᵉ)
            ( eq-is-contrᵉ
              ( is-contr-parity-transposition-permutationᵉ
                ( nᵉ)
                ( Yᵉ)
                ( gᵉ ∘eᵉ (fᵉ ∘eᵉ inv-equivᵉ gᵉ)))
              { xᵉ =
                centerᵉ
                  ( is-contr-parity-transposition-permutationᵉ
                    ( nᵉ)
                    ( Yᵉ)
                    ( gᵉ ∘eᵉ (fᵉ ∘eᵉ inv-equivᵉ gᵉ)))}
              { yᵉ =
                pairᵉ
                  ( mod-two-ℕᵉ
                    ( length-listᵉ
                      ( map-listᵉ
                        ( map-equivᵉ
                          ( equiv-universes-2-Element-Decidable-Subtypeᵉ
                            ( type-UU-Finᵉ nᵉ Yᵉ)
                            ( lᵉ)
                            ( l'ᵉ)))
                        ( list-conjugationᵉ hᵉ))))
                  ( unit-trunc-Propᵉ
                    ( pairᵉ
                      ( map-listᵉ
                        ( map-equivᵉ
                          ( equiv-universes-2-Element-Decidable-Subtypeᵉ
                            ( type-UU-Finᵉ nᵉ Yᵉ)
                            ( lᵉ)
                            ( l'ᵉ)))
                        ( list-conjugationᵉ hᵉ))
                      ( pairᵉ
                        ( reflᵉ)
                        ( ( invᵉ
                          ( ( eq-htpy-equivᵉ
                            ( correct-transposition-conjugation-equiv-listᵉ
                              ( type-UU-Finᵉ nᵉ Xᵉ)
                              ( type-UU-Finᵉ nᵉ Yᵉ)
                              ( gᵉ)
                              ( list-transᵉ hᵉ))) ∙ᵉ
                            ( apᵉ
                              ( λ h'ᵉ → gᵉ ∘eᵉ (h'ᵉ ∘eᵉ inv-equivᵉ gᵉ))
                              ( eq-htpy-equivᵉ
                                { eᵉ =
                                  permutation-list-transpositionsᵉ
                                    ( list-transᵉ hᵉ)}
                                ( retraction-permutation-list-transpositions-countᵉ
                                  ( type-UU-Finᵉ nᵉ Xᵉ)
                                  ( pairᵉ nᵉ hᵉ)
                                  ( fᵉ)))))) ∙ᵉ
                          ( eq-equiv-universes-transposition-listᵉ
                            ( type-UU-Finᵉ nᵉ Yᵉ)
                            ( lᵉ)
                            ( l'ᵉ)
                            ( list-conjugationᵉ hᵉ))))))})) ∙ᵉ
          ( ( apᵉ
            ( mod-two-ℕᵉ)
            ( ( length-map-listᵉ
              ( map-equivᵉ
                ( equiv-universes-2-Element-Decidable-Subtypeᵉ
                  ( type-UU-Finᵉ nᵉ Yᵉ)
                  ( lᵉ)
                  ( l'ᵉ)))
              ( list-conjugationᵉ hᵉ)) ∙ᵉ
              ( length-map-listᵉ
              ( transposition-conjugation-equivᵉ
                ( type-UU-Finᵉ nᵉ Xᵉ)
                ( type-UU-Finᵉ nᵉ Yᵉ)
                ( gᵉ))
              ( list-transᵉ hᵉ)))) ∙ᵉ
            ( apᵉ
              ( pr1ᵉ)
              { xᵉ =
                pairᵉ
                  ( mod-two-ℕᵉ (length-listᵉ (list-transᵉ hᵉ)))
                  ( unit-trunc-Propᵉ
                    ( pairᵉ
                      ( list-transᵉ hᵉ)
                      ( pairᵉ
                        ( reflᵉ)
                        ( invᵉ
                          ( eq-htpy-equivᵉ
                            ( retraction-permutation-list-transpositions-countᵉ
                              ( type-UU-Finᵉ nᵉ Xᵉ)
                              ( pairᵉ nᵉ hᵉ)
                              ( fᵉ)))))))}
              { yᵉ = centerᵉ (is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ fᵉ)}
              ( eq-is-contrᵉ
                ( is-contr-parity-transposition-permutationᵉ nᵉ Xᵉ fᵉ)))))
    where
    list-transᵉ :
      ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      listᵉ
        ( Σᵉ ( type-UU-Finᵉ nᵉ Xᵉ → Decidable-Propᵉ lᵉ)
            ( λ Pᵉ →
              has-cardinalityᵉ 2
                ( Σᵉ
                  ( type-UU-Finᵉ nᵉ Xᵉ)
                  ( type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
    list-transᵉ hᵉ =
      list-transpositions-permutation-countᵉ
        ( type-UU-Finᵉ nᵉ Xᵉ)
        ( pairᵉ nᵉ hᵉ)
        ( fᵉ)
    list-conjugationᵉ :
      ( hᵉ : Finᵉ nᵉ ≃ᵉ type-UU-Finᵉ nᵉ Xᵉ) →
      listᵉ
        ( Σᵉ ( (type-UU-Finᵉ nᵉ Yᵉ) → Decidable-Propᵉ lᵉ)
            ( λ Pᵉ →
              has-cardinalityᵉ 2
                ( Σᵉ
                  ( type-UU-Finᵉ nᵉ Yᵉ)
                  ( type-Decidable-Propᵉ ∘ᵉ Pᵉ))))
    list-conjugationᵉ hᵉ =
      map-listᵉ
        ( transposition-conjugation-equivᵉ
          { l4ᵉ = lᵉ}
          ( type-UU-Finᵉ nᵉ Xᵉ)
          ( type-UU-Finᵉ nᵉ Yᵉ)
          ( gᵉ))
        ( list-transᵉ hᵉ)
```

### The sign homomorphism into the symmetric group S₂

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ nᵉ)
  where

  map-sign-homomorphismᵉ : Autᵉ (type-UU-Finᵉ nᵉ Xᵉ) → Autᵉ (Finᵉ 2ᵉ)
  map-sign-homomorphismᵉ fᵉ =
    aut-point-Fin-two-ℕᵉ (sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ fᵉ)

  preserves-comp-map-sign-homomorphismᵉ :
    preserves-mulᵉ _∘eᵉ_ _∘eᵉ_ map-sign-homomorphismᵉ
  preserves-comp-map-sign-homomorphismᵉ {fᵉ} {gᵉ} =
    ( apᵉ
      ( aut-point-Fin-two-ℕᵉ)
      ( preserves-add-sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ fᵉ gᵉ)) ∙ᵉ
    ( preserves-add-aut-point-Fin-two-ℕᵉ
      ( sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ fᵉ)
      ( sign-homomorphism-Fin-twoᵉ nᵉ Xᵉ gᵉ))

  sign-homomorphismᵉ :
    hom-Groupᵉ
      ( symmetric-Groupᵉ (set-UU-Finᵉ nᵉ Xᵉ))
      ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
  pr1ᵉ sign-homomorphismᵉ = map-sign-homomorphismᵉ
  pr2ᵉ sign-homomorphismᵉ = preserves-comp-map-sign-homomorphismᵉ

  eq-sign-homomorphism-transpositionᵉ :
    ( Yᵉ : 2-Element-Decidable-Subtypeᵉ lᵉ (type-UU-Finᵉ nᵉ Xᵉ)) →
    Idᵉ
      ( map-hom-Groupᵉ
        ( symmetric-Groupᵉ (set-UU-Finᵉ nᵉ Xᵉ))
        ( symmetric-Groupᵉ (Fin-Setᵉ 2ᵉ))
        ( sign-homomorphismᵉ)
        ( transpositionᵉ Yᵉ))
      ( equiv-succ-Finᵉ 2ᵉ)
  eq-sign-homomorphism-transpositionᵉ Yᵉ =
    apᵉ aut-point-Fin-two-ℕᵉ (eq-sign-homomorphism-Fin-two-transpositionᵉ nᵉ Xᵉ Yᵉ)
```