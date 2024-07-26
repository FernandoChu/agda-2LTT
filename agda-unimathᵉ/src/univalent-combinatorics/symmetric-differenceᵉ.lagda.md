# Symmetric difference of finite subtypes

```agda
module univalent-combinatorics.symmetric-differenceᵉ where

open import foundation.symmetric-differenceᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

```agda
module _
  {lᵉ l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ lᵉ) (Fᵉ : is-finiteᵉ Xᵉ)
  (Pᵉ : decidable-subtypeᵉ l1ᵉ Xᵉ)
  (Qᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ)
  where

  eq-symmetric-differenceᵉ :
    Idᵉ
      ( add-ℕᵉ
        ( number-of-elements-is-finiteᵉ
          ( is-finite-type-decidable-subtypeᵉ Pᵉ Fᵉ))
        ( number-of-elements-is-finiteᵉ (is-finite-type-decidable-subtypeᵉ Qᵉ Fᵉ)))
      ( add-ℕᵉ
        ( number-of-elements-is-finiteᵉ
          ( is-finite-type-decidable-subtypeᵉ
            ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ) Fᵉ))
        ( 2 *ℕᵉ
          ( number-of-elements-is-finiteᵉ
            ( is-finite-type-decidable-subtypeᵉ
              ( intersection-decidable-subtypeᵉ Pᵉ Qᵉ)
              ( Fᵉ)))))
  eq-symmetric-differenceᵉ =
    ( ( coproduct-eq-is-finiteᵉ
        ( is-finite-type-decidable-subtypeᵉ Pᵉ Fᵉ)
        ( is-finite-type-decidable-subtypeᵉ Qᵉ Fᵉ))) ∙ᵉ
      ( ( apᵉ
          ( number-of-elements-has-finite-cardinalityᵉ)
          ( all-elements-equal-has-finite-cardinalityᵉ
            ( has-finite-cardinality-is-finiteᵉ
              ( is-finite-coproductᵉ
                ( is-finite-type-decidable-subtypeᵉ Pᵉ Fᵉ)
                ( is-finite-type-decidable-subtypeᵉ Qᵉ Fᵉ)))
            ( pairᵉ
              ( number-of-elements-is-finiteᵉ
                ( is-finite-coproduct-symmetric-differenceᵉ))
              ( transitive-mere-equivᵉ _ _ _
                ( unit-trunc-Propᵉ
                  ( inv-equivᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ)))
                ( mere-equiv-has-finite-cardinalityᵉ
                  ( has-finite-cardinality-is-finiteᵉ
                    ( is-finite-coproduct-symmetric-differenceᵉ))))))) ∙ᵉ
        ( invᵉ
          ( coproduct-eq-is-finiteᵉ
            ( is-finite-type-decidable-subtypeᵉ
              ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ) Fᵉ)
            ( is-finite-coproductᵉ
              ( is-finite-intersectionᵉ)
              ( is-finite-intersectionᵉ))) ∙ᵉ
          ( apᵉ
            ( ( number-of-elements-decidable-subtype-Xᵉ
                ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ℕᵉ_)
            ( ( invᵉ
                ( coproduct-eq-is-finiteᵉ
                  ( is-finite-intersectionᵉ)
                  ( is-finite-intersectionᵉ))) ∙ᵉ
              ( apᵉ
                ( _+ℕᵉ
                  ( number-of-elements-decidable-subtype-Xᵉ
                    ( intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))
                ( invᵉ
                  ( left-unit-law-mul-ℕᵉ
                    ( number-of-elements-decidable-subtype-Xᵉ
                      ( intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))))))))
    where
    is-finite-intersectionᵉ :
      is-finiteᵉ (type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ))
    is-finite-intersectionᵉ =
      is-finite-type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ) Fᵉ
    number-of-elements-decidable-subtype-Xᵉ :
      {l'ᵉ : Level} → decidable-subtypeᵉ l'ᵉ Xᵉ → ℕᵉ
    number-of-elements-decidable-subtype-Xᵉ Rᵉ =
      number-of-elements-is-finiteᵉ (is-finite-type-decidable-subtypeᵉ Rᵉ Fᵉ)
    is-finite-coproduct-symmetric-differenceᵉ :
      is-finiteᵉ
        ( ( type-decidable-subtypeᵉ
            ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
          ( ( type-decidable-subtypeᵉ
              ( intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
            ( type-decidable-subtypeᵉ
              ( intersection-decidable-subtypeᵉ Pᵉ Qᵉ))))
    is-finite-coproduct-symmetric-differenceᵉ =
      is-finite-coproductᵉ
        ( is-finite-type-decidable-subtypeᵉ
          ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)
          ( Fᵉ))
        ( is-finite-coproductᵉ is-finite-intersectionᵉ is-finite-intersectionᵉ)
```