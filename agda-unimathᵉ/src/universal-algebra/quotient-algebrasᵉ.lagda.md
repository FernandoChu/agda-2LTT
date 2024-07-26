# Quotient algebras

```agda
module universal-algebra.quotient-algebrasᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.multivariable-functoriality-set-quotientsᵉ
open import foundation.multivariable-operationsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.vectors-set-quotientsᵉ

open import linear-algebra.vectorsᵉ

open import universal-algebra.algebraic-theoriesᵉ
open import universal-algebra.algebras-of-theoriesᵉ
open import universal-algebra.congruencesᵉ
open import universal-algebra.models-of-signaturesᵉ
open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Theᵉ quotientᵉ ofᵉ anᵉ algebraᵉ byᵉ aᵉ congruenceᵉ isᵉ theᵉ setᵉ quotientᵉ byᵉ thatᵉ
congruence.ᵉ Thisᵉ quotientᵉ againᵉ hasᵉ theᵉ structureᵉ ofᵉ anᵉ algebraᵉ inheritedᵉ byᵉ theᵉ
originalᵉ one.ᵉ

## Definitions

```agda
module _
  { l1ᵉ : Level} ( Sgᵉ : signatureᵉ l1ᵉ)
  { l2ᵉ : Level} ( Thᵉ : Theoryᵉ Sgᵉ l2ᵉ)
  { l3ᵉ : Level} ( Algᵉ : Algebraᵉ Sgᵉ Thᵉ l3ᵉ)
  { l4ᵉ : Level} ( Rᵉ : congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ l4ᵉ)
  where

  set-quotient-Algebraᵉ : Setᵉ (l3ᵉ ⊔ l4ᵉ)
  set-quotient-Algebraᵉ =
    quotient-Setᵉ ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)

  type-quotient-Algebraᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  type-quotient-Algebraᵉ = pr1ᵉ set-quotient-Algebraᵉ

  is-set-set-quotient-Algebraᵉ : is-setᵉ type-quotient-Algebraᵉ
  is-set-set-quotient-Algebraᵉ = pr2ᵉ set-quotient-Algebraᵉ

  compute-quotient-Algebraᵉ :
    equivalence-classᵉ
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ) ≃ᵉ
      ( type-quotient-Algebraᵉ)
  compute-quotient-Algebraᵉ =
    compute-set-quotientᵉ
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)

  set-quotient-equivalence-class-Algebraᵉ :
    equivalence-classᵉ
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ) →
    type-quotient-Algebraᵉ
  set-quotient-equivalence-class-Algebraᵉ =
    map-equivᵉ compute-quotient-Algebraᵉ

  equivalence-class-set-quotient-Algebraᵉ :
    type-quotient-Algebraᵉ →
    equivalence-classᵉ
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)
  equivalence-class-set-quotient-Algebraᵉ =
    map-inv-equivᵉ compute-quotient-Algebraᵉ

  vec-type-quotient-vec-type-Algebraᵉ :
    { nᵉ : ℕᵉ} →
    vecᵉ type-quotient-Algebraᵉ nᵉ →
    type-trunc-Propᵉ (vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ) nᵉ)
  vec-type-quotient-vec-type-Algebraᵉ empty-vecᵉ = unit-trunc-Propᵉ empty-vecᵉ
  vec-type-quotient-vec-type-Algebraᵉ (xᵉ ∷ᵉ vᵉ) =
    map-universal-property-trunc-Propᵉ
      ( trunc-Propᵉ _)
      ( λ (zᵉ ,ᵉ pᵉ) →
        map-trunc-Propᵉ
          (λ v'ᵉ → zᵉ ∷ᵉ v'ᵉ)
          ( vec-type-quotient-vec-type-Algebraᵉ vᵉ))
      ( pr2ᵉ (equivalence-class-set-quotient-Algebraᵉ xᵉ))

  relation-holds-all-vec-all-sim-equivalence-relationᵉ :
    { nᵉ : ℕᵉ}
    ( vᵉ v'ᵉ : multivariable-inputᵉ nᵉ ( λ _ → type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)) →
    ( type-Propᵉ
      ( prop-equivalence-relationᵉ
        ( all-sim-equivalence-relationᵉ nᵉ
          ( λ _ → type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
          ( λ _ → equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)) vᵉ v'ᵉ)) →
    relation-holds-all-vecᵉ Sgᵉ Thᵉ Algᵉ
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)
      ( vector-multivariable-inputᵉ nᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ) vᵉ)
      ( vector-multivariable-inputᵉ nᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ) v'ᵉ)
  relation-holds-all-vec-all-sim-equivalence-relationᵉ {zero-ℕᵉ} vᵉ v'ᵉ pᵉ =
    raise-starᵉ
  relation-holds-all-vec-all-sim-equivalence-relationᵉ
    {succ-ℕᵉ nᵉ} (xᵉ ,ᵉ vᵉ) (x'ᵉ ,ᵉ v'ᵉ) (pᵉ ,ᵉ p'ᵉ) =
    pᵉ ,ᵉ (relation-holds-all-vec-all-sim-equivalence-relationᵉ vᵉ v'ᵉ p'ᵉ)

  is-model-set-quotient-Algebraᵉ :
    is-model-signatureᵉ Sgᵉ set-quotient-Algebraᵉ
  is-model-set-quotient-Algebraᵉ opᵉ vᵉ =
    multivariable-map-set-quotientᵉ
      ( arity-operation-signatureᵉ Sgᵉ opᵉ)
      ( λ _ → type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
      ( λ _ → equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)
      ( equivalence-relation-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ)
      ( pairᵉ
        ( λ vᵉ →
          is-model-set-Algebraᵉ Sgᵉ Thᵉ Algᵉ opᵉ
            ( vector-multivariable-inputᵉ
              ( arity-operation-signatureᵉ Sgᵉ opᵉ)
              ( type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
              ( vᵉ)))
        ( λ {vᵉ} {v'ᵉ} pᵉ →
          preserves-operations-congruence-Algebraᵉ Sgᵉ Thᵉ Algᵉ Rᵉ opᵉ
            ( vector-multivariable-inputᵉ
              ( arity-operation-signatureᵉ Sgᵉ opᵉ)
              ( type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
              ( vᵉ))
            ( vector-multivariable-inputᵉ
              ( arity-operation-signatureᵉ Sgᵉ opᵉ)
              ( type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
              ( v'ᵉ))
            (relation-holds-all-vec-all-sim-equivalence-relationᵉ vᵉ v'ᵉ pᵉ)))
      ( multivariable-input-vectorᵉ
        ( arity-operation-signatureᵉ Sgᵉ opᵉ)
        ( type-quotient-Algebraᵉ)
        ( vᵉ))
```