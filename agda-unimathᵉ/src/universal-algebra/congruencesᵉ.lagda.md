# Congruences

```agda
module universal-algebra.congruencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import universal-algebra.algebraic-theoriesᵉ
open import universal-algebra.algebras-of-theoriesᵉ
open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Aᵉ congruenceᵉ in anᵉ algebraᵉ isᵉ anᵉ equivalenceᵉ relationᵉ thatᵉ respectsᵉ allᵉ
operationsᵉ ofᵉ theᵉ algebra.ᵉ

## Definitions

```agda
module _
  { l1ᵉ : Level} ( Sgᵉ : signatureᵉ l1ᵉ)
  { l2ᵉ : Level} ( Thᵉ : Theoryᵉ Sgᵉ l2ᵉ)
  { l3ᵉ : Level} ( Algᵉ : Algebraᵉ Sgᵉ Thᵉ l3ᵉ)
  where

  relation-holds-all-vecᵉ :
    { l4ᵉ : Level} →
    ( Rᵉ : equivalence-relationᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)) →
    { nᵉ : ℕᵉ} →
    ( vᵉ : vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ) nᵉ) →
    ( v'ᵉ : vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ) nᵉ) →
    UUᵉ l4ᵉ
  relation-holds-all-vecᵉ {l4ᵉ} Rᵉ {.zero-ℕᵉ} empty-vecᵉ empty-vecᵉ = raise-unitᵉ l4ᵉ
  relation-holds-all-vecᵉ {l4ᵉ} Rᵉ {.(succ-ℕᵉ _)} (xᵉ ∷ᵉ vᵉ) (x'ᵉ ∷ᵉ v'ᵉ) =
    ( type-Propᵉ (prop-equivalence-relationᵉ Rᵉ xᵉ x'ᵉ)) ×ᵉ
    ( relation-holds-all-vecᵉ Rᵉ vᵉ v'ᵉ)

  preserves-operationsᵉ :
    { l4ᵉ : Level} →
    ( Rᵉ : equivalence-relationᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  preserves-operationsᵉ Rᵉ =
    ( opᵉ : operation-signatureᵉ Sgᵉ) →
    ( vᵉ : vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
      ( arity-operation-signatureᵉ Sgᵉ opᵉ)) →
    ( v'ᵉ : vecᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ)
      ( arity-operation-signatureᵉ Sgᵉ opᵉ)) →
        ( relation-holds-all-vecᵉ Rᵉ vᵉ v'ᵉ →
          ( type-Propᵉ
            ( prop-equivalence-relationᵉ Rᵉ
              ( is-model-set-Algebraᵉ Sgᵉ Thᵉ Algᵉ opᵉ vᵉ)
              ( is-model-set-Algebraᵉ Sgᵉ Thᵉ Algᵉ opᵉ v'ᵉ))))

  congruence-Algebraᵉ :
    ( l4ᵉ : Level) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ)
  congruence-Algebraᵉ l4ᵉ =
    Σᵉ ( equivalence-relationᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ))
      ( preserves-operationsᵉ)

  equivalence-relation-congruence-Algebraᵉ :
    { l4ᵉ : Level} →
    congruence-Algebraᵉ l4ᵉ → ( equivalence-relationᵉ l4ᵉ (type-Algebraᵉ Sgᵉ Thᵉ Algᵉ))
  equivalence-relation-congruence-Algebraᵉ = pr1ᵉ

  preserves-operations-congruence-Algebraᵉ :
    { l4ᵉ : Level} →
    ( Rᵉ : congruence-Algebraᵉ l4ᵉ) →
    ( preserves-operationsᵉ (equivalence-relation-congruence-Algebraᵉ Rᵉ))
  preserves-operations-congruence-Algebraᵉ = pr2ᵉ
```