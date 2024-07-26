# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ

open import linear-algebra.vectorsᵉ

open import universal-algebra.algebraic-theoriesᵉ
open import universal-algebra.algebras-of-theoriesᵉ
open import universal-algebra.signaturesᵉ
open import universal-algebra.terms-over-signaturesᵉ
```

</details>

## Idea

Thereᵉ isᵉ anᵉ algebraicᵉ theoryᵉ ofᵉ groups.ᵉ Theyᵉ typeᵉ ofᵉ allᵉ suchᵉ algebrasᵉ isᵉ
equivalentᵉ to theᵉ typeᵉ ofᵉ groups.ᵉ

## Definitions

### The algebra of groups

```agda
data group-opsᵉ : UUᵉ lzero where
  unit-group-opᵉ mul-group-opᵉ inv-group-opᵉ : group-opsᵉ

group-signatureᵉ : signatureᵉ lzero
pr1ᵉ group-signatureᵉ = group-opsᵉ
pr2ᵉ group-signatureᵉ unit-group-opᵉ = 0
pr2ᵉ group-signatureᵉ mul-group-opᵉ = 2
pr2ᵉ group-signatureᵉ inv-group-opᵉ = 1

data group-lawsᵉ : UUᵉ lzero where
  associative-l-group-lawsᵉ : group-lawsᵉ
  invl-l-group-lawsᵉ : group-lawsᵉ
  invr-r-group-lawsᵉ : group-lawsᵉ
  idl-l-group-lawsᵉ : group-lawsᵉ
  idr-r-group-lawsᵉ : group-lawsᵉ

group-Theoryᵉ : Theoryᵉ group-signatureᵉ lzero
pr1ᵉ group-Theoryᵉ = group-lawsᵉ
pr2ᵉ group-Theoryᵉ =
  λ where
  associative-l-group-lawsᵉ →
    ( opᵉ mul-group-opᵉ
      ( ( opᵉ mul-group-opᵉ (varᵉ 0 ∷ᵉ varᵉ 1 ∷ᵉ empty-vecᵉ)) ∷ᵉ varᵉ 2 ∷ᵉ empty-vecᵉ)) ,ᵉ
    ( opᵉ mul-group-opᵉ
      ( varᵉ 0 ∷ᵉ (opᵉ mul-group-opᵉ (varᵉ 1 ∷ᵉ varᵉ 2 ∷ᵉ empty-vecᵉ)) ∷ᵉ empty-vecᵉ))
  invl-l-group-lawsᵉ →
    ( opᵉ mul-group-opᵉ
      ( opᵉ inv-group-opᵉ (varᵉ 0 ∷ᵉ empty-vecᵉ) ∷ᵉ varᵉ 0 ∷ᵉ empty-vecᵉ)) ,ᵉ
    ( opᵉ unit-group-opᵉ empty-vecᵉ)
  invr-r-group-lawsᵉ →
    ( opᵉ mul-group-opᵉ
      ( varᵉ 0 ∷ᵉ opᵉ inv-group-opᵉ (varᵉ 0 ∷ᵉ empty-vecᵉ) ∷ᵉ empty-vecᵉ)) ,ᵉ
    ( opᵉ unit-group-opᵉ empty-vecᵉ)
  idl-l-group-lawsᵉ →
    ( opᵉ mul-group-opᵉ (opᵉ unit-group-opᵉ empty-vecᵉ ∷ᵉ varᵉ 0 ∷ᵉ empty-vecᵉ)) ,ᵉ
    ( varᵉ 0ᵉ)
  idr-r-group-lawsᵉ →
    ( opᵉ mul-group-opᵉ (varᵉ 0 ∷ᵉ opᵉ unit-group-opᵉ empty-vecᵉ ∷ᵉ empty-vecᵉ)) ,ᵉ
    ( varᵉ 0ᵉ)
    where
    opᵉ = op-Termᵉ
    varᵉ = var-Termᵉ

group-Algebraᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
group-Algebraᵉ lᵉ = Algebraᵉ group-signatureᵉ group-Theoryᵉ lᵉ
```

## Properties

### The algebra of groups is equivalent to the type of groups

```agda
group-Algebra-Groupᵉ :
  {lᵉ : Level} →
  Algebraᵉ group-signatureᵉ group-Theoryᵉ lᵉ →
  Groupᵉ lᵉ
pr1ᵉ (pr1ᵉ (group-Algebra-Groupᵉ ((A-Setᵉ ,ᵉ models-Aᵉ) ,ᵉ satisfies-Aᵉ))) = A-Setᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (group-Algebra-Groupᵉ ((A-Setᵉ ,ᵉ models-Aᵉ) ,ᵉ satisfies-Aᵉ)))) xᵉ yᵉ =
  models-Aᵉ mul-group-opᵉ (xᵉ ∷ᵉ yᵉ ∷ᵉ empty-vecᵉ)
pr2ᵉ (pr2ᵉ (pr1ᵉ (group-Algebra-Groupᵉ ((A-Setᵉ ,ᵉ models-Aᵉ) ,ᵉ satisfies-Aᵉ)))) xᵉ yᵉ zᵉ =
  satisfies-Aᵉ associative-l-group-lawsᵉ
    ( λ { 0 → xᵉ ; 1 → yᵉ ; (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → zᵉ})
pr1ᵉ (pr1ᵉ (pr2ᵉ (group-Algebra-Groupᵉ ((A-Setᵉ ,ᵉ models-Aᵉ) ,ᵉ satisfies-Aᵉ)))) =
  models-Aᵉ unit-group-opᵉ empty-vecᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (group-Algebra-Groupᵉ (ᵉ_ ,ᵉ satisfies-Aᵉ))))) xᵉ =
  satisfies-Aᵉ idl-l-group-lawsᵉ (λ _ → xᵉ)
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (group-Algebra-Groupᵉ (ᵉ_ ,ᵉ satisfies-Aᵉ))))) xᵉ =
  satisfies-Aᵉ idr-r-group-lawsᵉ (λ _ → xᵉ)
pr1ᵉ (pr2ᵉ (pr2ᵉ (group-Algebra-Groupᵉ ((A-Setᵉ ,ᵉ models-Aᵉ) ,ᵉ satisfies-Aᵉ)))) xᵉ =
  models-Aᵉ inv-group-opᵉ (xᵉ ∷ᵉ empty-vecᵉ)
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (group-Algebra-Groupᵉ (ᵉ_ ,ᵉ satisfies-Aᵉ))))) xᵉ =
  satisfies-Aᵉ invl-l-group-lawsᵉ (λ _ → xᵉ)
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (group-Algebra-Groupᵉ (ᵉ_ ,ᵉ satisfies-Aᵉ))))) xᵉ =
  satisfies-Aᵉ invr-r-group-lawsᵉ (λ _ → xᵉ)

Group-group-Algebraᵉ :
  {lᵉ : Level} →
  Groupᵉ lᵉ →
  Algebraᵉ group-signatureᵉ group-Theoryᵉ lᵉ
Group-group-Algebraᵉ Gᵉ =
  pairᵉ
    ( pairᵉ
      ( ( set-Groupᵉ Gᵉ))
      ( λ where
        unit-group-opᵉ vᵉ → unit-Groupᵉ Gᵉ
        mul-group-opᵉ (xᵉ ∷ᵉ yᵉ ∷ᵉ empty-vecᵉ) → mul-Groupᵉ Gᵉ xᵉ yᵉ
        inv-group-opᵉ (xᵉ ∷ᵉ empty-vecᵉ) → inv-Groupᵉ Gᵉ xᵉ))
    ( λ where
      associative-l-group-lawsᵉ assignᵉ →
        associative-mul-Groupᵉ Gᵉ (assignᵉ 0ᵉ) (assignᵉ 1ᵉ) (assignᵉ 2ᵉ)
      invl-l-group-lawsᵉ assignᵉ →
        left-inverse-law-mul-Groupᵉ Gᵉ (assignᵉ 0ᵉ)
      invr-r-group-lawsᵉ assignᵉ →
        right-inverse-law-mul-Groupᵉ Gᵉ (assignᵉ 0ᵉ)
      idl-l-group-lawsᵉ assignᵉ →
        left-unit-law-mul-Groupᵉ Gᵉ (assignᵉ 0ᵉ)
      idr-r-group-lawsᵉ assignᵉ →
        right-unit-law-mul-Groupᵉ Gᵉ (assignᵉ 0ᵉ))

abstract
  equiv-group-Algebra-Groupᵉ :
    {lᵉ : Level} →
    Algebraᵉ group-signatureᵉ group-Theoryᵉ lᵉ ≃ᵉ
    Groupᵉ lᵉ
  pr1ᵉ equiv-group-Algebra-Groupᵉ = group-Algebra-Groupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ equiv-group-Algebra-Groupᵉ)) = Group-group-Algebraᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ equiv-group-Algebra-Groupᵉ)) Gᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-is-propᵉ (is-prop-is-group-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)))
  pr1ᵉ (pr2ᵉ (pr2ᵉ equiv-group-Algebra-Groupᵉ)) = Group-group-Algebraᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equiv-group-Algebra-Groupᵉ)) Aᵉ =
    eq-pair-Σᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-htpyᵉ
          ( λ where
            unit-group-opᵉ → eq-htpyᵉ (λ where empty-vecᵉ → reflᵉ)
            mul-group-opᵉ → eq-htpyᵉ (λ where (xᵉ ∷ᵉ yᵉ ∷ᵉ empty-vecᵉ) → reflᵉ)
            inv-group-opᵉ → eq-htpyᵉ (λ where (xᵉ ∷ᵉ empty-vecᵉ) → reflᵉ))))
      ( eq-is-propᵉ
        ( is-prop-is-algebraᵉ
          ( group-signatureᵉ) ( group-Theoryᵉ)
          ( model-Algebraᵉ group-signatureᵉ group-Theoryᵉ Aᵉ)))
```