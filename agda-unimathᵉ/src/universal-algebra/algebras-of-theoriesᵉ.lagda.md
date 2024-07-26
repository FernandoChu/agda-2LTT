# Algebras

```agda
module universal-algebra.algebras-of-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import universal-algebra.abstract-equations-over-signaturesᵉ
open import universal-algebra.algebraic-theoriesᵉ
open import universal-algebra.models-of-signaturesᵉ
open import universal-algebra.signaturesᵉ
open import universal-algebra.terms-over-signaturesᵉ
```

</details>

## Idea

Givenᵉ aᵉ theory,ᵉ anᵉ algebraᵉ isᵉ aᵉ modelᵉ onᵉ aᵉ setᵉ suchᵉ thatᵉ itᵉ satisfiesᵉ allᵉ
equationsᵉ in theᵉ theory.ᵉ

## Definitions

### Algebra

```agda
module _
  { l1ᵉ : Level} ( Sgᵉ : signatureᵉ l1ᵉ)
  { l2ᵉ : Level} ( Thᵉ : Theoryᵉ Sgᵉ l2ᵉ)
  where

  is-algebraᵉ :
    { l3ᵉ : Level} →
    ( Xᵉ : Model-Signatureᵉ Sgᵉ l3ᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-algebraᵉ Mᵉ =
    ( eᵉ : index-Theoryᵉ Sgᵉ Thᵉ) →
    ( assignᵉ : assignmentᵉ Sgᵉ (type-Model-Signatureᵉ Sgᵉ Mᵉ)) →
    eval-termᵉ Sgᵉ (is-model-set-Model-Signatureᵉ Sgᵉ Mᵉ) assignᵉ
      ( lhs-Abstract-Equationᵉ Sgᵉ (index-Abstract-Equation-Theoryᵉ Sgᵉ Thᵉ eᵉ)) ＝ᵉ
      eval-termᵉ Sgᵉ (is-model-set-Model-Signatureᵉ Sgᵉ Mᵉ) assignᵉ
        ( rhs-Abstract-Equationᵉ Sgᵉ (index-Abstract-Equation-Theoryᵉ Sgᵉ Thᵉ eᵉ))

  Algebraᵉ :
    ( l3ᵉ : Level) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  Algebraᵉ l3ᵉ =
    Σᵉ ( Model-Signatureᵉ Sgᵉ l3ᵉ) (is-algebraᵉ)

  model-Algebraᵉ :
    { l3ᵉ : Level} →
    Algebraᵉ l3ᵉ → Model-Signatureᵉ Sgᵉ l3ᵉ
  model-Algebraᵉ Algᵉ = pr1ᵉ Algᵉ

  set-Algebraᵉ :
    { l3ᵉ : Level} →
    Algebraᵉ l3ᵉ → Setᵉ l3ᵉ
  set-Algebraᵉ Algᵉ = pr1ᵉ (pr1ᵉ Algᵉ)

  is-model-set-Algebraᵉ :
    { l3ᵉ : Level} →
    ( Algᵉ : Algebraᵉ l3ᵉ) →
    is-model-signatureᵉ Sgᵉ (set-Algebraᵉ Algᵉ)
  is-model-set-Algebraᵉ Algᵉ = pr2ᵉ (pr1ᵉ Algᵉ)

  type-Algebraᵉ :
    { l3ᵉ : Level} →
    Algebraᵉ l3ᵉ → UUᵉ l3ᵉ
  type-Algebraᵉ Algᵉ =
    pr1ᵉ (pr1ᵉ (pr1ᵉ Algᵉ))

  is-set-Algebraᵉ :
    { l3ᵉ : Level} →
    (Algᵉ : Algebraᵉ l3ᵉ) → is-setᵉ (type-Algebraᵉ Algᵉ)
  is-set-Algebraᵉ Algᵉ = pr2ᵉ (pr1ᵉ (pr1ᵉ Algᵉ))

  is-algebra-Algebraᵉ :
    { l3ᵉ : Level} →
    ( Algᵉ : Algebraᵉ l3ᵉ) →
    is-algebraᵉ (model-Algebraᵉ Algᵉ)
  is-algebra-Algebraᵉ Algᵉ = pr2ᵉ Algᵉ
```

## Properties

### Being an algebra is a proposition

```agda
  is-prop-is-algebraᵉ :
    { l3ᵉ : Level} →
    ( Xᵉ : Model-Signatureᵉ Sgᵉ l3ᵉ) →
    is-propᵉ (is-algebraᵉ Xᵉ)
  is-prop-is-algebraᵉ Mᵉ =
    is-prop-Πᵉ
      ( λ eᵉ →
        ( is-prop-Πᵉ
          ( λ assignᵉ → is-set-type-Model-Signatureᵉ Sgᵉ Mᵉ _ _)))
```