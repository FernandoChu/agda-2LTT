# Terms over signatures

```agda
module universal-algebra.terms-over-signaturesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import lists.listsᵉ
open import lists.lists-discrete-typesᵉ

open import universal-algebra.models-of-signaturesᵉ
open import universal-algebra.signaturesᵉ
```

</details>

## Idea

Aᵉ termᵉ in aᵉ signature,ᵉ isᵉ anᵉ abstract representationᵉ ofᵉ aᵉ wellᵉ formedᵉ expressionᵉ
whichᵉ usesᵉ onlyᵉ variablesᵉ andᵉ operationsᵉ in theᵉ signature.ᵉ Forᵉ thisᵉ particularᵉ
formalization,ᵉ weᵉ areᵉ using deᵉ Bruijnᵉ variables.ᵉ

## Definitions

### Terms

```agda
module _
  {l1ᵉ : Level} (Sgᵉ : signatureᵉ l1ᵉ)
  where

  data Termᵉ : UUᵉ l1ᵉ where
    var-Termᵉ : ℕᵉ → Termᵉ
    op-Termᵉ : is-modelᵉ Sgᵉ Termᵉ

  de-bruijn-variables-termᵉ : Termᵉ → listᵉ ℕᵉ

  de-bruijn-variables-term-vecᵉ : {nᵉ : ℕᵉ} → vecᵉ Termᵉ nᵉ → listᵉ ℕᵉ

  de-bruijn-variables-termᵉ (var-Termᵉ xᵉ) = consᵉ xᵉ nilᵉ
  de-bruijn-variables-termᵉ (op-Termᵉ fᵉ xᵉ) = de-bruijn-variables-term-vecᵉ xᵉ

  de-bruijn-variables-term-vecᵉ empty-vecᵉ = nilᵉ
  de-bruijn-variables-term-vecᵉ (xᵉ ∷ᵉ vᵉ) =
    union-listᵉ
      has-decidable-equality-ℕᵉ
        (de-bruijn-variables-termᵉ xᵉ)
        (de-bruijn-variables-term-vecᵉ vᵉ)

  arity-termᵉ : Termᵉ → ℕᵉ
  arity-termᵉ tᵉ = length-listᵉ (de-bruijn-variables-termᵉ tᵉ)
```

### Assignment of variables

Anᵉ assignmentᵉ ofᵉ variables,ᵉ assignsᵉ eachᵉ deᵉ Bruijnᵉ variableᵉ to anᵉ elementᵉ in aᵉ
type.ᵉ

```agda
  assignmentᵉ : {l2ᵉ : Level} → (Aᵉ : UUᵉ l2ᵉ) → UUᵉ l2ᵉ
  assignmentᵉ Aᵉ = ℕᵉ → Aᵉ
```

### Evaluation of terms

Givenᵉ aᵉ modelᵉ ofᵉ aᵉ typeᵉ `A`ᵉ andᵉ anᵉ assignmentᵉ ofᵉ variables,ᵉ anyᵉ termᵉ canᵉ beᵉ
evaluatedᵉ to aᵉ concreteᵉ elementᵉ ofᵉ theᵉ typeᵉ `A`.ᵉ

```agda
  eval-termᵉ :
    {l2ᵉ : Level} → {Aᵉ : UUᵉ l2ᵉ} →
    is-modelᵉ Sgᵉ Aᵉ → assignmentᵉ Aᵉ → Termᵉ → Aᵉ

  eval-vecᵉ :
    { l2ᵉ : Level} → {Aᵉ : UUᵉ l2ᵉ} {nᵉ : ℕᵉ} →
    is-modelᵉ Sgᵉ Aᵉ → assignmentᵉ Aᵉ → vecᵉ Termᵉ nᵉ → vecᵉ Aᵉ nᵉ

  eval-termᵉ mᵉ assignᵉ (var-Termᵉ nᵉ) = assignᵉ nᵉ
  eval-termᵉ mᵉ assignᵉ (op-Termᵉ fᵉ xᵉ) = mᵉ fᵉ (eval-vecᵉ mᵉ assignᵉ xᵉ)

  eval-vecᵉ mᵉ assignᵉ empty-vecᵉ = empty-vecᵉ
  eval-vecᵉ mᵉ assignᵉ (xᵉ ∷ᵉ vᵉ) =
    eval-termᵉ mᵉ assignᵉ xᵉ ∷ᵉ (eval-vecᵉ mᵉ assignᵉ vᵉ)

  eval-vec-map-vec-eval-termᵉ :
    { l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} {nᵉ : ℕᵉ} →
    (mᵉ : is-modelᵉ Sgᵉ Aᵉ) → (assignᵉ : assignmentᵉ Aᵉ) → (vᵉ : vecᵉ Termᵉ nᵉ) →
    eval-vecᵉ mᵉ assignᵉ vᵉ ＝ᵉ map-vecᵉ (eval-termᵉ mᵉ assignᵉ) vᵉ
  eval-vec-map-vec-eval-termᵉ mᵉ assignᵉ empty-vecᵉ = reflᵉ
  eval-vec-map-vec-eval-termᵉ mᵉ assignᵉ (xᵉ ∷ᵉ vᵉ) =
    apᵉ (eval-termᵉ mᵉ assignᵉ xᵉ ∷ᵉ_) (eval-vec-map-vec-eval-termᵉ mᵉ assignᵉ vᵉ)
```

### Evaluation for constant terms

Ifᵉ aᵉ termᵉ `t`ᵉ usesᵉ noᵉ variables,ᵉ thenᵉ anyᵉ modelᵉ onᵉ aᵉ typeᵉ `A`ᵉ assignsᵉ `t`ᵉ to anᵉ
elementᵉ ofᵉ `A`.ᵉ

```agda
  eval-constant-termᵉ :
    { l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} →
    ( is-modelᵉ Sgᵉ Aᵉ) →
    ( tᵉ : Termᵉ) →
    (de-bruijn-variables-termᵉ tᵉ ＝ᵉ nilᵉ) →
    Aᵉ

  eval-constant-term-vecᵉ :
    { l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} {nᵉ : ℕᵉ} →
    ( is-modelᵉ Sgᵉ Aᵉ) →
    ( vᵉ : vecᵉ Termᵉ nᵉ) →
    ( all-vecᵉ (λ tᵉ → is-nil-listᵉ (de-bruijn-variables-termᵉ tᵉ)) vᵉ) →
    vecᵉ Aᵉ nᵉ

  eval-constant-termᵉ mᵉ (op-Termᵉ fᵉ xᵉ) pᵉ =
    mᵉ fᵉ (eval-constant-term-vecᵉ mᵉ xᵉ (all-vec-lemmaᵉ xᵉ pᵉ))
    where
    all-vec-lemmaᵉ :
      { nᵉ : ℕᵉ}
      ( vᵉ : vecᵉ Termᵉ nᵉ) →
      ( de-bruijn-variables-term-vecᵉ vᵉ ＝ᵉ nilᵉ) →
      all-vecᵉ (λ tᵉ → is-nil-listᵉ (de-bruijn-variables-termᵉ tᵉ)) vᵉ
    all-vec-lemmaᵉ empty-vecᵉ pᵉ = raise-starᵉ
    all-vec-lemmaᵉ (xᵉ ∷ᵉ vᵉ) pᵉ =
      pairᵉ
        ( pr1ᵉ (is-nil-lemmaᵉ pᵉ))
        ( all-vec-lemmaᵉ vᵉ (pr2ᵉ (is-nil-lemmaᵉ pᵉ)))
      where
      is-nil-lemmaᵉ =
        is-nil-union-is-nil-listᵉ
          ( has-decidable-equality-ℕᵉ)
          ( de-bruijn-variables-termᵉ xᵉ)
          ( de-bruijn-variables-term-vecᵉ vᵉ)

  eval-constant-term-vecᵉ mᵉ empty-vecᵉ pᵉ = empty-vecᵉ
  eval-constant-term-vecᵉ mᵉ (xᵉ ∷ᵉ vᵉ) (pᵉ ,ᵉ p'ᵉ) =
    eval-constant-termᵉ mᵉ xᵉ pᵉ ∷ᵉ eval-constant-term-vecᵉ mᵉ vᵉ p'ᵉ
```

### The induced function by a term on a model

```agda
  vec-assignmentᵉ :
    {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} →
    ℕᵉ → (lᵉ : listᵉ ℕᵉ) →
    vecᵉ Aᵉ (succ-ℕᵉ (length-listᵉ lᵉ)) → assignmentᵉ Aᵉ
  vec-assignmentᵉ xᵉ nilᵉ (yᵉ ∷ᵉ empty-vecᵉ) nᵉ = yᵉ
  vec-assignmentᵉ xᵉ (consᵉ x'ᵉ lᵉ) (yᵉ ∷ᵉ y'ᵉ ∷ᵉ vᵉ) nᵉ
    with
    ( has-decidable-equality-ℕᵉ xᵉ nᵉ)
  ... | inlᵉ pᵉ = yᵉ
  ... | inrᵉ pᵉ = vec-assignmentᵉ x'ᵉ lᵉ (y'ᵉ ∷ᵉ vᵉ) nᵉ

  induced-function-termᵉ :
    {l2ᵉ : Level} → {Aᵉ : UUᵉ l2ᵉ} →
    is-modelᵉ Sgᵉ Aᵉ → (tᵉ : Termᵉ) →
    vecᵉ Aᵉ (arity-termᵉ tᵉ) → Aᵉ
  induced-function-termᵉ {l2ᵉ} {Aᵉ} mᵉ tᵉ vᵉ with
    ( has-decidable-equality-listᵉ
      has-decidable-equality-ℕᵉ
      (de-bruijn-variables-termᵉ tᵉ) nilᵉ)
  ... | inlᵉ pᵉ = eval-constant-termᵉ mᵉ tᵉ pᵉ
  ... | inrᵉ pᵉ =
    eval-termᵉ mᵉ
      ( trᵉ
        ( λ nᵉ → vecᵉ Aᵉ nᵉ → assignmentᵉ Aᵉ)
        ( lenght-tail-is-nonnil-listᵉ (de-bruijn-variables-termᵉ tᵉ) pᵉ)
        ( vec-assignmentᵉ
          ( head-is-nonnil-listᵉ (de-bruijn-variables-termᵉ tᵉ) pᵉ)
          ( tail-is-nonnil-listᵉ (de-bruijn-variables-termᵉ tᵉ) pᵉ))
          ( vᵉ))
      ( tᵉ)

  assignment-vecᵉ :
    {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} →
    (lᵉ : listᵉ ℕᵉ) →
    assignmentᵉ Aᵉ →
    vecᵉ Aᵉ (length-listᵉ lᵉ)
  assignment-vecᵉ nilᵉ fᵉ = empty-vecᵉ
  assignment-vecᵉ (consᵉ xᵉ lᵉ) fᵉ = fᵉ xᵉ ∷ᵉ assignment-vecᵉ lᵉ fᵉ
```

### Translation of terms

```agda
translation-termᵉ :
  { l1ᵉ l2ᵉ : Level} →
  ( Sg1ᵉ : signatureᵉ l1ᵉ) →
  ( Sg2ᵉ : signatureᵉ l2ᵉ) →
  is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ →
  Termᵉ Sg2ᵉ → Termᵉ Sg1ᵉ

translation-vecᵉ :
  { l1ᵉ l2ᵉ : Level} →
  ( Sg1ᵉ : signatureᵉ l1ᵉ) →
  ( Sg2ᵉ : signatureᵉ l2ᵉ) →
  { nᵉ : ℕᵉ} →
  is-extension-signatureᵉ Sg1ᵉ Sg2ᵉ →
  vecᵉ (Termᵉ Sg2ᵉ) nᵉ → vecᵉ (Termᵉ Sg1ᵉ) nᵉ

translation-termᵉ Sg1ᵉ Sg2ᵉ extᵉ (var-Termᵉ xᵉ) = var-Termᵉ xᵉ
translation-termᵉ Sg1ᵉ Sg2ᵉ extᵉ (op-Termᵉ fᵉ vᵉ) =
  op-Termᵉ (emb-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ fᵉ)
    ( trᵉ (vecᵉ (Termᵉ Sg1ᵉ))
      ( arity-preserved-extension-signatureᵉ Sg1ᵉ Sg2ᵉ extᵉ fᵉ)
      ( translation-vecᵉ Sg1ᵉ Sg2ᵉ extᵉ vᵉ))

translation-vecᵉ Sg1ᵉ Sg2ᵉ extᵉ empty-vecᵉ = empty-vecᵉ
translation-vecᵉ Sg1ᵉ Sg2ᵉ extᵉ (xᵉ ∷ᵉ vᵉ) =
  ( translation-termᵉ Sg1ᵉ Sg2ᵉ extᵉ xᵉ) ∷ᵉ
    ( translation-vecᵉ Sg1ᵉ Sg2ᵉ extᵉ vᵉ)
```