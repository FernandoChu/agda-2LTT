# The open modalities

```agda
module orthogonal-factorization-systems.open-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.higher-modalitiesᵉ
open import orthogonal-factorization-systems.locally-small-modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.uniquely-eliminating-modalitiesᵉ
```

</details>

## Idea

Givenᵉ anyᵉ [proposition](foundation-core.propositions.mdᵉ) `Q`,ᵉ theᵉ homᵉ functorᵉ
`Qᵉ →_`ᵉ definesᵉ aᵉ
[higherᵉ modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ Weᵉ
callᵉ theseᵉ theᵉ **openᵉ modalities**.ᵉ

## Definition

```agda
operator-open-modalityᵉ :
  (lᵉ : Level) {lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) → operator-modalityᵉ lᵉ (lQᵉ ⊔ lᵉ)
operator-open-modalityᵉ lᵉ Qᵉ Xᵉ = type-Propᵉ Qᵉ → Xᵉ

locally-small-operator-open-modalityᵉ :
  (lᵉ : Level) {lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) →
  locally-small-operator-modalityᵉ lᵉ (lQᵉ ⊔ lᵉ) (lQᵉ ⊔ lᵉ)
pr1ᵉ (locally-small-operator-open-modalityᵉ lᵉ Qᵉ) = operator-open-modalityᵉ lᵉ Qᵉ
pr2ᵉ (locally-small-operator-open-modalityᵉ lᵉ Qᵉ) Xᵉ = is-locally-small'ᵉ

unit-open-modalityᵉ :
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) → unit-modalityᵉ (operator-open-modalityᵉ lᵉ Qᵉ)
unit-open-modalityᵉ Qᵉ xᵉ _ = xᵉ
```

## Properties

### The open modalities are higher modalities

```agda
module _
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ)
  where

  ind-open-modalityᵉ : ind-modalityᵉ {lᵉ} (unit-open-modalityᵉ Qᵉ)
  ind-open-modalityᵉ Pᵉ fᵉ zᵉ qᵉ =
    trᵉ Pᵉ (eq-htpyᵉ λ q'ᵉ → apᵉ zᵉ (eq-is-propᵉ (is-prop-type-Propᵉ Qᵉ))) (fᵉ (zᵉ qᵉ) qᵉ)

  compute-ind-open-modalityᵉ :
    compute-ind-modalityᵉ {lᵉ} (unit-open-modalityᵉ Qᵉ) (ind-open-modalityᵉ)
  compute-ind-open-modalityᵉ Pᵉ fᵉ aᵉ =
    eq-htpyᵉ
      ( λ qᵉ →
        apᵉ
          ( λ pᵉ → trᵉ Pᵉ pᵉ (fᵉ aᵉ qᵉ))
          ( ( apᵉ
              ( eq-htpyᵉ)
              ( eq-htpyᵉ
                ( λ _ → ap-constᵉ aᵉ (eq-is-propᵉ (is-prop-type-Propᵉ Qᵉ))))) ∙ᵉ
            ( eq-htpy-refl-htpyᵉ (λ _ → aᵉ))))

  induction-principle-open-modalityᵉ :
    induction-principle-modalityᵉ {lᵉ} (unit-open-modalityᵉ Qᵉ)
  pr1ᵉ (induction-principle-open-modalityᵉ Pᵉ) = ind-open-modalityᵉ Pᵉ
  pr2ᵉ (induction-principle-open-modalityᵉ Pᵉ) = compute-ind-open-modalityᵉ Pᵉ
```

Forᵉ [localᵉ smallness](foundation.locally-small-types.mdᵉ) with respectᵉ to theᵉ
appropriateᵉ [universeᵉ level](foundation.universe-levels.md),ᵉ weᵉ mustᵉ takeᵉ theᵉ
maximumᵉ ofᵉ `l`ᵉ andᵉ `lQ`ᵉ asᵉ ourᵉ domain.ᵉ Inᵉ practice,ᵉ thisᵉ onlyᵉ allowsᵉ `lQ`ᵉ to beᵉ
smallerᵉ thanᵉ `l`.ᵉ

```agda
module _
  (lᵉ : Level) {lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ)
  where

  is-modal-identity-types-open-modalityᵉ :
    is-modal-small-identity-typesᵉ
      ( locally-small-operator-open-modalityᵉ (lᵉ ⊔ lQᵉ) Qᵉ)
      ( unit-open-modalityᵉ Qᵉ)
  is-modal-identity-types-open-modalityᵉ Xᵉ xᵉ yᵉ =
    is-equiv-is-invertibleᵉ
      ( λ zᵉ → eq-htpyᵉ (λ qᵉ → htpy-eqᵉ (zᵉ qᵉ) qᵉ))
      ( λ zᵉ →
        eq-htpyᵉ
          ( λ qᵉ →
            ( apᵉ
              ( eq-htpyᵉ)
              ( eq-htpyᵉ
                ( λ q'ᵉ →
                  apᵉ
                    ( λ q''ᵉ → htpy-eqᵉ (zᵉ q''ᵉ) q'ᵉ)
                    ( eq-is-propᵉ (is-prop-type-Propᵉ Qᵉ))))) ∙ᵉ
            ( is-retraction-eq-htpyᵉ (zᵉ qᵉ))))
      ( is-retraction-eq-htpyᵉ)

  is-higher-modality-open-modalityᵉ :
    is-higher-modalityᵉ
      ( locally-small-operator-open-modalityᵉ (lᵉ ⊔ lQᵉ) Qᵉ)
      ( unit-open-modalityᵉ Qᵉ)
  pr1ᵉ is-higher-modality-open-modalityᵉ =
    induction-principle-open-modalityᵉ Qᵉ
  pr2ᵉ is-higher-modality-open-modalityᵉ =
    is-modal-identity-types-open-modalityᵉ

  open-higher-modalityᵉ : higher-modalityᵉ (lᵉ ⊔ lQᵉ) (lᵉ ⊔ lQᵉ)
  pr1ᵉ open-higher-modalityᵉ = locally-small-operator-open-modalityᵉ (lᵉ ⊔ lQᵉ) Qᵉ
  pr1ᵉ (pr2ᵉ open-higher-modalityᵉ) = unit-open-modalityᵉ Qᵉ
  pr2ᵉ (pr2ᵉ open-higher-modalityᵉ) = is-higher-modality-open-modalityᵉ
```

### The open modalities are uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-open-modalityᵉ :
  (lᵉ : Level) {lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) →
  is-uniquely-eliminating-modalityᵉ {lᵉ ⊔ lQᵉ} (unit-open-modalityᵉ Qᵉ)
is-uniquely-eliminating-modality-open-modalityᵉ lᵉ Qᵉ =
  is-uniquely-eliminating-higher-modalityᵉ (open-higher-modalityᵉ lᵉ Qᵉ)
```