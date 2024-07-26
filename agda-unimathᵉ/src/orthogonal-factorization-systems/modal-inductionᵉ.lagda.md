# Modal induction

```agda
module orthogonal-factorization-systems.modal-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.multivariable-sectionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ)
`○`ᵉ andᵉ aᵉ modalᵉ unit,ᵉ aᵉ **modalᵉ inductionᵉ principle**ᵉ forᵉ theᵉ modalityᵉ isᵉ aᵉ
[sectionᵉ ofᵉ mapsᵉ ofᵉ maps](foundation.multivariable-sections.mdᵉ):

```text
  multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ))
```

where

```text
  precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ) : ((x'ᵉ : ○ᵉ Xᵉ) → ○ᵉ (Pᵉ x'ᵉ)) → (xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))
```

forᵉ allᵉ familiesᵉ `P`ᵉ overᵉ someᵉ `○ᵉ X`.ᵉ

Noteᵉ thatᵉ forᵉ suchᵉ principlesᵉ to coincideᵉ with
[modalᵉ subuniverseᵉ induction](orthogonal-factorization-systems.modal-subuniverse-induction.md),ᵉ
theᵉ modalityᵉ mustᵉ beᵉ idempotent.ᵉ

## Definition

### Modal induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  ind-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  ind-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    ((xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) →
    (x'ᵉ : ○ᵉ Xᵉ) → ○ᵉ (Pᵉ x'ᵉ)

  compute-ind-modalityᵉ : ind-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-ind-modalityᵉ ind-○ᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    (fᵉ : (xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) →
    (xᵉ : Xᵉ) → ind-○ᵉ Pᵉ fᵉ (unit-○ᵉ xᵉ) ＝ᵉ fᵉ xᵉ

  induction-principle-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  induction-principle-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ))

  ind-induction-principle-modalityᵉ : induction-principle-modalityᵉ → ind-modalityᵉ
  ind-induction-principle-modalityᵉ Iᵉ Pᵉ =
    map-multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ)) (Iᵉ Pᵉ)

  compute-ind-induction-principle-modalityᵉ :
    (Iᵉ : induction-principle-modalityᵉ) →
    compute-ind-modalityᵉ (ind-induction-principle-modalityᵉ Iᵉ)
  compute-ind-induction-principle-modalityᵉ Iᵉ Pᵉ =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ))
      ( Iᵉ Pᵉ)
```

### Modal recursion

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  rec-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  rec-modalityᵉ = {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ → ○ᵉ Yᵉ) → ○ᵉ Xᵉ → ○ᵉ Yᵉ

  compute-rec-modalityᵉ : rec-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-rec-modalityᵉ rec-○ᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} →
    (fᵉ : Xᵉ → ○ᵉ Yᵉ) →
    (xᵉ : Xᵉ) → rec-○ᵉ fᵉ (unit-○ᵉ xᵉ) ＝ᵉ fᵉ xᵉ

  recursion-principle-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  recursion-principle-modalityᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → multivariable-sectionᵉ 1 (precompᵉ {Aᵉ = Xᵉ} unit-○ᵉ (○ᵉ Yᵉ))

  rec-recursion-principle-modalityᵉ : recursion-principle-modalityᵉ → rec-modalityᵉ
  rec-recursion-principle-modalityᵉ Iᵉ {Yᵉ = Yᵉ} =
    map-multivariable-sectionᵉ 1 (precompᵉ unit-○ᵉ (○ᵉ Yᵉ)) Iᵉ

  compute-rec-recursion-principle-modalityᵉ :
    (Iᵉ : recursion-principle-modalityᵉ) →
    compute-rec-modalityᵉ (rec-recursion-principle-modalityᵉ Iᵉ)
  compute-rec-recursion-principle-modalityᵉ Iᵉ {Yᵉ = Yᵉ} =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precompᵉ unit-○ᵉ (○ᵉ Yᵉ)) Iᵉ
```

## Properties

### Modal recursion from induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  rec-ind-modalityᵉ : ind-modalityᵉ unit-○ᵉ → rec-modalityᵉ unit-○ᵉ
  rec-ind-modalityᵉ indᵉ {Yᵉ = Yᵉ} = indᵉ (λ _ → Yᵉ)

  compute-rec-compute-ind-modalityᵉ :
    (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ) →
    compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ →
    compute-rec-modalityᵉ unit-○ᵉ (rec-ind-modalityᵉ ind-○ᵉ)
  compute-rec-compute-ind-modalityᵉ ind-○ᵉ compute-ind-○ᵉ {Yᵉ = Yᵉ} =
    compute-ind-○ᵉ (λ _ → Yᵉ)

  recursion-principle-induction-principle-modalityᵉ :
    induction-principle-modalityᵉ unit-○ᵉ → recursion-principle-modalityᵉ unit-○ᵉ
  recursion-principle-induction-principle-modalityᵉ Iᵉ {Yᵉ = Yᵉ} = Iᵉ (λ _ → Yᵉ)
```

### Modal induction gives an inverse to the unit

```agda
is-section-ind-modalityᵉ :
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ)
  (compute-ind-○ᵉ : compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
  {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ} → (precomp-Πᵉ unit-○ᵉ (○ᵉ ∘ᵉ Pᵉ) ∘ᵉ ind-○ᵉ Pᵉ) ~ᵉ idᵉ
is-section-ind-modalityᵉ unit-○ᵉ ind-○ᵉ compute-ind-○ᵉ {Xᵉ} {Pᵉ} =
  eq-htpyᵉ ∘ᵉ compute-ind-○ᵉ Pᵉ

is-retraction-ind-id-modalityᵉ :
  {lᵉ : Level}
  {○ᵉ : operator-modalityᵉ lᵉ lᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ)
  (compute-ind-○ᵉ : compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
  {Xᵉ : UUᵉ lᵉ} → (ind-○ᵉ (λ _ → Xᵉ) idᵉ ∘ᵉ unit-○ᵉ) ~ᵉ idᵉ
is-retraction-ind-id-modalityᵉ {○ᵉ = ○ᵉ} unit-○ᵉ ind-○ᵉ compute-ind-○ᵉ {Xᵉ} =
  compute-ind-○ᵉ (λ _ → Xᵉ) idᵉ

module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (rec-○ᵉ : rec-modalityᵉ unit-○ᵉ)
  (compute-rec-○ᵉ : compute-rec-modalityᵉ unit-○ᵉ rec-○ᵉ)
  where

  is-retraction-rec-map-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : ○ᵉ Xᵉ → Yᵉ) (rᵉ : retractionᵉ fᵉ) →
    (rec-○ᵉ (map-retractionᵉ fᵉ rᵉ) ∘ᵉ (unit-○ᵉ ∘ᵉ fᵉ)) ~ᵉ idᵉ
  is-retraction-rec-map-modalityᵉ {Xᵉ} {Yᵉ} fᵉ rᵉ =
    ( compute-rec-○ᵉ (map-retractionᵉ fᵉ rᵉ) ∘ᵉ fᵉ) ∙hᵉ
    ( is-retraction-map-retractionᵉ fᵉ rᵉ)

  retraction-rec-map-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : ○ᵉ Xᵉ → Yᵉ) →
    retractionᵉ fᵉ → retractionᵉ (unit-○ᵉ ∘ᵉ fᵉ)
  pr1ᵉ (retraction-rec-map-modalityᵉ {Xᵉ} {Yᵉ} fᵉ rᵉ) = rec-○ᵉ (map-retractionᵉ fᵉ rᵉ)
  pr2ᵉ (retraction-rec-map-modalityᵉ fᵉ rᵉ) = is-retraction-rec-map-modalityᵉ fᵉ rᵉ

  section-rec-map-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → ○ᵉ Yᵉ) →
    sectionᵉ fᵉ → sectionᵉ (rec-○ᵉ fᵉ)
  pr1ᵉ (section-rec-map-modalityᵉ fᵉ sᵉ) = unit-○ᵉ ∘ᵉ map-sectionᵉ fᵉ sᵉ
  pr2ᵉ (section-rec-map-modalityᵉ {Xᵉ} {Yᵉ} fᵉ sᵉ) =
    (compute-rec-○ᵉ fᵉ ∘ᵉ map-sectionᵉ fᵉ sᵉ) ∙hᵉ is-section-map-sectionᵉ fᵉ sᵉ
```

### A modal induction principle consists precisely of an induction rule and a computation rule

```agda
equiv-section-unit-induction-principle-modalityᵉ :
  { l1ᵉ l2ᵉ : Level}
  { ○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  ( unit-○ᵉ : unit-modalityᵉ ○ᵉ) →
  ( induction-principle-modalityᵉ unit-○ᵉ) ≃ᵉ
  Σᵉ ( {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
      ((xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) → (x'ᵉ : ○ᵉ Xᵉ) → ○ᵉ (Pᵉ x'ᵉ))
    ( λ Iᵉ →
      {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) (fᵉ : (xᵉ : Xᵉ) → ○ᵉ (Pᵉ (unit-○ᵉ xᵉ))) →
      Iᵉ Pᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ)
equiv-section-unit-induction-principle-modalityᵉ unit-○ᵉ =
  distributive-implicit-Π-Σᵉ ∘eᵉ
  equiv-implicit-Π-equiv-familyᵉ (λ _ → distributive-Π-Σᵉ)

equiv-section-unit-recursion-principle-modalityᵉ :
  { l1ᵉ l2ᵉ : Level}
  { ○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  ( unit-○ᵉ : unit-modalityᵉ ○ᵉ) →
  ( recursion-principle-modalityᵉ unit-○ᵉ) ≃ᵉ
    Σᵉ ( {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ → ○ᵉ Yᵉ) → ○ᵉ Xᵉ → ○ᵉ Yᵉ)
    ( λ Iᵉ → {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → ○ᵉ Yᵉ) → Iᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ)
equiv-section-unit-recursion-principle-modalityᵉ unit-○ᵉ =
  distributive-implicit-Π-Σᵉ ∘eᵉ
  equiv-implicit-Π-equiv-familyᵉ (λ _ → distributive-implicit-Π-Σᵉ)
```

### The modal operator's action on maps

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  ap-map-rec-modalityᵉ :
    rec-modalityᵉ unit-○ᵉ → {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ → Yᵉ) → ○ᵉ Xᵉ → ○ᵉ Yᵉ
  ap-map-rec-modalityᵉ rec-○ᵉ fᵉ = rec-○ᵉ (unit-○ᵉ ∘ᵉ fᵉ)

  ap-map-ind-modalityᵉ :
    ind-modalityᵉ unit-○ᵉ → {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ → Yᵉ) → ○ᵉ Xᵉ → ○ᵉ Yᵉ
  ap-map-ind-modalityᵉ ind-○ᵉ =
    ap-map-rec-modalityᵉ (rec-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
```

### Naturality of the unit

Forᵉ everyᵉ `fᵉ : Xᵉ → Y`ᵉ thereᵉ isᵉ anᵉ associatedᵉ
[naturalityᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
         fᵉ
    Xᵉ ------>ᵉ Yᵉ
    |         |
    |         |
    ∨ᵉ         ∨ᵉ
   ○ᵉ Xᵉ ---->ᵉ ○ᵉ Y.ᵉ
        ○ᵉ fᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (rec-○ᵉ : rec-modalityᵉ unit-○ᵉ)
  (compute-rec-○ᵉ : compute-rec-modalityᵉ unit-○ᵉ rec-○ᵉ)
  where

  naturality-unit-rec-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) →
    (ap-map-rec-modalityᵉ unit-○ᵉ rec-○ᵉ fᵉ ∘ᵉ unit-○ᵉ) ~ᵉ (unit-○ᵉ ∘ᵉ fᵉ)
  naturality-unit-rec-modalityᵉ fᵉ =
    compute-rec-○ᵉ (unit-○ᵉ ∘ᵉ fᵉ)

  naturality-unit-rec-modality'ᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) {xᵉ x'ᵉ : Xᵉ} →
    unit-○ᵉ xᵉ ＝ᵉ unit-○ᵉ x'ᵉ → unit-○ᵉ (fᵉ xᵉ) ＝ᵉ unit-○ᵉ (fᵉ x'ᵉ)
  naturality-unit-rec-modality'ᵉ fᵉ {xᵉ} {x'ᵉ} pᵉ =
    ( invᵉ (naturality-unit-rec-modalityᵉ fᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ (ap-map-rec-modalityᵉ unit-○ᵉ rec-○ᵉ fᵉ) pᵉ) ∙ᵉ
      ( naturality-unit-rec-modalityᵉ fᵉ x'ᵉ))

module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ)
  (compute-ind-○ᵉ : compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
  where

  naturality-unit-ind-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) →
    ap-map-ind-modalityᵉ unit-○ᵉ ind-○ᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ unit-○ᵉ ∘ᵉ fᵉ
  naturality-unit-ind-modalityᵉ =
    naturality-unit-rec-modalityᵉ unit-○ᵉ
      ( rec-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
      ( compute-rec-compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ compute-ind-○ᵉ)

  naturality-unit-ind-modality'ᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) {xᵉ x'ᵉ : Xᵉ} →
    unit-○ᵉ xᵉ ＝ᵉ unit-○ᵉ x'ᵉ → unit-○ᵉ (fᵉ xᵉ) ＝ᵉ unit-○ᵉ (fᵉ x'ᵉ)
  naturality-unit-ind-modality'ᵉ =
    naturality-unit-rec-modality'ᵉ unit-○ᵉ
      ( rec-ind-modalityᵉ unit-○ᵉ ind-○ᵉ)
      ( compute-rec-compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ compute-ind-○ᵉ)
```

## See also

-ᵉ [Functorialityᵉ ofᵉ higherᵉ modalities](orthogonal-factorization-systems.functoriality-higher-modalities.mdᵉ)
-ᵉ [Modalᵉ subuniverseᵉ induction](orthogonal-factorization-systems.modal-subuniverse-induction.mdᵉ)