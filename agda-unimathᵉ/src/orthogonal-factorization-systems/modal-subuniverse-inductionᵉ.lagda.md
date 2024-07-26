# Modal subuniverse induction

```agda
module orthogonal-factorization-systems.modal-subuniverse-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.multivariable-sectionsᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.retractionsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [modalᵉ operator](orthogonal-factorization-systems.modal-operators.mdᵉ)
`○`ᵉ andᵉ aᵉ modalᵉ unit,ᵉ weᵉ canᵉ formᵉ theᵉ [subuniverse](foundation.subuniverses.mdᵉ)
ofᵉ modalᵉ typesᵉ asᵉ thoseᵉ typesᵉ whoseᵉ unitᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ Aᵉ **modalᵉ subuniverseᵉ inductionᵉ
principle**ᵉ forᵉ theᵉ modalityᵉ isᵉ thenᵉ aᵉ
[sectionᵉ ofᵉ mapsᵉ ofᵉ maps](foundation.multivariable-sections.mdᵉ):

```text
  multivariable-sectionᵉ (precomp-Πᵉ unit-○ᵉ Pᵉ)
```

where

```text
  precomp-Πᵉ unit-○ᵉ Pᵉ : ((x'ᵉ : ○ᵉ Xᵉ) → Pᵉ x'ᵉ) → (xᵉ : Xᵉ) → Pᵉ (unit-○ᵉ xᵉ)
```

forᵉ allᵉ familiesᵉ ofᵉ modalᵉ typesᵉ `P`ᵉ overᵉ someᵉ `○ᵉ X`.ᵉ

Noteᵉ thatᵉ forᵉ suchᵉ principlesᵉ to coincideᵉ with
[modalᵉ induction](orthogonal-factorization-systems.modal-induction.md),ᵉ theᵉ
modalityᵉ mustᵉ beᵉ idempotent.ᵉ

## Definition

### Subuniverse induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  induction-principle-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  induction-principle-subuniverse-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) (is-modal-Pᵉ : is-modal-familyᵉ unit-○ᵉ Pᵉ) →
    multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ Pᵉ)

  ind-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  ind-subuniverse-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) → is-modal-familyᵉ unit-○ᵉ Pᵉ →
    ((xᵉ : Xᵉ) → Pᵉ (unit-○ᵉ xᵉ)) → (x'ᵉ : ○ᵉ Xᵉ) → Pᵉ x'ᵉ

  compute-ind-subuniverse-modalityᵉ :
    ind-subuniverse-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-ind-subuniverse-modalityᵉ ind-○ᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) (is-modal-Pᵉ : is-modal-familyᵉ unit-○ᵉ Pᵉ) →
    (fᵉ : (xᵉ : Xᵉ) → Pᵉ (unit-○ᵉ xᵉ)) → ind-○ᵉ Pᵉ is-modal-Pᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ

  ind-induction-principle-subuniverse-modalityᵉ :
    induction-principle-subuniverse-modalityᵉ → ind-subuniverse-modalityᵉ
  ind-induction-principle-subuniverse-modalityᵉ Iᵉ Pᵉ is-modal-Pᵉ =
    map-multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ Pᵉ) (Iᵉ Pᵉ is-modal-Pᵉ)

  compute-ind-induction-principle-subuniverse-modalityᵉ :
    (Iᵉ : induction-principle-subuniverse-modalityᵉ) →
    compute-ind-subuniverse-modalityᵉ
      ( ind-induction-principle-subuniverse-modalityᵉ Iᵉ)
  compute-ind-induction-principle-subuniverse-modalityᵉ Iᵉ Pᵉ is-modal-Pᵉ =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precomp-Πᵉ unit-○ᵉ Pᵉ)
      ( Iᵉ Pᵉ is-modal-Pᵉ)
```

### Subuniverse recursion

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  recursion-principle-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  recursion-principle-subuniverse-modalityᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → is-modalᵉ unit-○ᵉ Yᵉ →
    multivariable-sectionᵉ 1 (precompᵉ {Aᵉ = Xᵉ} unit-○ᵉ Yᵉ)

  rec-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  rec-subuniverse-modalityᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → is-modalᵉ unit-○ᵉ Yᵉ → (Xᵉ → Yᵉ) → ○ᵉ Xᵉ → Yᵉ

  compute-rec-subuniverse-modalityᵉ :
    rec-subuniverse-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-rec-subuniverse-modalityᵉ rec-○ᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (is-modal-Yᵉ : is-modalᵉ unit-○ᵉ Yᵉ) →
    (fᵉ : Xᵉ → Yᵉ) → rec-○ᵉ is-modal-Yᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ

  rec-recursion-principle-subuniverse-modalityᵉ :
    recursion-principle-subuniverse-modalityᵉ → rec-subuniverse-modalityᵉ
  rec-recursion-principle-subuniverse-modalityᵉ Iᵉ {Yᵉ = Yᵉ} is-modal-Yᵉ =
    map-multivariable-sectionᵉ 1 (precompᵉ unit-○ᵉ Yᵉ) (Iᵉ is-modal-Yᵉ)

  compute-rec-recursion-principle-subuniverse-modalityᵉ :
    (Iᵉ : recursion-principle-subuniverse-modalityᵉ) →
    compute-rec-subuniverse-modalityᵉ
      ( rec-recursion-principle-subuniverse-modalityᵉ Iᵉ)
  compute-rec-recursion-principle-subuniverse-modalityᵉ Iᵉ {Yᵉ = Yᵉ} is-modal-Yᵉ =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precompᵉ unit-○ᵉ Yᵉ)
      ( Iᵉ is-modal-Yᵉ)
```

### Strong subuniverse induction

Weᵉ canᵉ weakenᵉ theᵉ assumptionᵉ thatᵉ theᵉ codomainᵉ isᵉ modalᵉ andᵉ onlyᵉ askᵉ thatᵉ theᵉ
unitᵉ hasᵉ aᵉ [retraction](foundation-core.retractions.md).ᵉ Weᵉ callᵉ thisᵉ principleᵉ
**strongᵉ subuniverseᵉ induction**.ᵉ Noteᵉ thatᵉ suchᵉ aᵉ retractionᵉ mayᵉ notᵉ in generalᵉ
beᵉ [unique](foundation-core.contractible-types.md),ᵉ andᵉ theᵉ computationalᵉ
behaviourᵉ ofᵉ thisᵉ inductionᵉ principleᵉ dependsᵉ onᵉ theᵉ choiceᵉ ofᵉ retraction.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  strong-induction-principle-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  strong-induction-principle-subuniverse-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    ((x'ᵉ : ○ᵉ Xᵉ) → retractionᵉ (unit-○ᵉ {Pᵉ x'ᵉ})) →
    multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ Pᵉ)

  strong-ind-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  strong-ind-subuniverse-modalityᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    ((x'ᵉ : ○ᵉ Xᵉ) → retractionᵉ (unit-○ᵉ {Pᵉ x'ᵉ})) →
    ((xᵉ : Xᵉ) → Pᵉ (unit-○ᵉ xᵉ)) → (x'ᵉ : ○ᵉ Xᵉ) → Pᵉ x'ᵉ

  compute-strong-ind-subuniverse-modalityᵉ :
    strong-ind-subuniverse-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-strong-ind-subuniverse-modalityᵉ ind-○ᵉ =
    {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : ○ᵉ Xᵉ → UUᵉ l1ᵉ) →
    (is-premodal-Pᵉ : (x'ᵉ : ○ᵉ Xᵉ) → retractionᵉ (unit-○ᵉ {Pᵉ x'ᵉ})) →
    (fᵉ : (xᵉ : Xᵉ) → Pᵉ (unit-○ᵉ xᵉ)) → ind-○ᵉ Pᵉ is-premodal-Pᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ

  strong-ind-strong-induction-principle-subuniverse-modalityᵉ :
    strong-induction-principle-subuniverse-modalityᵉ →
    strong-ind-subuniverse-modalityᵉ
  strong-ind-strong-induction-principle-subuniverse-modalityᵉ
    Iᵉ Pᵉ is-premodal-Pᵉ =
    map-multivariable-sectionᵉ 1 (precomp-Πᵉ unit-○ᵉ Pᵉ) (Iᵉ Pᵉ is-premodal-Pᵉ)

  compute-strong-ind-strong-induction-principle-subuniverse-modalityᵉ :
    (Iᵉ : strong-induction-principle-subuniverse-modalityᵉ) →
    compute-strong-ind-subuniverse-modalityᵉ
      ( strong-ind-strong-induction-principle-subuniverse-modalityᵉ Iᵉ)
  compute-strong-ind-strong-induction-principle-subuniverse-modalityᵉ
    Iᵉ Pᵉ is-premodal-Pᵉ =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precomp-Πᵉ unit-○ᵉ Pᵉ)
      ( Iᵉ Pᵉ is-premodal-Pᵉ)
```

### Strong subuniverse recursion

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  strong-recursion-principle-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  strong-recursion-principle-subuniverse-modalityᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → retractionᵉ (unit-○ᵉ {Yᵉ}) →
    multivariable-sectionᵉ 1 (precompᵉ {Aᵉ = Xᵉ} unit-○ᵉ Yᵉ)

  strong-rec-subuniverse-modalityᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  strong-rec-subuniverse-modalityᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → retractionᵉ (unit-○ᵉ {Yᵉ}) →
    (Xᵉ → Yᵉ) → ○ᵉ Xᵉ → Yᵉ

  compute-strong-rec-subuniverse-modalityᵉ :
    strong-rec-subuniverse-modalityᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
  compute-strong-rec-subuniverse-modalityᵉ rec-○ᵉ =
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (is-premodal-Yᵉ : retractionᵉ (unit-○ᵉ {Yᵉ})) →
    (fᵉ : Xᵉ → Yᵉ) → rec-○ᵉ is-premodal-Yᵉ fᵉ ∘ᵉ unit-○ᵉ ~ᵉ fᵉ

  strong-rec-strong-recursion-principle-subuniverse-modalityᵉ :
    strong-recursion-principle-subuniverse-modalityᵉ →
    strong-rec-subuniverse-modalityᵉ
  strong-rec-strong-recursion-principle-subuniverse-modalityᵉ
    Iᵉ {Yᵉ = Yᵉ} is-premodal-Yᵉ =
    map-multivariable-sectionᵉ 1 (precompᵉ unit-○ᵉ Yᵉ) (Iᵉ is-premodal-Yᵉ)

  compute-strong-rec-strong-recursion-principle-subuniverse-modalityᵉ :
    (Iᵉ : strong-recursion-principle-subuniverse-modalityᵉ) →
    compute-strong-rec-subuniverse-modalityᵉ
      ( strong-rec-strong-recursion-principle-subuniverse-modalityᵉ Iᵉ)
  compute-strong-rec-strong-recursion-principle-subuniverse-modalityᵉ
    Iᵉ {Yᵉ = Yᵉ} is-premodal-Yᵉ =
    is-multivariable-section-map-multivariable-sectionᵉ 1
      ( precompᵉ unit-○ᵉ Yᵉ)
      ( Iᵉ is-premodal-Yᵉ)
```

## Properties

### Subuniverse recursion from subuniverse induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  rec-subuniverse-ind-subuniverse-modalityᵉ :
    ind-subuniverse-modalityᵉ unit-○ᵉ → rec-subuniverse-modalityᵉ unit-○ᵉ
  rec-subuniverse-ind-subuniverse-modalityᵉ ind-○ᵉ {Yᵉ = Yᵉ} is-modal-Yᵉ =
    ind-○ᵉ (λ _ → Yᵉ) (λ _ → is-modal-Yᵉ)

  compute-rec-subuniverse-compute-ind-subuniverse-modalityᵉ :
    (ind-○ᵉ : ind-subuniverse-modalityᵉ unit-○ᵉ) →
    compute-ind-subuniverse-modalityᵉ unit-○ᵉ ind-○ᵉ →
    compute-rec-subuniverse-modalityᵉ unit-○ᵉ
      ( rec-subuniverse-ind-subuniverse-modalityᵉ ind-○ᵉ)
  compute-rec-subuniverse-compute-ind-subuniverse-modalityᵉ
    ind-○ᵉ compute-ind-○ᵉ {Yᵉ = Yᵉ} is-modal-Yᵉ =
      compute-ind-○ᵉ (λ _ → Yᵉ) (λ _ → is-modal-Yᵉ)

  recursion-principle-induction-principle-subuniverse-modalityᵉ :
    induction-principle-subuniverse-modalityᵉ unit-○ᵉ →
    recursion-principle-subuniverse-modalityᵉ unit-○ᵉ
  recursion-principle-induction-principle-subuniverse-modalityᵉ
    Iᵉ {Yᵉ = Yᵉ} is-modal-Yᵉ =
    Iᵉ (λ _ → Yᵉ) (λ _ → is-modal-Yᵉ)
```

### Subuniverse induction from strong subuniverse induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  ind-subuniverse-strong-ind-subuniverse-modalityᵉ :
    strong-ind-subuniverse-modalityᵉ unit-○ᵉ → ind-subuniverse-modalityᵉ unit-○ᵉ
  ind-subuniverse-strong-ind-subuniverse-modalityᵉ ind-○ᵉ Pᵉ is-modal-Pᵉ =
    ind-○ᵉ Pᵉ (retraction-is-equivᵉ ∘ᵉ is-modal-Pᵉ)

  compute-ind-subuniverse-strong-ind-subuniverse-modalityᵉ :
    (ind-○ᵉ : strong-ind-subuniverse-modalityᵉ unit-○ᵉ) →
    compute-strong-ind-subuniverse-modalityᵉ unit-○ᵉ ind-○ᵉ →
    compute-ind-subuniverse-modalityᵉ unit-○ᵉ
      ( ind-subuniverse-strong-ind-subuniverse-modalityᵉ ind-○ᵉ)
  compute-ind-subuniverse-strong-ind-subuniverse-modalityᵉ
    ind-○ᵉ compute-ind-○ᵉ Pᵉ is-modal-Pᵉ =
    compute-ind-○ᵉ Pᵉ (retraction-is-equivᵉ ∘ᵉ is-modal-Pᵉ)

  induction-principle-strong-induction-principle-subuniverse-modalityᵉ :
    strong-induction-principle-subuniverse-modalityᵉ unit-○ᵉ →
    induction-principle-subuniverse-modalityᵉ unit-○ᵉ
  induction-principle-strong-induction-principle-subuniverse-modalityᵉ
    Iᵉ Pᵉ is-modal-Pᵉ = Iᵉ Pᵉ (retraction-is-equivᵉ ∘ᵉ is-modal-Pᵉ)
```

### Subuniverse recursion from strong subuniverse recursion

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  rec-subuniverse-strong-rec-subuniverse-modalityᵉ :
    strong-rec-subuniverse-modalityᵉ unit-○ᵉ → rec-subuniverse-modalityᵉ unit-○ᵉ
  rec-subuniverse-strong-rec-subuniverse-modalityᵉ rec-○ᵉ is-modal-Yᵉ =
    rec-○ᵉ (retraction-is-equivᵉ is-modal-Yᵉ)

  compute-rec-subuniverse-strong-rec-subuniverse-modalityᵉ :
    (rec-○ᵉ : strong-rec-subuniverse-modalityᵉ unit-○ᵉ)
    (compute-rec-○ᵉ : compute-strong-rec-subuniverse-modalityᵉ unit-○ᵉ rec-○ᵉ) →
    compute-rec-subuniverse-modalityᵉ unit-○ᵉ
      ( rec-subuniverse-strong-rec-subuniverse-modalityᵉ rec-○ᵉ)
  compute-rec-subuniverse-strong-rec-subuniverse-modalityᵉ
    rec-○ᵉ compute-rec-○ᵉ is-modal-Yᵉ =
    compute-rec-○ᵉ (retraction-is-equivᵉ is-modal-Yᵉ)

  recursion-principle-strong-recursion-principle-subuniverse-modalityᵉ :
    strong-recursion-principle-subuniverse-modalityᵉ unit-○ᵉ →
    recursion-principle-subuniverse-modalityᵉ unit-○ᵉ
  recursion-principle-strong-recursion-principle-subuniverse-modalityᵉ
    Iᵉ is-modal-Yᵉ =
    Iᵉ (retraction-is-equivᵉ is-modal-Yᵉ)
```

### Subuniverse induction from modal induction

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  strong-ind-subuniverse-ind-modalityᵉ :
    ind-modalityᵉ unit-○ᵉ → strong-ind-subuniverse-modalityᵉ unit-○ᵉ
  strong-ind-subuniverse-ind-modalityᵉ ind-○ᵉ Pᵉ is-premodal-Pᵉ fᵉ x'ᵉ =
    map-retractionᵉ unit-○ᵉ (is-premodal-Pᵉ x'ᵉ) (ind-○ᵉ Pᵉ (unit-○ᵉ ∘ᵉ fᵉ) x'ᵉ)

  compute-strong-ind-subuniverse-ind-modalityᵉ :
    (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ) →
    compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ →
    compute-strong-ind-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-ind-subuniverse-ind-modalityᵉ ind-○ᵉ)
  compute-strong-ind-subuniverse-ind-modalityᵉ
    ind-○ᵉ compute-ind-○ᵉ Pᵉ is-premodal-Pᵉ fᵉ xᵉ =
    ( apᵉ
      ( map-retractionᵉ unit-○ᵉ (is-premodal-Pᵉ (unit-○ᵉ xᵉ)))
      ( compute-ind-○ᵉ Pᵉ (unit-○ᵉ ∘ᵉ fᵉ) xᵉ)) ∙ᵉ
    ( is-retraction-map-retractionᵉ unit-○ᵉ (is-premodal-Pᵉ (unit-○ᵉ xᵉ)) (fᵉ xᵉ))

  strong-induction-principle-subuniverse-induction-principle-modalityᵉ :
    induction-principle-modalityᵉ unit-○ᵉ →
    strong-induction-principle-subuniverse-modalityᵉ unit-○ᵉ
  pr1ᵉ
    ( strong-induction-principle-subuniverse-induction-principle-modalityᵉ
      Iᵉ Pᵉ is-modal-Pᵉ) =
    strong-ind-subuniverse-ind-modalityᵉ
      ( ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ) Pᵉ is-modal-Pᵉ
  pr2ᵉ
    ( strong-induction-principle-subuniverse-induction-principle-modalityᵉ
        Iᵉ Pᵉ is-modal-Pᵉ) =
    compute-strong-ind-subuniverse-ind-modalityᵉ
    ( ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ)
    ( compute-ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ)
    ( Pᵉ)
    ( is-modal-Pᵉ)

  ind-subuniverse-ind-modalityᵉ :
    ind-modalityᵉ unit-○ᵉ → ind-subuniverse-modalityᵉ unit-○ᵉ
  ind-subuniverse-ind-modalityᵉ ind-○ᵉ =
    ind-subuniverse-strong-ind-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-ind-subuniverse-ind-modalityᵉ ind-○ᵉ)

  compute-ind-subuniverse-ind-modalityᵉ :
    (ind-○ᵉ : ind-modalityᵉ unit-○ᵉ) →
    compute-ind-modalityᵉ unit-○ᵉ ind-○ᵉ →
    compute-ind-subuniverse-modalityᵉ unit-○ᵉ
      ( ind-subuniverse-ind-modalityᵉ ind-○ᵉ)
  compute-ind-subuniverse-ind-modalityᵉ ind-○ᵉ compute-ind-○ᵉ =
    compute-ind-subuniverse-strong-ind-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-ind-subuniverse-ind-modalityᵉ ind-○ᵉ)
      ( compute-strong-ind-subuniverse-ind-modalityᵉ ind-○ᵉ compute-ind-○ᵉ)

  induction-principle-subuniverse-induction-principle-modalityᵉ :
    induction-principle-modalityᵉ unit-○ᵉ →
    induction-principle-subuniverse-modalityᵉ unit-○ᵉ
  pr1ᵉ
    ( induction-principle-subuniverse-induction-principle-modalityᵉ
        Iᵉ Pᵉ is-modal-Pᵉ) =
    ind-subuniverse-ind-modalityᵉ
      ( ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( Pᵉ)
      ( is-modal-Pᵉ)
  pr2ᵉ
    ( induction-principle-subuniverse-induction-principle-modalityᵉ
        Iᵉ Pᵉ is-modal-Pᵉ) =
    compute-ind-subuniverse-ind-modalityᵉ
      ( ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( compute-ind-induction-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( Pᵉ)
      ( is-modal-Pᵉ)
```

### Subuniverse recursion from modal recursion

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {○ᵉ : operator-modalityᵉ l1ᵉ l2ᵉ}
  (unit-○ᵉ : unit-modalityᵉ ○ᵉ)
  where

  strong-rec-subuniverse-rec-modalityᵉ :
    rec-modalityᵉ unit-○ᵉ → strong-rec-subuniverse-modalityᵉ unit-○ᵉ
  strong-rec-subuniverse-rec-modalityᵉ rec-○ᵉ is-premodal-Yᵉ fᵉ x'ᵉ =
    map-retractionᵉ unit-○ᵉ (is-premodal-Yᵉ) (rec-○ᵉ (unit-○ᵉ ∘ᵉ fᵉ) x'ᵉ)

  compute-strong-rec-subuniverse-rec-modalityᵉ :
    (rec-○ᵉ : rec-modalityᵉ unit-○ᵉ) →
    compute-rec-modalityᵉ unit-○ᵉ rec-○ᵉ →
    compute-strong-rec-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-rec-subuniverse-rec-modalityᵉ rec-○ᵉ)
  compute-strong-rec-subuniverse-rec-modalityᵉ
    rec-○ᵉ compute-rec-○ᵉ is-premodal-Yᵉ fᵉ xᵉ =
    ( apᵉ
      ( map-retractionᵉ unit-○ᵉ (is-premodal-Yᵉ))
      ( compute-rec-○ᵉ (unit-○ᵉ ∘ᵉ fᵉ) xᵉ)) ∙ᵉ
    ( is-retraction-map-retractionᵉ unit-○ᵉ (is-premodal-Yᵉ) (fᵉ xᵉ))

  strong-recursion-principle-subuniverse-recursion-principle-modalityᵉ :
    recursion-principle-modalityᵉ unit-○ᵉ →
    strong-recursion-principle-subuniverse-modalityᵉ unit-○ᵉ
  pr1ᵉ
    ( strong-recursion-principle-subuniverse-recursion-principle-modalityᵉ
        Iᵉ is-premodal-Yᵉ) =
    strong-rec-subuniverse-rec-modalityᵉ
      ( rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( is-premodal-Yᵉ)
  pr2ᵉ
    ( strong-recursion-principle-subuniverse-recursion-principle-modalityᵉ
        Iᵉ is-premodal-Yᵉ) =
    compute-strong-rec-subuniverse-rec-modalityᵉ
      ( rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( compute-rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( is-premodal-Yᵉ)

  rec-subuniverse-rec-modalityᵉ :
    rec-modalityᵉ unit-○ᵉ → rec-subuniverse-modalityᵉ unit-○ᵉ
  rec-subuniverse-rec-modalityᵉ rec-○ᵉ =
    rec-subuniverse-strong-rec-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-rec-subuniverse-rec-modalityᵉ rec-○ᵉ)

  compute-rec-subuniverse-rec-modalityᵉ :
    (rec-○ᵉ : rec-modalityᵉ unit-○ᵉ) →
    compute-rec-modalityᵉ unit-○ᵉ rec-○ᵉ →
    compute-rec-subuniverse-modalityᵉ unit-○ᵉ (rec-subuniverse-rec-modalityᵉ rec-○ᵉ)
  compute-rec-subuniverse-rec-modalityᵉ rec-○ᵉ compute-rec-○ᵉ =
    compute-rec-subuniverse-strong-rec-subuniverse-modalityᵉ unit-○ᵉ
      ( strong-rec-subuniverse-rec-modalityᵉ rec-○ᵉ)
      ( compute-strong-rec-subuniverse-rec-modalityᵉ rec-○ᵉ compute-rec-○ᵉ)

  recursion-principle-subuniverse-recursion-principle-modalityᵉ :
    recursion-principle-modalityᵉ unit-○ᵉ →
    recursion-principle-subuniverse-modalityᵉ unit-○ᵉ
  pr1ᵉ
    ( recursion-principle-subuniverse-recursion-principle-modalityᵉ
        Iᵉ is-modal-Yᵉ) =
    rec-subuniverse-rec-modalityᵉ
      ( rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ) is-modal-Yᵉ
  pr2ᵉ
    ( recursion-principle-subuniverse-recursion-principle-modalityᵉ
        Iᵉ is-modal-Yᵉ) =
    compute-rec-subuniverse-rec-modalityᵉ
      ( rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( compute-rec-recursion-principle-modalityᵉ unit-○ᵉ Iᵉ)
      ( is-modal-Yᵉ)
```

## See also

-ᵉ [Modalᵉ induction](orthogonal-factorization-systems.modal-induction.mdᵉ)
-ᵉ [Reflectiveᵉ subuniverses](orthogonal-factorization-systems.reflective-subuniverses.mdᵉ)