# The action on homotopies of functions

```agda
module foundation.action-on-homotopies-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Applyingᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
to [identifications](foundation-core.identity-types.mdᵉ) arisingᵉ fromᵉ theᵉ
[functionᵉ extensionalityᵉ axiom](foundation.function-extensionality.mdᵉ) givesᵉ usᵉ
theᵉ
{{#conceptᵉ "actionᵉ onᵉ homotopies"ᵉ Disambiguation="functions"ᵉ Agda=action-htpy-function}}.ᵉ
Forᵉ arbitraryᵉ functionsᵉ ofᵉ typeᵉ

```text
  Fᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → C.ᵉ
```

Weᵉ thusᵉ getᵉ anᵉ actionᵉ ofᵉ typeᵉ

```text
  fᵉ ~ᵉ gᵉ → Fᵉ fᵉ ＝ᵉ Fᵉ g.ᵉ
```

## Definition

### The unique functorial action of functions on homotopies

Thereᵉ isᵉ aᵉ uniqueᵉ actionᵉ ofᵉ functionsᵉ onᵉ homotopies.ᵉ Namely,ᵉ byᵉ
[homotopyᵉ induction](foundation.homotopy-induction.md),ᵉ functionᵉ homotopiesᵉ
satisfyᵉ
[theᵉ dependentᵉ universalᵉ propertyᵉ ofᵉ beingᵉ anᵉ identityᵉ system](foundation.universal-property-identity-systems.mdᵉ)
onᵉ (dependentᵉ) functionᵉ types.ᵉ Thisᵉ meansᵉ thatᵉ forᵉ everyᵉ typeᵉ familyᵉ

```text
  Cᵉ : (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → 𝒰ᵉ
```

theᵉ mapᵉ `ev-refl-htpyᵉ C`ᵉ isᵉ anᵉ equivalenceᵉ
[equivalence](foundation-core.equivalences.mdᵉ)

```text
  ev-refl-htpyᵉ Cᵉ : ((gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) → Cᵉ gᵉ Hᵉ) ≃ᵉ (Cᵉ fᵉ refl-htpy).ᵉ
```

Inᵉ particular,ᵉ applyingᵉ thisᵉ to typeᵉ familiesᵉ ofᵉ theᵉ formᵉ

```text
  gᵉ Hᵉ ↦ᵉ Fᵉ fᵉ ＝ᵉ Fᵉ gᵉ
```

with theᵉ mappingᵉ

```text
  fᵉ refl-htpyᵉ ↦ᵉ reflᵉ
```

showsᵉ thatᵉ ourᵉ actionᵉ onᵉ homotopiesᵉ isᵉ
[unique](foundation-core.contractible-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (Fᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Cᵉ)
  where

  abstract
    unique-action-htpy-functionᵉ :
      (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
      is-contrᵉ
        ( Σᵉ ( (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ~ᵉ gᵉ → Fᵉ fᵉ ＝ᵉ Fᵉ gᵉ)
            ( λ αᵉ → αᵉ fᵉ refl-htpyᵉ ＝ᵉ reflᵉ))
    unique-action-htpy-functionᵉ fᵉ =
      is-contr-map-ev-refl-htpyᵉ (λ gᵉ _ → Fᵉ fᵉ ＝ᵉ Fᵉ gᵉ) reflᵉ

  action-htpy-functionᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ᵉ gᵉ → Fᵉ fᵉ ＝ᵉ Fᵉ gᵉ
  action-htpy-functionᵉ Hᵉ = apᵉ Fᵉ (eq-htpyᵉ Hᵉ)

  compute-action-htpy-function-refl-htpyᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → action-htpy-functionᵉ refl-htpyᵉ ＝ᵉ reflᵉ
  compute-action-htpy-function-refl-htpyᵉ fᵉ =
    ap²ᵉ Fᵉ (eq-htpy-refl-htpyᵉ fᵉ)
```

## Properties

### The action on homotopies preserves concatenation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (Fᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Cᵉ)
  {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  distributive-action-htpy-function-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (H'ᵉ : gᵉ ~ᵉ hᵉ) →
    action-htpy-functionᵉ Fᵉ (Hᵉ ∙hᵉ H'ᵉ) ＝ᵉ
    action-htpy-functionᵉ Fᵉ Hᵉ ∙ᵉ action-htpy-functionᵉ Fᵉ H'ᵉ
  distributive-action-htpy-function-concat-htpyᵉ Hᵉ H'ᵉ =
    ap²ᵉ Fᵉ (eq-htpy-concat-htpyᵉ Hᵉ H'ᵉ) ∙ᵉ ap-concatᵉ Fᵉ (eq-htpyᵉ Hᵉ) (eq-htpyᵉ H'ᵉ)
```

### The action on homotopies preserves inverses

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (Fᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Cᵉ)
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-action-htpy-function-inv-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) →
    action-htpy-functionᵉ Fᵉ (inv-htpyᵉ Hᵉ) ＝ᵉ invᵉ (action-htpy-functionᵉ Fᵉ Hᵉ)
  compute-action-htpy-function-inv-htpyᵉ Hᵉ =
    ap²ᵉ Fᵉ (compute-inv-eq-htpyᵉ Hᵉ) ∙ᵉ ap-invᵉ Fᵉ (eq-htpyᵉ Hᵉ)
```