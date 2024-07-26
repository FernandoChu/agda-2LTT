# The induction principle of pushouts

```agda
module synthetic-homotopy-theory.induction-principle-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
```

</details>

## Idea

Theᵉ **inductionᵉ principleᵉ ofᵉ pushouts**ᵉ assertsᵉ thatᵉ forᵉ everyᵉ
[dependentᵉ cocone](synthetic-homotopy-theory.dependent-cocones-under-spans.mdᵉ)
ofᵉ aᵉ typeᵉ familyᵉ `P`ᵉ overᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) `c`ᵉ thereᵉ isᵉ aᵉ
sectionᵉ ofᵉ `P`ᵉ correspondingᵉ to `c`.ᵉ Moreᵉ precisely,ᵉ itᵉ assertsᵉ thatᵉ theᵉ mapᵉ

```text
  dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ : ((xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
```

hasᵉ aᵉ [section](foundation.sections.md).ᵉ

Theᵉ factᵉ thatᵉ theᵉ inductionᵉ principleᵉ ofᵉ pushoutsᵉ isᵉ
[logicallyᵉ equivalent](foundation.logical-equivalences.mdᵉ) to theᵉ
[dependentᵉ universalᵉ property](synthetic-homotopy-theory.dependent-universal-property-pushouts.mdᵉ)
ofᵉ pushoutsᵉ isᵉ shownᵉ in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).ᵉ

## Definition

### The induction principle of pushouts

```agda
induction-principle-pushoutᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} →
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  UUωᵉ
induction-principle-pushoutᵉ {Xᵉ = Xᵉ} fᵉ gᵉ cᵉ =
  {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) → sectionᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ)

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( ind-cᵉ : induction-principle-pushoutᵉ fᵉ gᵉ cᵉ)
  {lᵉ : Level} ( Pᵉ : Xᵉ → UUᵉ lᵉ)
  where

  ind-induction-principle-pushoutᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ → (xᵉ : Xᵉ) → Pᵉ xᵉ
  ind-induction-principle-pushoutᵉ = pr1ᵉ (ind-cᵉ Pᵉ)

  eq-compute-ind-induction-principle-pushoutᵉ :
    (hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ (ind-induction-principle-pushoutᵉ hᵉ) ＝ᵉ hᵉ
  eq-compute-ind-induction-principle-pushoutᵉ = pr2ᵉ (ind-cᵉ Pᵉ)

  compute-ind-induction-principle-pushoutᵉ :
    (hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ (ind-induction-principle-pushoutᵉ hᵉ))
      ( hᵉ)
  compute-ind-induction-principle-pushoutᵉ hᵉ =
    htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ (ind-induction-principle-pushoutᵉ hᵉ))
      ( hᵉ)
      ( eq-compute-ind-induction-principle-pushoutᵉ hᵉ)

  compute-horizontal-map-ind-induction-principle-pushoutᵉ :
    ( hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) (aᵉ : Aᵉ) →
    ind-induction-principle-pushoutᵉ hᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ) ＝ᵉ
    horizontal-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ aᵉ
  compute-horizontal-map-ind-induction-principle-pushoutᵉ hᵉ =
    pr1ᵉ (compute-ind-induction-principle-pushoutᵉ hᵉ)

  compute-vertical-map-ind-induction-principle-pushoutᵉ :
    ( hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) (bᵉ : Bᵉ) →
    ind-induction-principle-pushoutᵉ hᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ) ＝ᵉ
    vertical-map-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ bᵉ
  compute-vertical-map-ind-induction-principle-pushoutᵉ hᵉ =
    pr1ᵉ (pr2ᵉ (compute-ind-induction-principle-pushoutᵉ hᵉ))

  compute-glue-ind-induction-principle-pushoutᵉ :
    (hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    coherence-htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ (ind-induction-principle-pushoutᵉ hᵉ))
      ( hᵉ)
      ( compute-horizontal-map-ind-induction-principle-pushoutᵉ hᵉ)
      ( compute-vertical-map-ind-induction-principle-pushoutᵉ hᵉ)
  compute-glue-ind-induction-principle-pushoutᵉ hᵉ =
    pr2ᵉ (pr2ᵉ (compute-ind-induction-principle-pushoutᵉ hᵉ))
```