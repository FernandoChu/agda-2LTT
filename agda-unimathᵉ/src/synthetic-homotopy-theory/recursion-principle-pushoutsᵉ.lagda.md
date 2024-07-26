# The recursion principle of pushouts

```agda
module synthetic-homotopy-theory.recursion-principle-pushoutsᵉ where
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

Theᵉ {{#conceptᵉ "recursionᵉ principleᵉ ofᵉ pushouts"ᵉ}} assertsᵉ thatᵉ forᵉ everyᵉ typeᵉ
`Y`ᵉ andᵉ [cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) onᵉ aᵉ typeᵉ
`X`,ᵉ theᵉ coconeᵉ mapᵉ

```text
  cocone-mapᵉ fᵉ gᵉ cᵉ Yᵉ : (Xᵉ → Yᵉ) → coconeᵉ fᵉ gᵉ Yᵉ
```

hasᵉ aᵉ [section](foundation.sections.md).ᵉ

## Definition

### The recursion principle of pushouts

```agda
recursion-principle-pushoutᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} →
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  UUωᵉ
recursion-principle-pushoutᵉ fᵉ gᵉ cᵉ =
  {lᵉ : Level} {Yᵉ : UUᵉ lᵉ} → sectionᵉ (cocone-mapᵉ fᵉ gᵉ {Yᵉ = Yᵉ} cᵉ)

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ lᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( rec-cᵉ : recursion-principle-pushoutᵉ fᵉ gᵉ cᵉ)
  ( Yᵉ : UUᵉ lᵉ)
  where

  rec-recursion-principle-pushoutᵉ : coconeᵉ fᵉ gᵉ Yᵉ → Xᵉ → Yᵉ
  rec-recursion-principle-pushoutᵉ = pr1ᵉ rec-cᵉ

  compute-rec-recursion-principle-pushoutᵉ :
    (hᵉ : coconeᵉ fᵉ gᵉ Yᵉ) →
    htpy-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ cᵉ (rec-recursion-principle-pushoutᵉ hᵉ))
      ( hᵉ)
  compute-rec-recursion-principle-pushoutᵉ hᵉ =
    htpy-eq-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ cᵉ (rec-recursion-principle-pushoutᵉ hᵉ))
      ( hᵉ)
      ( pr2ᵉ rec-cᵉ hᵉ)

  compute-horizontal-map-rec-recursion-principle-pushoutᵉ :
    ( hᵉ : coconeᵉ fᵉ gᵉ Yᵉ) (aᵉ : Aᵉ) →
    rec-recursion-principle-pushoutᵉ hᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ) ＝ᵉ
    horizontal-map-coconeᵉ fᵉ gᵉ hᵉ aᵉ
  compute-horizontal-map-rec-recursion-principle-pushoutᵉ hᵉ =
    pr1ᵉ (compute-rec-recursion-principle-pushoutᵉ hᵉ)

  compute-vertical-map-rec-recursion-principle-pushoutᵉ :
    ( hᵉ : coconeᵉ fᵉ gᵉ Yᵉ) (bᵉ : Bᵉ) →
    rec-recursion-principle-pushoutᵉ hᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ) ＝ᵉ
    vertical-map-coconeᵉ fᵉ gᵉ hᵉ bᵉ
  compute-vertical-map-rec-recursion-principle-pushoutᵉ hᵉ =
    pr1ᵉ (pr2ᵉ (compute-rec-recursion-principle-pushoutᵉ hᵉ))

  compute-glue-rec-recursion-principle-pushoutᵉ :
    (hᵉ : coconeᵉ fᵉ gᵉ Yᵉ) →
    statement-coherence-htpy-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ cᵉ (rec-recursion-principle-pushoutᵉ hᵉ))
      ( hᵉ)
      ( compute-horizontal-map-rec-recursion-principle-pushoutᵉ hᵉ)
      ( compute-vertical-map-rec-recursion-principle-pushoutᵉ hᵉ)
  compute-glue-rec-recursion-principle-pushoutᵉ hᵉ =
    pr2ᵉ (pr2ᵉ (compute-rec-recursion-principle-pushoutᵉ hᵉ))
```