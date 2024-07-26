# Functoriality of higher modalities

```agda
module orthogonal-factorization-systems.functoriality-higher-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.small-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import orthogonal-factorization-systems.higher-modalitiesᵉ
open import orthogonal-factorization-systems.modal-inductionᵉ
open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.modal-subuniverse-inductionᵉ
```

</details>

## Idea

Everyᵉ [higherᵉ modality](orthogonal-factorization-systems.higher-modalities.mdᵉ)
`○`ᵉ isᵉ functorial.ᵉ Givenᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`,ᵉ thereᵉ isᵉ aᵉ
[unique](foundation-core.contractible-types.mdᵉ) mapᵉ `○fᵉ : ○Aᵉ → ○B`ᵉ thatᵉ fitsᵉ
intoᵉ aᵉ [naturalᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
         fᵉ
    Xᵉ ------>ᵉ Yᵉ
    |         |
    |         |
    ∨ᵉ         ∨ᵉ
   ○ᵉ Xᵉ ---->ᵉ ○ᵉ Y.ᵉ
        ○ᵉ fᵉ
```

Thisᵉ constructionᵉ preservesᵉ [composition](foundation-core.function-types.md),ᵉ
[identifications](foundation-core.identity-types.md),ᵉ
[homotopies](foundation-core.homotopies.md),ᵉ andᵉ
[equivalences](foundation-core.equivalences.md).ᵉ

## Properties

### Action on maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} (mᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  where

  ap-map-higher-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} →
    (Xᵉ → Yᵉ) → operator-higher-modalityᵉ mᵉ Xᵉ → operator-higher-modalityᵉ mᵉ Yᵉ
  ap-map-higher-modalityᵉ =
    ap-map-ind-modalityᵉ (unit-higher-modalityᵉ mᵉ) (ind-higher-modalityᵉ mᵉ)
```

### Functoriality

```agda
module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  functoriality-higher-modalityᵉ :
    {Xᵉ Yᵉ Zᵉ : UUᵉ lᵉ} (gᵉ : Yᵉ → Zᵉ) (fᵉ : Xᵉ → Yᵉ) →
    ( ap-map-higher-modalityᵉ mᵉ gᵉ ∘ᵉ ap-map-higher-modalityᵉ mᵉ fᵉ) ~ᵉ
    ( ap-map-higher-modalityᵉ mᵉ (gᵉ ∘ᵉ fᵉ))
  functoriality-higher-modalityᵉ {Xᵉ} {Yᵉ} {Zᵉ} gᵉ fᵉ =
    ind-subuniverse-Id-higher-modalityᵉ mᵉ
      ( ap-map-higher-modalityᵉ mᵉ gᵉ ∘ᵉ ap-map-higher-modalityᵉ mᵉ fᵉ)
      ( ap-map-higher-modalityᵉ mᵉ (gᵉ ∘ᵉ fᵉ))
      ( λ xᵉ →
        ( apᵉ
          ( ap-map-higher-modalityᵉ mᵉ gᵉ)
          ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ fᵉ) xᵉ)) ∙ᵉ
        ( ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ) (fᵉ xᵉ)) ∙ᵉ
          ( invᵉ
            ( compute-rec-higher-modalityᵉ mᵉ
              ( unit-higher-modalityᵉ mᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ))
              ( xᵉ)))))
```

### Naturality of the unit of a higher modality

Forᵉ everyᵉ mapᵉ `fᵉ : Xᵉ → Y`ᵉ thereᵉ isᵉ aᵉ naturalityᵉ squareᵉ

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
  {l1ᵉ l2ᵉ : Level} (mᵉ : higher-modalityᵉ l1ᵉ l2ᵉ)
  where

  naturality-unit-higher-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) →
    ( ap-map-higher-modalityᵉ mᵉ fᵉ ∘ᵉ unit-higher-modalityᵉ mᵉ) ~ᵉ
    ( unit-higher-modalityᵉ mᵉ ∘ᵉ fᵉ)
  naturality-unit-higher-modalityᵉ =
    naturality-unit-ind-modalityᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)
      ( compute-ind-higher-modalityᵉ mᵉ)
```

```agda
  naturality-unit-higher-modality'ᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} (fᵉ : Xᵉ → Yᵉ) {xᵉ x'ᵉ : Xᵉ} →
    unit-higher-modalityᵉ mᵉ xᵉ ＝ᵉ unit-higher-modalityᵉ mᵉ x'ᵉ →
    unit-higher-modalityᵉ mᵉ (fᵉ xᵉ) ＝ᵉ unit-higher-modalityᵉ mᵉ (fᵉ x'ᵉ)
  naturality-unit-higher-modality'ᵉ =
    naturality-unit-ind-modality'ᵉ
      ( unit-higher-modalityᵉ mᵉ)
      ( ind-higher-modalityᵉ mᵉ)
      ( compute-ind-higher-modalityᵉ mᵉ)

module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  compute-naturality-unit-ind-modalityᵉ :
    {Xᵉ Yᵉ Zᵉ : UUᵉ lᵉ} (gᵉ : Yᵉ → Zᵉ) (fᵉ : Xᵉ → Yᵉ) (xᵉ : Xᵉ) →
    ( ( functoriality-higher-modalityᵉ mᵉ gᵉ fᵉ (unit-higher-modalityᵉ mᵉ xᵉ)) ∙ᵉ
      ( naturality-unit-higher-modalityᵉ mᵉ (gᵉ ∘ᵉ fᵉ) xᵉ)) ＝ᵉ
    ( ( apᵉ
        ( ap-map-higher-modalityᵉ mᵉ gᵉ)
        ( naturality-unit-higher-modalityᵉ mᵉ fᵉ xᵉ)) ∙ᵉ
      ( naturality-unit-higher-modalityᵉ mᵉ gᵉ (fᵉ xᵉ)))
  compute-naturality-unit-ind-modalityᵉ gᵉ fᵉ xᵉ =
    ( right-whisker-concatᵉ
      ( compute-ind-subuniverse-Id-higher-modalityᵉ mᵉ
        ( ap-map-higher-modalityᵉ mᵉ gᵉ ∘ᵉ ap-map-higher-modalityᵉ mᵉ fᵉ)
        ( ap-map-higher-modalityᵉ mᵉ (gᵉ ∘ᵉ fᵉ))
        ( _)
        ( xᵉ))
      ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ)) xᵉ)) ∙ᵉ
    ( assocᵉ
      ( apᵉ
        ( ap-map-higher-modalityᵉ mᵉ gᵉ)
        ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ fᵉ) xᵉ))
      ( ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ) (fᵉ xᵉ)) ∙ᵉ
        ( invᵉ
          ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ) xᵉ)))
      ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ) xᵉ)) ∙ᵉ
    ( left-whisker-concatᵉ
      ( apᵉ
        ( ap-map-higher-modalityᵉ mᵉ gᵉ)
        ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ fᵉ) xᵉ))
      ( is-section-inv-concat'ᵉ
        ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ ∘ᵉ fᵉ) xᵉ)
        ( compute-rec-higher-modalityᵉ mᵉ (unit-higher-modalityᵉ mᵉ ∘ᵉ gᵉ) (fᵉ xᵉ))))
```

### Action on homotopies

Thisᵉ definitionᵉ ofᵉ actionᵉ onᵉ [homotopies](foundation-core.homotopies.mdᵉ) isᵉ
meantᵉ to avoidᵉ using
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ Thisᵉ isᵉ leftᵉ
forᵉ futureᵉ work.ᵉ

```agda
module _
  {lᵉ : Level} (mᵉ : higher-modalityᵉ lᵉ lᵉ)
  where

  htpy-ap-higher-modalityᵉ :
    {Xᵉ Yᵉ : UUᵉ lᵉ} {fᵉ gᵉ : Xᵉ → Yᵉ} →
    fᵉ ~ᵉ gᵉ → ap-map-higher-modalityᵉ mᵉ fᵉ ~ᵉ ap-map-higher-modalityᵉ mᵉ gᵉ
  htpy-ap-higher-modalityᵉ Hᵉ x'ᵉ =
    apᵉ (λ fᵉ → ap-map-higher-modalityᵉ mᵉ fᵉ x'ᵉ) (eq-htpyᵉ Hᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ Felixwellen/DCHoTT-Agdaᵉ}}