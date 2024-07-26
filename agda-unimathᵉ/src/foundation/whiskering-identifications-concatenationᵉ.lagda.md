# Whiskering identifications with respect to concatenation

```agda
module foundation.whiskering-identifications-concatenationᵉ where

open import foundation-core.whiskering-identifications-concatenationᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-operationsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [identifications](foundation-core.identity-types.mdᵉ) `pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ
in aᵉ typeᵉ `A`.ᵉ Theᵉ whiskeringᵉ operationsᵉ areᵉ operationsᵉ thatᵉ takeᵉ
identificationsᵉ `pᵉ ＝ᵉ q`ᵉ to identificationsᵉ `rᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ ∙ᵉ q`ᵉ orᵉ to
identificationsᵉ `pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ r`.ᵉ

Theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="identifications"ᵉ Agda=left-whisker-concatᵉ}}
operationᵉ takesᵉ anᵉ identificationᵉ `rᵉ : zᵉ ＝ᵉ x`ᵉ andᵉ anᵉ identificationᵉ `pᵉ ＝ᵉ q`ᵉ to
anᵉ identificationᵉ `rᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ ∙ᵉ q`.ᵉ Similarly,ᵉ theᵉ
{{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="identifications"ᵉ Agda=right-whisker-concatᵉ}}
operationᵉ takesᵉ anᵉ identificationᵉ `rᵉ : yᵉ ＝ᵉ z`ᵉ andᵉ anᵉ identificationᵉ `pᵉ ＝ᵉ q`ᵉ to
anᵉ identificationᵉ `pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ r`.ᵉ

Theᵉ whiskeringᵉ operationsᵉ canᵉ beᵉ definedᵉ byᵉ theᵉ
[acionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ) ofᵉ
concatenation.ᵉ Sinceᵉ concatenationᵉ onᵉ eitherᵉ sideᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md),ᵉ itᵉ followsᵉ thatᵉ theᵉ whiskeringᵉ
operationsᵉ areᵉ equivalences.ᵉ

## Properties

### Left whiskering of identifications is an equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ q'ᵉ : yᵉ ＝ᵉ zᵉ}
  where

  is-equiv-left-whisker-concatᵉ :
    is-equivᵉ (left-whisker-concatᵉ pᵉ {qᵉ} {q'ᵉ})
  is-equiv-left-whisker-concatᵉ =
    is-emb-is-equivᵉ (is-equiv-concatᵉ pᵉ zᵉ) qᵉ q'ᵉ

  equiv-left-whisker-concatᵉ : (qᵉ ＝ᵉ q'ᵉ) ≃ᵉ (pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ q'ᵉ)
  pr1ᵉ equiv-left-whisker-concatᵉ =
    left-whisker-concatᵉ pᵉ
  pr2ᵉ equiv-left-whisker-concatᵉ =
    is-equiv-left-whisker-concatᵉ
```

### Right whiskering of identification is an equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ)
  where

  is-equiv-right-whisker-concatᵉ :
    is-equivᵉ (λ (αᵉ : pᵉ ＝ᵉ p'ᵉ) → right-whisker-concatᵉ αᵉ qᵉ)
  is-equiv-right-whisker-concatᵉ =
    is-emb-is-equivᵉ (is-equiv-concat'ᵉ xᵉ qᵉ) pᵉ p'ᵉ

  equiv-right-whisker-concatᵉ : (pᵉ ＝ᵉ p'ᵉ) ≃ᵉ (pᵉ ∙ᵉ qᵉ ＝ᵉ p'ᵉ ∙ᵉ qᵉ)
  pr1ᵉ equiv-right-whisker-concatᵉ αᵉ =
    right-whisker-concatᵉ αᵉ qᵉ
  pr2ᵉ equiv-right-whisker-concatᵉ =
    is-equiv-right-whisker-concatᵉ
```