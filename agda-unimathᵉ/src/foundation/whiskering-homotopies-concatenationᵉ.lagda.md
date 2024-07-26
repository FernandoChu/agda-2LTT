# Whiskering homotopies with respect to concatenation

```agda
module foundation.whiskering-homotopies-concatenationᵉ where

open import foundation-core.whiskering-homotopies-concatenationᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ andᵉ aᵉ homotopyᵉ `Kᵉ : Iᵉ ~ᵉ J`ᵉ betweenᵉ twoᵉ
homotopiesᵉ `Iᵉ Jᵉ : gᵉ ~ᵉ f`.ᵉ Theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="homotopiesᵉ with respectᵉ to concatenation"ᵉ Agda=left-whisker-concat-htpyᵉ}}
ofᵉ `H`ᵉ andᵉ `K`ᵉ isᵉ aᵉ homotopyᵉ `Hᵉ ∙hᵉ Iᵉ ~ᵉ Hᵉ ∙hᵉ J`.ᵉ Inᵉ otherᵉ words,ᵉ leftᵉ whiskeringᵉ
ofᵉ homotopiesᵉ with respectᵉ to concatenationᵉ isᵉ aᵉ
[whiskeringᵉ operation](foundation.whiskering-operations.mdᵉ)

```text
  (Hᵉ : fᵉ ~ᵉ gᵉ) {Iᵉ Jᵉ : gᵉ ~ᵉ hᵉ} → Iᵉ ~ᵉ Jᵉ → Hᵉ ∙hᵉ Iᵉ ~ᵉ Hᵉ ∙hᵉ K.ᵉ
```

Similarly,ᵉ weᵉ introduceᵉ
{{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="homotopiesᵉ with respectᵉ to concatenation"ᵉ Agda=right-whisker-concat-htpyᵉ}}
to beᵉ anᵉ operationᵉ

```text
  {Hᵉ Iᵉ : fᵉ ~ᵉ gᵉ} → Hᵉ ~ᵉ Iᵉ → (Jᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ Jᵉ ~ᵉ Iᵉ ∙hᵉ J.ᵉ
```

## Properties

### Left whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-equiv-left-whisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) {Iᵉ Jᵉ : gᵉ ~ᵉ hᵉ} →
    is-equivᵉ (left-whisker-concat-htpyᵉ Hᵉ {Iᵉ} {Jᵉ})
  is-equiv-left-whisker-concat-htpyᵉ Hᵉ =
    is-equiv-map-Π-is-fiberwise-equivᵉ
      ( λ xᵉ → is-equiv-left-whisker-concatᵉ (Hᵉ xᵉ))
```

### Right whiskering of homotopies with respect to concatenation is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-equiv-right-whisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Hᵉ Iᵉ : fᵉ ~ᵉ gᵉ} (Jᵉ : gᵉ ~ᵉ hᵉ) →
    is-equivᵉ (λ (Kᵉ : Hᵉ ~ᵉ Iᵉ) → right-whisker-concat-htpyᵉ Kᵉ Jᵉ)
  is-equiv-right-whisker-concat-htpyᵉ Jᵉ =
    is-equiv-map-Π-is-fiberwise-equivᵉ
      ( λ xᵉ → is-equiv-right-whisker-concatᵉ (Jᵉ xᵉ))
```