# Whiskering homotopies with respect to concatenation

```agda
module foundation-core.whiskering-homotopies-concatenationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-operationsᵉ

open import foundation-core.homotopiesᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
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

## Definitions

### Left whiskering of homotopies with respect to concatenation

Leftᵉ whiskeringᵉ ofᵉ homotopiesᵉ with respectᵉ to concatenationᵉ isᵉ anᵉ operationᵉ

```text
  (Hᵉ : fᵉ ~ᵉ gᵉ) {Iᵉ Jᵉ : gᵉ ~ᵉ hᵉ} → Iᵉ ~ᵉ Jᵉ → Hᵉ ∙hᵉ Iᵉ ~ᵉ Hᵉ ∙hᵉ J.ᵉ
```

Weᵉ implementᵉ theᵉ leftᵉ whiskeringᵉ operationᵉ ofᵉ homotopiesᵉ with respectᵉ to
concatenationᵉ asᵉ anᵉ instance ofᵉ aᵉ generalᵉ leftᵉ whiskeringᵉ operation.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-whisker-concat-htpyᵉ :
    left-whiskering-operationᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (_~ᵉ_) (_∙hᵉ_) (_~ᵉ_)
  left-whisker-concat-htpyᵉ Hᵉ Kᵉ xᵉ = left-whisker-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)

  left-unwhisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) {Iᵉ Jᵉ : gᵉ ~ᵉ hᵉ} → Hᵉ ∙hᵉ Iᵉ ~ᵉ Hᵉ ∙hᵉ Jᵉ → Iᵉ ~ᵉ Jᵉ
  left-unwhisker-concat-htpyᵉ Hᵉ Kᵉ xᵉ = left-unwhisker-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)
```

### Right whiskering of homotopies with respect to concatenation

Rightᵉ whiskeringᵉ ofᵉ homotopiesᵉ with respectᵉ to concatenationᵉ isᵉ anᵉ operationᵉ

```text
  {Hᵉ Iᵉ : fᵉ ~ᵉ gᵉ} → Hᵉ ~ᵉ Iᵉ → (Jᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ Jᵉ ~ᵉ Iᵉ ∙hᵉ J.ᵉ
```

Weᵉ implementᵉ theᵉ rightᵉ whiskeringᵉ operationᵉ ofᵉ homotopiesᵉ with respectᵉ to
concatenationᵉ asᵉ anᵉ instance ofᵉ aᵉ generalᵉ rightᵉ whiskeringᵉ operation.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  right-whisker-concat-htpyᵉ :
    right-whiskering-operationᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (_~ᵉ_) (_∙hᵉ_) (_~ᵉ_)
  right-whisker-concat-htpyᵉ Kᵉ Jᵉ xᵉ = right-whisker-concatᵉ (Kᵉ xᵉ) (Jᵉ xᵉ)

  right-unwhisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Hᵉ Iᵉ : fᵉ ~ᵉ gᵉ} (Jᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ Jᵉ ~ᵉ Iᵉ ∙hᵉ Jᵉ → Hᵉ ~ᵉ Iᵉ
  right-unwhisker-concat-htpyᵉ Hᵉ Kᵉ xᵉ = right-unwhisker-concatᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)
```

## Properties

### The unit and absorption laws for left whiskering of homotopies with respect to concatenation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-unit-law-left-whisker-concat-htpyᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Iᵉ Jᵉ : fᵉ ~ᵉ gᵉ} (Kᵉ : Iᵉ ~ᵉ Jᵉ) →
    left-whisker-concat-htpyᵉ refl-htpyᵉ Kᵉ ~ᵉ Kᵉ
  left-unit-law-left-whisker-concat-htpyᵉ Kᵉ xᵉ =
    left-unit-law-left-whisker-concatᵉ (Kᵉ xᵉ)

  right-absorption-law-left-whisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) {Iᵉ : gᵉ ~ᵉ hᵉ} →
    left-whisker-concat-htpyᵉ Hᵉ (refl-htpy'ᵉ Iᵉ) ~ᵉ refl-htpyᵉ
  right-absorption-law-left-whisker-concat-htpyᵉ Hᵉ xᵉ =
    right-absorption-law-left-whisker-concatᵉ (Hᵉ xᵉ) _
```

### The unit and absorption laws for right whiskering of homotopies with respect to concatenation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-absorption-law-right-whisker-concat-htpyᵉ :
    {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Hᵉ : fᵉ ~ᵉ gᵉ} (Jᵉ : gᵉ ~ᵉ hᵉ) →
    right-whisker-concat-htpyᵉ (refl-htpy'ᵉ Hᵉ) Jᵉ ~ᵉ refl-htpyᵉ
  left-absorption-law-right-whisker-concat-htpyᵉ Jᵉ xᵉ =
    left-absorption-law-right-whisker-concatᵉ _ (Jᵉ xᵉ)

  right-unit-law-right-whisker-concat-htpyᵉ :
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {Iᵉ Jᵉ : fᵉ ~ᵉ gᵉ} (Kᵉ : Iᵉ ~ᵉ Jᵉ) →
    right-unit-htpyᵉ ∙hᵉ Kᵉ ~ᵉ
    right-whisker-concat-htpyᵉ Kᵉ refl-htpyᵉ ∙hᵉ right-unit-htpyᵉ
  right-unit-law-right-whisker-concat-htpyᵉ Kᵉ xᵉ =
    right-unit-law-right-whisker-concatᵉ (Kᵉ xᵉ)
```