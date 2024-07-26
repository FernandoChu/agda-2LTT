# Whiskering operations

```agda
module foundation.whiskering-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ with aᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ)
`Rᵉ : Aᵉ → Aᵉ → 𝒰`,ᵉ whichᵉ comesᵉ equippedᵉ with aᵉ multiplicativeᵉ operationᵉ

```text
  μᵉ : (xᵉ yᵉ zᵉ : Aᵉ) → Rᵉ xᵉ yᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ z.ᵉ
```

Furthermore,ᵉ assumeᵉ thatᵉ eachᵉ `Rᵉ xᵉ y`ᵉ comesᵉ equippedᵉ with aᵉ furtherᵉ binaryᵉ
relationᵉ `Eᵉ : Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → 𝒰`.ᵉ Aᵉ
{{#conceptᵉ "leftᵉ whiskeringᵉ operation"ᵉ Agda=left-whiskering-operationᵉ}} onᵉ `E`ᵉ
with respectᵉ to `μ`ᵉ isᵉ anᵉ operationᵉ

```text
  (fᵉ : Rᵉ xᵉ yᵉ) {gᵉ hᵉ : Rᵉ yᵉ zᵉ} → Eᵉ gᵉ hᵉ → Eᵉ (μᵉ fᵉ gᵉ) (μᵉ fᵉ h).ᵉ
```

Similarly,ᵉ aᵉ
{{#conceptᵉ "rightᵉ whiskeringᵉ operation"ᵉ Agda=right-whiskering-operationᵉ}} onᵉ `E`ᵉ
with respectᵉ to `μ`ᵉ isᵉ anᵉ operationᵉ

```text
  {gᵉ hᵉ : Rᵉ xᵉ yᵉ} → Eᵉ gᵉ hᵉ → (fᵉ : Rᵉ yᵉ zᵉ) → Eᵉ (μᵉ gᵉ fᵉ) (μᵉ hᵉ f).ᵉ
```

Theᵉ generalᵉ notionᵉ ofᵉ whiskeringᵉ isᵉ introducedᵉ in orderᵉ to establishᵉ aᵉ clearᵉ
namingᵉ schemeᵉ forᵉ allᵉ theᵉ variationsᵉ ofᵉ whiskeringᵉ thatᵉ existᵉ in theᵉ
`agda-unimath`ᵉ libraryᵉ:

1.ᵉ Inᵉ
   [whiskeringᵉ identificationsᵉ with respectᵉ to concatenation](foundation.whiskering-identifications-concatenation.mdᵉ)
   weᵉ defineᵉ theᵉ whiskeringᵉ operationsᵉ

   ```text
     left-whisker-concatᵉ :
       (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} → qᵉ ＝ᵉ rᵉ → pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ rᵉ
   ```

   andᵉ

   ```text
     right-whisker-concatᵉ :
       {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ＝ᵉ qᵉ → (rᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ
   ```

   with respectᵉ to concatenationᵉ ofᵉ identifications.ᵉ

2.ᵉ Inᵉ
   [whiskeringᵉ homotopiesᵉ with respectᵉ to composition](foundation.whiskering-homotopies-composition.mdᵉ)
   weᵉ defineᵉ theᵉ whiskeringᵉ operationsᵉ

   ```text
     left-whisker-compᵉ :
       (fᵉ : Bᵉ → Cᵉ) {gᵉ hᵉ : Aᵉ → Bᵉ} → gᵉ ~ᵉ hᵉ → fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ hᵉ
   ```

   andᵉ

   ```text
     right-whisker-compᵉ :
       {fᵉ gᵉ : Bᵉ → Cᵉ} → (fᵉ ~ᵉ gᵉ) → (hᵉ : Aᵉ → Bᵉ) → fᵉ ∘ᵉ hᵉ ~ᵉ gᵉ ∘ᵉ hᵉ
   ```

   ofᵉ homotopiesᵉ with respectᵉ to compositionᵉ ofᵉ functions.ᵉ

3.ᵉ Inᵉ
   [whiskeringᵉ homotopiesᵉ with respectᵉ to concatenation](foundation.whiskering-homotopies-concatenation.mdᵉ)
   weᵉ defineᵉ theᵉ whiskeringᵉ operationsᵉ

   ```text
     left-whisker-comp-concatᵉ :
       (Hᵉ : fᵉ ~ᵉ gᵉ) {Kᵉ Lᵉ : gᵉ ~ᵉ hᵉ} → Kᵉ ~ᵉ Lᵉ → Hᵉ ∙hᵉ Kᵉ ~ᵉ Hᵉ ∙hᵉ Lᵉ
   ```

   andᵉ

   ```text
     right-whisker-comp-concatᵉ :
       {Hᵉ Kᵉ : fᵉ ~ᵉ gᵉ} → Hᵉ ~ᵉ Kᵉ → (Lᵉ : gᵉ ~ᵉ hᵉ) → Hᵉ ∙hᵉ Lᵉ ~ᵉ Kᵉ ∙hᵉ Lᵉ
   ```

   ofᵉ homotopiesᵉ with respectᵉ to concatenationᵉ ofᵉ homotopies.ᵉ

4.ᵉ Inᵉ
   [whsikeringᵉ higherᵉ homotopiesᵉ with respectᵉ to composition](foundation.whiskering-higher-homotopies-composition.mdᵉ)
   weᵉ defineᵉ theᵉ whiskeringᵉ operationsᵉ

   ```text
     left-whisker-comp²ᵉ :
       (fᵉ : Bᵉ → Cᵉ) {gᵉ hᵉ : Aᵉ → Bᵉ} {Hᵉ Kᵉ : gᵉ ~ᵉ hᵉ} → Hᵉ ~ᵉ Kᵉ → fᵉ ·lᵉ Hᵉ ~ᵉ fᵉ ·lᵉ Kᵉ
   ```

   andᵉ

   ```text
     right-whisker-comp²ᵉ :
       {fᵉ gᵉ : Bᵉ → Cᵉ} {Hᵉ Kᵉ : fᵉ ~ᵉ gᵉ} → Hᵉ ~ᵉ Kᵉ → (hᵉ : Aᵉ → Bᵉ) → Hᵉ ·rᵉ hᵉ ~ᵉ Kᵉ ·rᵉ hᵉ
   ```

   ofᵉ higherᵉ homotopiesᵉ with respectᵉ to compositionᵉ ofᵉ functions.ᵉ

## Definitions

### Left whiskering operations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Rᵉ : Aᵉ → Aᵉ → UUᵉ l2ᵉ)
  where

  left-whiskering-operationᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  left-whiskering-operationᵉ μᵉ Eᵉ =
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : Rᵉ xᵉ yᵉ) {gᵉ hᵉ : Rᵉ yᵉ zᵉ} → Eᵉ gᵉ hᵉ → Eᵉ (μᵉ fᵉ gᵉ) (μᵉ fᵉ hᵉ)

  left-whiskering-operation'ᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  left-whiskering-operation'ᵉ μᵉ Eᵉ =
    {xᵉ yᵉ zᵉ : Aᵉ} (fᵉ : Rᵉ yᵉ zᵉ) {gᵉ hᵉ : Rᵉ xᵉ yᵉ} → Eᵉ gᵉ hᵉ → Eᵉ (μᵉ fᵉ gᵉ) (μᵉ fᵉ hᵉ)
```

### Right whiskering operations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Rᵉ : Aᵉ → Aᵉ → UUᵉ l2ᵉ)
  where

  right-whiskering-operationᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  right-whiskering-operationᵉ μᵉ Eᵉ =
    {xᵉ yᵉ zᵉ : Aᵉ} {fᵉ gᵉ : Rᵉ xᵉ yᵉ} → Eᵉ fᵉ gᵉ → (hᵉ : Rᵉ yᵉ zᵉ) → Eᵉ (μᵉ fᵉ hᵉ) (μᵉ gᵉ hᵉ)

  right-whiskering-operation'ᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  right-whiskering-operation'ᵉ μᵉ Eᵉ =
    {xᵉ yᵉ zᵉ : Aᵉ} {fᵉ gᵉ : Rᵉ yᵉ zᵉ} → Eᵉ fᵉ gᵉ → (hᵉ : Rᵉ xᵉ yᵉ) → Eᵉ (μᵉ fᵉ hᵉ) (μᵉ gᵉ hᵉ)
```

### Double whiskering operations

Doubleᵉ whiskeringᵉ operationsᵉ areᵉ operationsᵉ thatᵉ simultaneouslyᵉ performᵉ
whiskeringᵉ onᵉ theᵉ leftᵉ andᵉ onᵉ theᵉ right.ᵉ

Noteᵉ thatᵉ doubleᵉ whiskeringᵉ shouldᵉ notᵉ beᵉ confusedᵉ with iteratedᵉ whiskeringᵉ onᵉ
theᵉ leftᵉ orᵉ with iteratedᵉ whiskeringᵉ onᵉ theᵉ right.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Rᵉ : Aᵉ → Aᵉ → UUᵉ l2ᵉ)
  where

  double-whiskering-operationᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ yᵉ zᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  double-whiskering-operationᵉ μᵉ Eᵉ =
    {x'ᵉ xᵉ yᵉ y'ᵉ : Aᵉ} (hᵉ : Rᵉ x'ᵉ xᵉ) {fᵉ gᵉ : Rᵉ xᵉ yᵉ} (eᵉ : Eᵉ fᵉ gᵉ) (kᵉ : Rᵉ yᵉ y'ᵉ) →
    Eᵉ (μᵉ (μᵉ hᵉ fᵉ) kᵉ) (μᵉ (μᵉ hᵉ gᵉ) kᵉ)

  double-whiskering-operation'ᵉ :
    (μᵉ : {xᵉ yᵉ zᵉ : Aᵉ} → Rᵉ yᵉ zᵉ → Rᵉ xᵉ yᵉ → Rᵉ xᵉ zᵉ) →
    ({xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  double-whiskering-operation'ᵉ μᵉ Eᵉ =
    {x'ᵉ xᵉ yᵉ y'ᵉ : Aᵉ} (hᵉ : Rᵉ yᵉ y'ᵉ) {fᵉ gᵉ : Rᵉ xᵉ yᵉ} (eᵉ : Eᵉ fᵉ gᵉ) (kᵉ : Rᵉ x'ᵉ xᵉ) →
    Eᵉ (μᵉ (μᵉ hᵉ fᵉ) kᵉ) (μᵉ (μᵉ hᵉ gᵉ) kᵉ)
```