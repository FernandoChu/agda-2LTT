# Whiskering homotopies with respect to composition

```agda
module foundation.whiskering-homotopies-compositionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Thereᵉ areᵉ twoᵉ
{{#conceptᵉ "whiskeringᵉ operations"ᵉ Disambiguation="homotopiesᵉ with respectᵉ to compostion"ᵉ}}
onᵉ [homotopies](foundation-core.homotopies.mdᵉ) with respectᵉ to composition.ᵉ Theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="homotopiesᵉ with respectᵉ to composition"ᵉ Agda=left-whisker-compᵉ}}
operationᵉ ofᵉ homotopiesᵉ with respectᵉ to compositionᵉ assumesᵉ aᵉ diagramᵉ ofᵉ mapsᵉ ofᵉ
theᵉ formᵉ

```text
      fᵉ
    ----->ᵉ     hᵉ
  Aᵉ ----->ᵉ Bᵉ ----->ᵉ Cᵉ
      gᵉ
```

andᵉ isᵉ definedᵉ to beᵉ theᵉ functionᵉ `Hᵉ ↦ᵉ hᵉ ·lᵉ Hᵉ : (fᵉ ~ᵉ gᵉ) → (hᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ g)`.ᵉ Theᵉ
{{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="homotopiesᵉ with respectᵉ to composition"ᵉ Agda=right-whisker-compᵉ}}
operationᵉ ofᵉ homotopiesᵉ with respectᵉ to compositionᵉ assumesᵉ aᵉ diagramᵉ ofᵉ mapsᵉ
theᵉ formᵉ

```text
               gᵉ
      fᵉ      ----->ᵉ
  Aᵉ ----->ᵉ Bᵉ ----->ᵉ Cᵉ
               hᵉ
```

andᵉ isᵉ definedᵉ to beᵉ theᵉ functionᵉ `Hᵉ ↦ᵉ Hᵉ ·rᵉ fᵉ : (gᵉ ~ᵉ hᵉ) → (gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ f)`.ᵉ

**Note.**ᵉ Theᵉ infix whiskeringᵉ operatorsᵉ `_·l_`ᵉ andᵉ `_·r_`ᵉ useᵉ theᵉ
[middleᵉ dot](https://codepoints.net/U+00B7ᵉ) `·`ᵉ (agda-inputᵉ: `\cdot`ᵉ
`\centerdot`),ᵉ asᵉ opposedᵉ to theᵉ infix homotopyᵉ concatenationᵉ operatorᵉ `_∙h_`ᵉ
whichᵉ usesᵉ theᵉ [bulletᵉ operator](https://codepoints.net/U+2219ᵉ) `∙`ᵉ (agda-inputᵉ:
`\.`).ᵉ Ifᵉ theseᵉ lookᵉ theᵉ sameᵉ in yourᵉ editor,ᵉ weᵉ suggestᵉ thatᵉ youᵉ changeᵉ yourᵉ
font.ᵉ Forᵉ moreᵉ details,ᵉ seeᵉ [Howᵉ to install](HOWTO-INSTALL.md).ᵉ

**Note.**ᵉ Weᵉ willᵉ defineᵉ theᵉ whiskeringᵉ operationsᵉ with respectᵉ to functionᵉ
compositionᵉ forᵉ dependentᵉ functions.ᵉ Theᵉ definitionᵉ ofᵉ `whiskering-operations`ᵉ
in [whiskeringᵉ operations](foundation.whiskering-operations.mdᵉ) doesᵉ notᵉ supportᵉ
thisᵉ levelᵉ ofᵉ generality,ᵉ soᵉ weᵉ willᵉ notᵉ beᵉ ableᵉ to useᵉ itᵉ here.ᵉ

## Definitions

### Left whiskering of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  left-whisker-compᵉ :
    (hᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ)
    {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ~ᵉ gᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ gᵉ
  left-whisker-compᵉ hᵉ Hᵉ xᵉ = apᵉ hᵉ (Hᵉ xᵉ)

  infixr 17 _·lᵉ_
  _·lᵉ_ = left-whisker-compᵉ
```

### Right whiskering of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  right-whisker-compᵉ :
    {gᵉ hᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ}
    (Hᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ hᵉ {xᵉ})
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → gᵉ ∘ᵉ fᵉ ~ᵉ hᵉ ∘ᵉ fᵉ
  right-whisker-compᵉ Hᵉ fᵉ xᵉ = Hᵉ (fᵉ xᵉ)

  infixl 16 _·rᵉ_
  _·rᵉ_ = right-whisker-compᵉ
```

### Double whiskering of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ} {Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l4ᵉ}
  where

  double-whisker-compᵉ :
    (leftᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} → Cᵉ xᵉ yᵉ → Dᵉ xᵉ yᵉ)
    {gᵉ hᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ}
    (Hᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ hᵉ {xᵉ})
    (rightᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → leftᵉ ∘ᵉ gᵉ ∘ᵉ rightᵉ ~ᵉ leftᵉ ∘ᵉ hᵉ ∘ᵉ rightᵉ
  double-whisker-compᵉ leftᵉ Hᵉ rightᵉ = leftᵉ ·lᵉ Hᵉ ·rᵉ rightᵉ
```

## Properties

### The left and right whiskering operations commute

Weᵉ haveᵉ theᵉ coherenceᵉ

```text
  (hᵉ ·lᵉ Hᵉ) ·rᵉ h'ᵉ ~ᵉ hᵉ ·lᵉ (Hᵉ ·rᵉ h'ᵉ)
```

definitionally.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {Cᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → UUᵉ l3ᵉ} {Dᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → UUᵉ l4ᵉ}
  {fᵉ gᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ yᵉ}
  where

  coherence-double-whisker-compᵉ :
    (hᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} → Cᵉ yᵉ → Dᵉ yᵉ)
    (Hᵉ : {xᵉ : Aᵉ} → fᵉ {xᵉ} ~ᵉ gᵉ {xᵉ})
    (h'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    (hᵉ ·lᵉ Hᵉ) ·rᵉ h'ᵉ ~ᵉ hᵉ ·lᵉ (Hᵉ ·rᵉ h'ᵉ)
  coherence-double-whisker-compᵉ hᵉ Hᵉ h'ᵉ = refl-htpyᵉ
```

### Unit laws and absorption laws for whiskering homotopies

Theᵉ identityᵉ mapᵉ isᵉ aᵉ _unitᵉ elementᵉ_ forᵉ whiskeringsᵉ fromᵉ theᵉ functionᵉ side,ᵉ andᵉ
theᵉ reflexivityᵉ homotopyᵉ isᵉ anᵉ _absorbingᵉ elementᵉ_ onᵉ theᵉ homotopyᵉ sideᵉ forᵉ
whiskerings.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-unit-law-left-whisker-compᵉ :
    {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ f'ᵉ) → idᵉ ·lᵉ Hᵉ ~ᵉ Hᵉ
  left-unit-law-left-whisker-compᵉ Hᵉ xᵉ = ap-idᵉ (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  right-absorption-law-left-whisker-compᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (gᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) →
    gᵉ ·lᵉ refl-htpyᵉ {fᵉ = fᵉ} ~ᵉ refl-htpyᵉ
  right-absorption-law-left-whisker-compᵉ gᵉ = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  where

  left-absorption-law-right-whisker-compᵉ :
    {gᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    refl-htpyᵉ {fᵉ = gᵉ} ·rᵉ fᵉ ~ᵉ refl-htpyᵉ
  left-absorption-law-right-whisker-compᵉ fᵉ = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  right-unit-law-right-whisker-compᵉ :
    {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ f'ᵉ) → Hᵉ ·rᵉ idᵉ ~ᵉ Hᵉ
  right-unit-law-right-whisker-compᵉ Hᵉ = refl-htpyᵉ
```

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (gᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) (Hᵉ : fᵉ ~ᵉ f'ᵉ)
  where

  left-whisker-inv-htpyᵉ : gᵉ ·lᵉ (inv-htpyᵉ Hᵉ) ~ᵉ inv-htpyᵉ (gᵉ ·lᵉ Hᵉ)
  left-whisker-inv-htpyᵉ xᵉ = ap-invᵉ gᵉ (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  {gᵉ g'ᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} (Hᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ})
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  right-whisker-inv-htpyᵉ : inv-htpyᵉ Hᵉ ·rᵉ fᵉ ~ᵉ inv-htpyᵉ (Hᵉ ·rᵉ fᵉ)
  right-whisker-inv-htpyᵉ = refl-htpyᵉ
```

### Inverse laws for whiskered homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (gᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) (Hᵉ : fᵉ ~ᵉ f'ᵉ)
  where

  left-inv-htpy-left-whiskerᵉ : gᵉ ·lᵉ (inv-htpyᵉ Hᵉ) ∙hᵉ gᵉ ·lᵉ Hᵉ ~ᵉ refl-htpyᵉ
  left-inv-htpy-left-whiskerᵉ =
    ( ap-concat-htpy'ᵉ (gᵉ ·lᵉ Hᵉ) (left-whisker-inv-htpyᵉ gᵉ Hᵉ)) ∙hᵉ
    ( left-inv-htpyᵉ (gᵉ ·lᵉ Hᵉ))

  right-inv-htpy-left-whiskerᵉ : gᵉ ·lᵉ Hᵉ ∙hᵉ gᵉ ·lᵉ (inv-htpyᵉ Hᵉ) ~ᵉ refl-htpyᵉ
  right-inv-htpy-left-whiskerᵉ =
    ( ap-concat-htpyᵉ (gᵉ ·lᵉ Hᵉ) (left-whisker-inv-htpyᵉ gᵉ Hᵉ)) ∙hᵉ
    ( right-inv-htpyᵉ (gᵉ ·lᵉ Hᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  {gᵉ g'ᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} (Hᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ})
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  where

  left-inv-htpy-right-whiskerᵉ : (inv-htpyᵉ Hᵉ) ·rᵉ fᵉ ∙hᵉ Hᵉ ·rᵉ fᵉ ~ᵉ refl-htpyᵉ
  left-inv-htpy-right-whiskerᵉ = left-inv-htpyᵉ (Hᵉ ·rᵉ fᵉ)

  right-inv-htpy-right-whiskerᵉ : Hᵉ ·rᵉ fᵉ ∙hᵉ (inv-htpyᵉ Hᵉ) ·rᵉ fᵉ ~ᵉ refl-htpyᵉ
  right-inv-htpy-right-whiskerᵉ = right-inv-htpyᵉ (Hᵉ ·rᵉ fᵉ)
```

### Distributivity of whiskering over concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  distributive-left-whisker-comp-concatᵉ :
    { fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (kᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) →
    ( Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    kᵉ ·lᵉ (Hᵉ ∙hᵉ Kᵉ) ~ᵉ (kᵉ ·lᵉ Hᵉ) ∙hᵉ (kᵉ ·lᵉ Kᵉ)
  distributive-left-whisker-comp-concatᵉ kᵉ Hᵉ Kᵉ aᵉ =
    ap-concatᵉ kᵉ (Hᵉ aᵉ) (Kᵉ aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  (kᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) {fᵉ gᵉ hᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ}
  (Hᵉ : {xᵉ : Aᵉ} → fᵉ {xᵉ} ~ᵉ gᵉ {xᵉ}) (Kᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ hᵉ {xᵉ})
  where

  distributive-right-whisker-comp-concatᵉ :
    (Hᵉ ∙hᵉ Kᵉ) ·rᵉ kᵉ ~ᵉ (Hᵉ ·rᵉ kᵉ) ∙hᵉ (Kᵉ ·rᵉ kᵉ)
  distributive-right-whisker-comp-concatᵉ = refl-htpyᵉ
```

### Whiskering preserves function composition

Inᵉ otherᵉ words,ᵉ whiskeringᵉ isᵉ anᵉ actionᵉ ofᵉ functionsᵉ onᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : Aᵉ → UUᵉ l4ᵉ}
  where

  inv-preserves-comp-left-whisker-compᵉ :
    ( kᵉ : {xᵉ : Aᵉ} → Cᵉ xᵉ → Dᵉ xᵉ) (hᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
    ( Hᵉ : fᵉ ~ᵉ gᵉ) →
    (kᵉ ∘ᵉ hᵉ) ·lᵉ Hᵉ ~ᵉ kᵉ ·lᵉ (hᵉ ·lᵉ Hᵉ)
  inv-preserves-comp-left-whisker-compᵉ kᵉ hᵉ Hᵉ xᵉ = ap-compᵉ kᵉ hᵉ (Hᵉ xᵉ)

  preserves-comp-left-whisker-compᵉ :
    ( kᵉ : {xᵉ : Aᵉ} → Cᵉ xᵉ → Dᵉ xᵉ) (hᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
    ( Hᵉ : fᵉ ~ᵉ gᵉ) →
    kᵉ ·lᵉ (hᵉ ·lᵉ Hᵉ) ~ᵉ (kᵉ ∘ᵉ hᵉ) ·lᵉ Hᵉ
  preserves-comp-left-whisker-compᵉ kᵉ hᵉ Hᵉ =
    inv-htpyᵉ (inv-preserves-comp-left-whisker-compᵉ kᵉ hᵉ Hᵉ)

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  { Dᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) (zᵉ : Cᵉ xᵉ yᵉ) → UUᵉ l4ᵉ}
  { fᵉ gᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} (zᵉ : Cᵉ xᵉ yᵉ) → Dᵉ xᵉ yᵉ zᵉ}
  ( hᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ) (kᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  ( Hᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} → fᵉ {xᵉ} {yᵉ} ~ᵉ gᵉ {xᵉ} {yᵉ})
  where

  preserves-comp-right-whisker-compᵉ : (Hᵉ ·rᵉ hᵉ) ·rᵉ kᵉ ~ᵉ Hᵉ ·rᵉ (hᵉ ∘ᵉ kᵉ)
  preserves-comp-right-whisker-compᵉ = refl-htpyᵉ
```

### A coherence for homotopies to the identity function

Considerᵉ aᵉ functionᵉ `fᵉ : Aᵉ → A`ᵉ andᵉ let `Hᵉ : fᵉ ~ᵉ id`ᵉ beᵉ aᵉ homotopyᵉ to theᵉ
identityᵉ function.ᵉ Thenᵉ weᵉ haveᵉ aᵉ homotopyᵉ

```text
  Hᵉ ·rᵉ fᵉ ~ᵉ fᵉ ·lᵉ H.ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {fᵉ : Aᵉ → Aᵉ} (Hᵉ : fᵉ ~ᵉ idᵉ)
  where

  coh-htpy-idᵉ : Hᵉ ·rᵉ fᵉ ~ᵉ fᵉ ·lᵉ Hᵉ
  coh-htpy-idᵉ xᵉ = is-injective-concat'ᵉ (Hᵉ xᵉ) (nat-htpy-idᵉ Hᵉ (Hᵉ xᵉ))

  inv-coh-htpy-idᵉ : fᵉ ·lᵉ Hᵉ ~ᵉ Hᵉ ·rᵉ fᵉ
  inv-coh-htpy-idᵉ = inv-htpyᵉ coh-htpy-idᵉ
```

## See also

-ᵉ Forᵉ interactionsᵉ betweenᵉ whiskeringᵉ andᵉ exponentiation,ᵉ seeᵉ
  [`foundation.composition-algebra`](foundation.composition-algebra.md).ᵉ