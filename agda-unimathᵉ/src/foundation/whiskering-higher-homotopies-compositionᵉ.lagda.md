# Whiskering higher homotopies with respect to composition

```agda
module foundation.whiskering-higher-homotopies-compositionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ dependentᵉ functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ x`ᵉ equippedᵉ with twoᵉ
[homotopies](foundation-core.homotopies.mdᵉ) `Hᵉ H'ᵉ : fᵉ ~ᵉ g`,ᵉ andᵉ considerᵉ aᵉ
familyᵉ ofᵉ mapsᵉ `hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ x`.ᵉ Thenᵉ weᵉ obtainᵉ aᵉ mapᵉ

```text
  αᵉ ↦ᵉ apᵉ hᵉ ·lᵉ αᵉ : Hᵉ ~ᵉ H'ᵉ → hᵉ ·lᵉ Hᵉ ~ᵉ hᵉ ·lᵉ H'ᵉ
```

Thisᵉ operationᵉ isᵉ calledᵉ theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="`2`-homotopiesᵉ with respectᵉ to composition"ᵉ Agda=left-whisker-comp²}}.ᵉ
Alternativelyᵉ theᵉ leftᵉ whiskeringᵉ operationᵉ ofᵉ `2`-homotopiesᵉ canᵉ beᵉ definedᵉ
using theᵉ
[actionᵉ onᵉ higherᵉ identificationsᵉ ofᵉ functions](foundation.action-on-higher-identifications-functions.mdᵉ)
byᵉ

```text
  αᵉ xᵉ ↦ᵉ ap²ᵉ hᵉ (αᵉ x).ᵉ
```

Similarly,ᵉ theᵉ
{{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="2-homotopiesᵉ with respectᵉ to composition"ᵉ Agda=right-whisker-comp²ᵉ}}
isᵉ definedᵉ to beᵉ theᵉ operationᵉ

```text
  (Hᵉ ~ᵉ H'ᵉ) → (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → (Hᵉ ·rᵉ hᵉ ~ᵉ H'ᵉ ·rᵉ hᵉ)
```

givenᵉ byᵉ

```text
  αᵉ hᵉ ↦ᵉ αᵉ ·rᵉ h,ᵉ
```

forᵉ anyᵉ pairᵉ ofᵉ homotopiesᵉ `Hᵉ H'ᵉ : fᵉ ~ᵉ g`,ᵉ where
`fᵉ gᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ y`.ᵉ

## Definitions

### Left whiskering higher homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-whisker-comp²ᵉ :
    (hᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) {Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ} (αᵉ : Hᵉ ~ᵉ H'ᵉ) → hᵉ ·lᵉ Hᵉ ~ᵉ hᵉ ·lᵉ H'ᵉ
  left-whisker-comp²ᵉ hᵉ αᵉ = apᵉ hᵉ ·lᵉ αᵉ
```

### Right whiskering higher homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  {fᵉ gᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} {Hᵉ H'ᵉ : {xᵉ : Aᵉ} → fᵉ {xᵉ} ~ᵉ gᵉ {xᵉ}}
  where

  right-whisker-comp²ᵉ :
    (αᵉ : {xᵉ : Aᵉ} → Hᵉ {xᵉ} ~ᵉ H'ᵉ {xᵉ}) (hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → Hᵉ ·rᵉ hᵉ ~ᵉ H'ᵉ ·rᵉ hᵉ
  right-whisker-comp²ᵉ αᵉ hᵉ = αᵉ ·rᵉ hᵉ
```

### Double whiskering higher homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ} {Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l4ᵉ}
  {fᵉ gᵉ : {xᵉ : Aᵉ} (yᵉ : Bᵉ xᵉ) → Cᵉ xᵉ yᵉ} {Hᵉ H'ᵉ : {xᵉ : Aᵉ} → fᵉ {xᵉ} ~ᵉ gᵉ {xᵉ}}
  where

  double-whisker-comp²ᵉ :
    (leftᵉ : {xᵉ : Aᵉ} {yᵉ : Bᵉ xᵉ} → Cᵉ xᵉ yᵉ → Dᵉ xᵉ yᵉ)
    (αᵉ : {xᵉ : Aᵉ} → Hᵉ {xᵉ} ~ᵉ H'ᵉ {xᵉ})
    (rightᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    leftᵉ ·lᵉ Hᵉ ·rᵉ rightᵉ ~ᵉ leftᵉ ·lᵉ H'ᵉ ·rᵉ rightᵉ
  double-whisker-comp²ᵉ leftᵉ αᵉ rightᵉ = double-whisker-compᵉ (apᵉ leftᵉ) αᵉ rightᵉ
```