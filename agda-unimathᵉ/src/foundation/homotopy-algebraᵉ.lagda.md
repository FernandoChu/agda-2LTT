# Homotopy algebra

```agda
module foundation.homotopy-algebraᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.whiskering-homotopies-concatenationᵉ
```

</details>

## Idea

Thisᵉ fileᵉ hasᵉ beenᵉ createdᵉ to collectᵉ operationsᵉ onᵉ andᵉ factsᵉ aboutᵉ higherᵉ
[homotopies](foundation-core.homotopies.md).ᵉ Theᵉ scopeᵉ ofᵉ thisᵉ fileᵉ isᵉ analogousᵉ
to theᵉ scopeᵉ ofᵉ theᵉ fileᵉ [pathᵉ algebra](foundation.path-algebra.md),ᵉ whichᵉ isᵉ
aboutᵉ higherᵉ identifications.ᵉ

## Definitions

### Horizontal concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {gᵉ g'ᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  horizontal-concat-htpyᵉ : ({xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ}) → fᵉ ~ᵉ f'ᵉ → gᵉ ∘ᵉ fᵉ ~ᵉ g'ᵉ ∘ᵉ f'ᵉ
  horizontal-concat-htpyᵉ Gᵉ Fᵉ = (gᵉ ·lᵉ Fᵉ) ∙hᵉ (Gᵉ ·rᵉ f'ᵉ)

  horizontal-concat-htpy'ᵉ :
    ({xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ}) → fᵉ ~ᵉ f'ᵉ → gᵉ ∘ᵉ fᵉ ~ᵉ g'ᵉ ∘ᵉ f'ᵉ
  horizontal-concat-htpy'ᵉ Gᵉ Fᵉ = (Gᵉ ·rᵉ fᵉ) ∙hᵉ (g'ᵉ ·lᵉ Fᵉ)
```

## Properties

### The two definitions of horizontal concatenation of homotopies agree

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  coh-right-unit-horizontal-concat-htpyᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {gᵉ g'ᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ}
    (Gᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ}) →
    horizontal-concat-htpyᵉ Gᵉ (refl-htpy'ᵉ fᵉ) ~ᵉ
    horizontal-concat-htpy'ᵉ Gᵉ (refl-htpy'ᵉ fᵉ)
  coh-right-unit-horizontal-concat-htpyᵉ Gᵉ = inv-htpy-right-unit-htpyᵉ

  coh-left-unit-horizontal-concat-htpyᵉ :
    {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {gᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ}
    (Fᵉ : fᵉ ~ᵉ f'ᵉ) →
    horizontal-concat-htpyᵉ (refl-htpy'ᵉ gᵉ) Fᵉ ~ᵉ
    horizontal-concat-htpy'ᵉ (refl-htpy'ᵉ gᵉ) Fᵉ
  coh-left-unit-horizontal-concat-htpyᵉ Fᵉ = right-unit-htpyᵉ
```

Forᵉ theᵉ generalᵉ case,ᵉ weᵉ mustᵉ constructᵉ aᵉ coherenceᵉ ofᵉ theᵉ squareᵉ

```text
            gᵉ ·rᵉ Fᵉ
        gfᵉ ------->ᵉ gf'ᵉ
         |          |
  Gᵉ ·rᵉ fᵉ |          | Gᵉ ·rᵉ f'ᵉ
         ∨ᵉ          ∨ᵉ
       g'fᵉ ------>ᵉ g'f'ᵉ
           g'ᵉ ·rᵉ Fᵉ
```

butᵉ thisᵉ isᵉ anᵉ instance ofᵉ naturalityᵉ ofᵉ `G`ᵉ appliedᵉ to `F`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} {gᵉ g'ᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ}
  (Gᵉ : {xᵉ : Aᵉ} → gᵉ {xᵉ} ~ᵉ g'ᵉ {xᵉ}) (Fᵉ : fᵉ ~ᵉ f'ᵉ)
  where

  coh-horizontal-concat-htpyᵉ :
    horizontal-concat-htpy'ᵉ Gᵉ Fᵉ ~ᵉ horizontal-concat-htpyᵉ Gᵉ Fᵉ
  coh-horizontal-concat-htpyᵉ = nat-htpyᵉ Gᵉ ·rᵉ Fᵉ
```

### Eckmann-Hilton for homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Zᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ : Xᵉ → Yᵉ} {f'ᵉ g'ᵉ : Yᵉ → Zᵉ}
  where

  commutative-right-whisker-left-whisker-htpyᵉ :
    (H'ᵉ : f'ᵉ ~ᵉ g'ᵉ) (Hᵉ : fᵉ ~ᵉ gᵉ) →
    (H'ᵉ ·rᵉ fᵉ) ∙hᵉ (g'ᵉ ·lᵉ Hᵉ) ~ᵉ
    (f'ᵉ ·lᵉ Hᵉ) ∙hᵉ (H'ᵉ ·rᵉ gᵉ)
  commutative-right-whisker-left-whisker-htpyᵉ H'ᵉ Hᵉ xᵉ =
      coh-horizontal-concat-htpyᵉ H'ᵉ Hᵉ xᵉ

module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  eckmann-hilton-htpyᵉ :
    (Hᵉ Kᵉ : idᵉ {Aᵉ = Xᵉ} ~ᵉ idᵉ) →
    (Hᵉ ∙hᵉ Kᵉ) ~ᵉ (Kᵉ ∙hᵉ Hᵉ)
  eckmann-hilton-htpyᵉ Hᵉ Kᵉ =
    ( inv-htpyᵉ
      ( left-whisker-concat-htpyᵉ Hᵉ (left-unit-law-left-whisker-compᵉ Kᵉ))) ∙hᵉ
    ( commutative-right-whisker-left-whisker-htpyᵉ Hᵉ Kᵉ) ∙hᵉ
    ( right-whisker-concat-htpyᵉ (left-unit-law-left-whisker-compᵉ Kᵉ) Hᵉ)
```