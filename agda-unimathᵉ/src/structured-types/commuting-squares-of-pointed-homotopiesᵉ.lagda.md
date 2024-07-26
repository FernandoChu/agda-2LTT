# Commuting squares of pointed homotopies

```agda
module structured-types.commuting-squares-of-pointed-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import structured-types.pointed-2-homotopiesᵉ
open import structured-types.pointed-dependent-functionsᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ [pointedᵉ homotopies](structured-types.pointed-homotopies.mdᵉ)

```text
          topᵉ
      fᵉ ------>ᵉ gᵉ
      |         |
 leftᵉ |         | rightᵉ
      ∨ᵉ         ∨ᵉ
      hᵉ ------>ᵉ iᵉ
        bottomᵉ
```

isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="pointedᵉ homotopies"ᵉ Agda=coherence-square-pointed-homotopiesᵉ}}
ofᵉ pointedᵉ homotopiesᵉ ifᵉ thereᵉ isᵉ aᵉ pointedᵉ homotopyᵉ
`leftᵉ ∙hᵉ bottomᵉ ~∗ᵉ topᵉ ∙hᵉ rightᵉ `.ᵉ Suchᵉ aᵉ pointedᵉ homotopyᵉ isᵉ calledᵉ aᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ homotopies"ᵉ Agda=coherence-square-pointed-homotopiesᵉ}}
ofᵉ theᵉ square.ᵉ

## Definitions

### Commuting squares of pointed homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Famᵉ l2ᵉ Aᵉ} {fᵉ gᵉ hᵉ iᵉ : pointed-Πᵉ Aᵉ Bᵉ}
  (topᵉ : fᵉ ~∗ᵉ gᵉ) (leftᵉ : fᵉ ~∗ᵉ hᵉ) (rightᵉ : gᵉ ~∗ᵉ iᵉ) (bottomᵉ : hᵉ ~∗ᵉ iᵉ)
  where

  coherence-square-pointed-homotopiesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-square-pointed-homotopiesᵉ =
    pointed-2-htpyᵉ
      ( concat-pointed-htpyᵉ leftᵉ bottomᵉ)
      ( concat-pointed-htpyᵉ topᵉ rightᵉ)

  coherence-square-pointed-homotopies'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-square-pointed-homotopies'ᵉ =
    pointed-2-htpyᵉ
      ( concat-pointed-htpyᵉ topᵉ rightᵉ)
      ( concat-pointed-htpyᵉ leftᵉ bottomᵉ)
```