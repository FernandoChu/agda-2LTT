# Commuting triangles of pointed maps

```agda
module structured-types.commuting-triangles-of-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.whiskering-pointed-homotopies-compositionᵉ
```

</details>

## Idea

Considerᵉ aᵉ triangleᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ)

```text
           topᵉ
       Aᵉ ------>ᵉ Bᵉ
        \ᵉ       /ᵉ
    leftᵉ \ᵉ     /ᵉ rightᵉ
          \ᵉ   /ᵉ
           ∨ᵉ ∨ᵉ
            Cᵉ
```

Suchᵉ aᵉ triangleᵉ isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "commutingᵉ triangleᵉ ofᵉ pointedᵉ maps"ᵉ Agda=coherence-triangle-pointed-mapsᵉ}}
ifᵉ thereᵉ isᵉ aᵉ [pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ)

```text
  leftᵉ ~∗ᵉ rightᵉ ∘∗ᵉ top.ᵉ
```

Suchᵉ aᵉ homotopyᵉ isᵉ referredᵉ to asᵉ theᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ trianglesᵉ ofᵉ pointedᵉ maps"ᵉ Agda=coherence-triangle-pointed-mapsᵉ}}
ofᵉ theᵉ commutingᵉ triangleᵉ ofᵉ pointedᵉ maps.ᵉ

## Definitions

### Coherences of commuting triangles of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  (leftᵉ : Aᵉ →∗ᵉ Cᵉ) (rightᵉ : Bᵉ →∗ᵉ Cᵉ) (topᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  coherence-triangle-pointed-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-triangle-pointed-mapsᵉ =
    leftᵉ ~∗ᵉ rightᵉ ∘∗ᵉ topᵉ

  coherence-triangle-pointed-maps'ᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-triangle-pointed-maps'ᵉ =
    rightᵉ ∘∗ᵉ topᵉ ~∗ᵉ leftᵉ
```

## Properties

### Left whiskering of coherences of commuting triangles of pointed maps

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ pointedᵉ mapsᵉ

```text
           topᵉ
       Aᵉ ------>ᵉ Bᵉ
        \ᵉ       /ᵉ
    leftᵉ \ᵉ     /ᵉ rightᵉ
          \ᵉ   /ᵉ
           ∨ᵉ ∨ᵉ
            Cᵉ
```

andᵉ considerᵉ aᵉ pointedᵉ mapᵉ `fᵉ : Cᵉ →∗ᵉ X`.ᵉ Theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="commutingᵉ trianglesᵉ ofᵉ pointedᵉ maps"ᵉ Agda=left-whisker-coherence-triangle-pointed-mapsᵉ}}
isᵉ aᵉ coherenceᵉ ofᵉ theᵉ triangleᵉ ofᵉ pointedᵉ mapsᵉ

```text
              topᵉ
          Aᵉ ------>ᵉ Bᵉ
           \ᵉ       /ᵉ
  fᵉ ∘∗ᵉ leftᵉ \ᵉ     /ᵉ fᵉ ∘∗ᵉ rightᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
               Xᵉ
```

Inᵉ otherᵉ words,ᵉ leftᵉ whiskeringᵉ ofᵉ coherencesᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ pointedᵉ
mapsᵉ isᵉ anᵉ operationᵉ

```text
  (leftᵉ ~∗ᵉ rightᵉ ∘∗ᵉ topᵉ) → (fᵉ ∘∗ᵉ leftᵉ ~∗ᵉ (fᵉ ∘∗ᵉ rightᵉ) ∘∗ᵉ top).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  {Xᵉ : Pointed-Typeᵉ l4ᵉ} (fᵉ : Cᵉ →∗ᵉ Xᵉ)
  (leftᵉ : Aᵉ →∗ᵉ Cᵉ) (rightᵉ : Bᵉ →∗ᵉ Cᵉ) (topᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  left-whisker-coherence-triangle-pointed-mapsᵉ :
    coherence-triangle-pointed-mapsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-pointed-mapsᵉ (fᵉ ∘∗ᵉ leftᵉ) (fᵉ ∘∗ᵉ rightᵉ) topᵉ
  left-whisker-coherence-triangle-pointed-mapsᵉ Hᵉ =
    concat-pointed-htpyᵉ
      ( left-whisker-comp-pointed-htpyᵉ fᵉ leftᵉ (rightᵉ ∘∗ᵉ topᵉ) Hᵉ)
      ( inv-pointed-htpyᵉ
        ( associative-comp-pointed-mapᵉ fᵉ rightᵉ topᵉ))
```