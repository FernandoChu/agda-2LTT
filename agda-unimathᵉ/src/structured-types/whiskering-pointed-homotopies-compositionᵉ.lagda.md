# Whiskering of pointed homotopies with respect to composition of pointed maps

```agda
module structured-types.whiskering-pointed-homotopies-compositionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-2-homotopiesᵉ
open import structured-types.pointed-families-of-typesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ [whiskeringᵉ operations](foundation.whiskering-operations.mdᵉ) ofᵉ
[pointedᵉ homotopies](structured-types.pointed-homotopies.mdᵉ) with respectᵉ to
compositionᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ) areᵉ twoᵉ
operationsᵉ thatᵉ produceᵉ pointedᵉ homotopiesᵉ betweenᵉ compositesᵉ ofᵉ pointedᵉ mapsᵉ
fromᵉ eitherᵉ aᵉ pointedᵉ homotopyᵉ onᵉ theᵉ leftᵉ orᵉ onᵉ theᵉ rightᵉ ofᵉ theᵉ composition.ᵉ

-ᵉ Considerᵉ aᵉ pointedᵉ homotopyᵉ `Hᵉ : fᵉ ~∗ᵉ g`ᵉ betweenᵉ pointedᵉ mapsᵉ `fᵉ gᵉ : Aᵉ →∗ᵉ B`,ᵉ
  andᵉ considerᵉ aᵉ pointedᵉ mapᵉ `hᵉ : Bᵉ →∗ᵉ C`,ᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

  ```text
        fᵉ
      ----->ᵉ     hᵉ
    Aᵉ ----->ᵉ Bᵉ ----->ᵉ C.ᵉ
        gᵉ
  ```

  Theᵉ
  {{#conceptᵉ "leftᵉ whiskeringᵉ operationᵉ onᵉ pointedᵉ homotopies"ᵉ Agda=left-whisker-comp-pointed-htpyᵉ}}
  ofᵉ `h`ᵉ andᵉ `H`ᵉ isᵉ aᵉ pointedᵉ homotopyᵉ

  ```text
    hᵉ ·l∗ᵉ Hᵉ : hᵉ ∘∗ᵉ fᵉ ~∗ᵉ hᵉ ∘∗ᵉ g.ᵉ
  ```

-ᵉ Considerᵉ aᵉ pointedᵉ mapᵉ `fᵉ : Aᵉ →∗ᵉ B`ᵉ andᵉ considerᵉ aᵉ pointedᵉ homotopyᵉ
  `Hᵉ : gᵉ ~∗ᵉ g`ᵉ betweenᵉ twᵉ pointedᵉ mapsᵉ `gᵉ hᵉ : Bᵉ →∗ᵉ C`,ᵉ asᵉ indicatedᵉ in theᵉ
  diagramᵉ

  ```text
                 gᵉ
        fᵉ      ----->ᵉ
    Aᵉ ----->ᵉ Bᵉ ----->ᵉ C.ᵉ
                 hᵉ
  ```

  Theᵉ
  {{#conceptᵉ "rightᵉ whiskeringᵉ operationᵉ onᵉ pointedᵉ homotopies"ᵉ Agda=right-whisker-comp-pointed-htpyᵉ}}
  ofᵉ `H`ᵉ andᵉ `f`ᵉ isᵉ aᵉ pointedᵉ homotopyᵉ

  ```text
    Hᵉ ·r∗ᵉ fᵉ : gᵉ ∘∗ᵉ fᵉ ~∗ᵉ hᵉ ∘∗ᵉ f.ᵉ
  ```

## Definitions

### Left whiskering of pointed homotopies

Considerᵉ twoᵉ pointedᵉ mapsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁ᵉ) : Aᵉ →∗ᵉ B`ᵉ andᵉ
`gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁ᵉ) : Aᵉ →∗ᵉ B`ᵉ equippedᵉ with aᵉ pointedᵉ homotopyᵉ
`Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁ᵉ) : fᵉ ~∗ᵉ g`,ᵉ andᵉ considerᵉ furthermoreᵉ aᵉ pointedᵉ mapᵉ
`hᵉ :=ᵉ (h₀ᵉ ,ᵉ h₁ᵉ) : Bᵉ →∗ᵉ C`.ᵉ Thenᵉ weᵉ constructᵉ aᵉ pointedᵉ homotopyᵉ

```text
  hᵉ ·l∗ᵉ Hᵉ : (hᵉ ∘∗ᵉ fᵉ) ~∗ᵉ (hᵉ ∘∗ᵉ g).ᵉ
```

**Construction.**ᵉ Theᵉ underlyingᵉ homotopyᵉ ofᵉ `hᵉ ·l∗ᵉ H`ᵉ isᵉ theᵉ whiskeredᵉ homotpyᵉ

```text
  h₀ᵉ ·lᵉ H₀.ᵉ
```

Forᵉ theᵉ coherence,ᵉ weᵉ haveᵉ to showᵉ thatᵉ theᵉ triangleᵉ

```text
            apᵉ h₀ᵉ (H₀ᵉ *ᵉ)
  h₀ᵉ (f₀ᵉ *ᵉ) ------------>ᵉ h₀ᵉ (g₀ᵉ *ᵉ)
           \ᵉ             /ᵉ
   apᵉ h₀ᵉ f₁ᵉ \ᵉ           /ᵉ apᵉ h₀ᵉ g₁ᵉ
             ∨ᵉ         ∨ᵉ
           h₀ᵉ *ᵉ       h₀ᵉ *ᵉ
               \ᵉ     /ᵉ
             h₁ᵉ \ᵉ   /ᵉ h₁ᵉ
                 ∨ᵉ ∨ᵉ
                  ∗ᵉ
```

commutes.ᵉ Byᵉ rightᵉ whiskeringᵉ ofᵉ
[commutingᵉ trianglesᵉ ofᵉ identifications](foundation.commuting-squares-of-identifications.mdᵉ)
with respectᵉ to concatenationᵉ itᵉ sufficesᵉ to showᵉ thatᵉ theᵉ triangleᵉ

```text
           apᵉ h₀ᵉ (H₀ᵉ *ᵉ)
  h₀ᵉ (f₀ᵉ *ᵉ) --------->ᵉ h₀ᵉ (g₀ᵉ *ᵉ)
           \ᵉ          /ᵉ
   apᵉ h₀ᵉ f₁ᵉ \ᵉ        /ᵉ apᵉ h₀ᵉ g₁ᵉ
             \ᵉ      /ᵉ
              ∨ᵉ    ∨ᵉ
               h₀ᵉ *ᵉ
```

commutes.ᵉ Byᵉ functorialityᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ identifications,ᵉ thisᵉ
followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ triangleᵉ

```text
        H₀ᵉ *ᵉ
  f₀ᵉ *ᵉ ------>ᵉ g₀ᵉ *ᵉ
      \ᵉ       /ᵉ
    f₁ᵉ \ᵉ     /ᵉ g₁ᵉ
        \ᵉ   /ᵉ
         ∨ᵉ ∨ᵉ
          *ᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  (hᵉ : Bᵉ →∗ᵉ Cᵉ) (fᵉ gᵉ : Aᵉ →∗ᵉ Bᵉ) (Hᵉ : fᵉ ~∗ᵉ gᵉ)
  where

  htpy-left-whisker-comp-pointed-htpyᵉ :
    map-comp-pointed-mapᵉ hᵉ fᵉ ~ᵉ map-comp-pointed-mapᵉ hᵉ gᵉ
  htpy-left-whisker-comp-pointed-htpyᵉ =
    map-pointed-mapᵉ hᵉ ·lᵉ htpy-pointed-htpyᵉ Hᵉ

  coherence-point-left-whisker-comp-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( hᵉ ∘∗ᵉ fᵉ)
      ( hᵉ ∘∗ᵉ gᵉ)
      ( htpy-left-whisker-comp-pointed-htpyᵉ)
  coherence-point-left-whisker-comp-pointed-htpyᵉ =
    right-whisker-concat-coherence-triangle-identificationsᵉ
      ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ fᵉ))
      ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ gᵉ))
      ( apᵉ
        ( map-pointed-mapᵉ hᵉ)
        ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ)))
      ( preserves-point-pointed-mapᵉ hᵉ)
      ( map-coherence-triangle-identificationsᵉ
        ( map-pointed-mapᵉ hᵉ)
        ( preserves-point-pointed-mapᵉ fᵉ)
        ( preserves-point-pointed-mapᵉ gᵉ)
        ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
        ( coherence-point-pointed-htpyᵉ Hᵉ))

  left-whisker-comp-pointed-htpyᵉ : hᵉ ∘∗ᵉ fᵉ ~∗ᵉ hᵉ ∘∗ᵉ gᵉ
  pr1ᵉ left-whisker-comp-pointed-htpyᵉ =
    htpy-left-whisker-comp-pointed-htpyᵉ
  pr2ᵉ left-whisker-comp-pointed-htpyᵉ =
    coherence-point-left-whisker-comp-pointed-htpyᵉ
```

### Right whiskering of pointed homotopies

Considerᵉ aᵉ pointedᵉ mapᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁ᵉ) : Aᵉ →∗ᵉ B`ᵉ andᵉ twoᵉ pointedᵉ mapsᵉ
`gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁ᵉ) : Bᵉ →∗ᵉ C`ᵉ andᵉ `hᵉ :=ᵉ (h₀ᵉ ,ᵉ h₁ᵉ) : Bᵉ →∗ᵉ C`ᵉ equippedᵉ with aᵉ pointedᵉ
homotopyᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁ᵉ) : gᵉ ~∗ᵉ h`.ᵉ Thenᵉ weᵉ constructᵉ aᵉ pointedᵉ homotopyᵉ

```text
  Hᵉ ·r∗ᵉ fᵉ : (gᵉ ∘∗ᵉ fᵉ) ~∗ᵉ (hᵉ ∘∗ᵉ f).ᵉ
```

**Construction.**ᵉ Theᵉ underlyingᵉ homotopyᵉ ofᵉ `Hᵉ ·r∗ᵉ f`ᵉ isᵉ theᵉ homotopyᵉ

```text
  H₀ᵉ ·rᵉ f₀ᵉ : (g₀ᵉ ∘ᵉ f₀ᵉ) ~ᵉ (h₀ᵉ ∘ᵉ f₀).ᵉ
```

Thenᵉ weᵉ haveᵉ to showᵉ thatᵉ theᵉ outerᵉ triangleᵉ in theᵉ diagramᵉ

```text
              H₀ᵉ (f₀ᵉ *ᵉ)
  g₀ᵉ (f₀ᵉ *ᵉ) ------------>ᵉ h₀ᵉ (f₀ᵉ *ᵉ)
           \ᵉ             /ᵉ
   apᵉ g₀ᵉ f₁ᵉ \ᵉ           /ᵉ apᵉ h₀ᵉ f₁ᵉ
             ∨ᵉ  H₀ᵉ *ᵉ   ∨ᵉ
           g₀ᵉ *ᵉ ---->ᵉ h₀ᵉ *ᵉ
               \ᵉ     /ᵉ
             g₁ᵉ \ᵉ   /ᵉ h₁ᵉ
                 ∨ᵉ ∨ᵉ
                  ∗ᵉ
```

commutes.ᵉ Thisᵉ isᵉ doneᵉ byᵉ verticallyᵉ pastingᵉ theᵉ upperᵉ squareᵉ andᵉ theᵉ lowerᵉ
triangle.ᵉ Theᵉ upperᵉ squareᵉ commutesᵉ byᵉ inverseᵉ naturalityᵉ ofᵉ theᵉ homotopyᵉ `H₀`.ᵉ
Theᵉ lowerᵉ triangleᵉ isᵉ theᵉ baseᵉ pointᵉ coherenceᵉ `H₁`ᵉ ofᵉ theᵉ pointedᵉ homotopyᵉ
`Hᵉ ≐ᵉ (H₀ᵉ ,ᵉ H₁)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  (g1ᵉ g2ᵉ : Bᵉ →∗ᵉ Cᵉ) (Hᵉ : g1ᵉ ~∗ᵉ g2ᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  htpy-right-whisker-comp-pointed-htpyᵉ :
    unpointed-htpy-pointed-Πᵉ (g1ᵉ ∘∗ᵉ fᵉ) (g2ᵉ ∘∗ᵉ fᵉ)
  htpy-right-whisker-comp-pointed-htpyᵉ =
    htpy-pointed-htpyᵉ Hᵉ ·rᵉ map-pointed-mapᵉ fᵉ

  coherence-point-right-whisker-comp-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( g1ᵉ ∘∗ᵉ fᵉ)
      ( g2ᵉ ∘∗ᵉ fᵉ)
      ( htpy-right-whisker-comp-pointed-htpyᵉ)
  coherence-point-right-whisker-comp-pointed-htpyᵉ =
    vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ
      ( htpy-pointed-htpyᵉ Hᵉ _)
      ( apᵉ (map-pointed-mapᵉ g1ᵉ) _)
      ( apᵉ (map-pointed-mapᵉ g2ᵉ) _)
      ( htpy-pointed-htpyᵉ Hᵉ _)
      ( preserves-point-pointed-mapᵉ g1ᵉ)
      ( preserves-point-pointed-mapᵉ g2ᵉ)
      ( inv-nat-htpyᵉ (htpy-pointed-htpyᵉ Hᵉ) _)
      ( coherence-point-pointed-htpyᵉ Hᵉ)

  right-whisker-comp-pointed-htpyᵉ : g1ᵉ ∘∗ᵉ fᵉ ~∗ᵉ g2ᵉ ∘∗ᵉ fᵉ
  pr1ᵉ right-whisker-comp-pointed-htpyᵉ =
    htpy-right-whisker-comp-pointed-htpyᵉ
  pr2ᵉ right-whisker-comp-pointed-htpyᵉ =
    coherence-point-right-whisker-comp-pointed-htpyᵉ
```

## Properties

### Computing the left whiskering of the reflexive pointed homotopy

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  (hᵉ : Bᵉ →∗ᵉ Cᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  compute-refl-left-whisker-comp-pointed-htpyᵉ :
    pointed-2-htpyᵉ
      ( left-whisker-comp-pointed-htpyᵉ hᵉ fᵉ fᵉ (refl-pointed-htpyᵉ fᵉ))
      ( refl-pointed-htpyᵉ (hᵉ ∘∗ᵉ fᵉ))
  compute-refl-left-whisker-comp-pointed-htpyᵉ =
    refl-pointed-2-htpyᵉ (refl-pointed-htpyᵉ (hᵉ ∘∗ᵉ fᵉ))
```

### Computing the right whiskering of the reflexive pointed homotopy

Considerᵉ twoᵉ pointedᵉ mapsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁ᵉ) : Aᵉ →∗ᵉ B`ᵉ andᵉ
`gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁ᵉ) : Bᵉ →∗ᵉ C`.ᵉ Weᵉ areᵉ constructingᵉ aᵉ pointedᵉ `2`-homotopyᵉ

```text
  right-whisker-comp-pointed-htpyᵉ (refl-pointed-htpyᵉ hᵉ) fᵉ ~∗ᵉ
  refl-pointed-htpyᵉ (gᵉ ∘∗ᵉ fᵉ)
```

Theᵉ underlyingᵉ homotopyᵉ ofᵉ thisᵉ pointedᵉ `2`-homotopyᵉ isᵉ `refl-htpy`.ᵉ Theᵉ baseᵉ
pointᵉ coherenceᵉ ofᵉ thisᵉ homotopyᵉ isᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ
triangleᵉ

```text
                   H₁ᵉ
  apᵉ g₀ᵉ f₁ᵉ ∙ᵉ g₁ᵉ ------>ᵉ reflᵉ ∙ᵉ (apᵉ g₀ᵉ f₁ᵉ ∙ᵉ g₁ᵉ)
               \ᵉ       /ᵉ
           reflᵉ \ᵉ     /ᵉ right-whisker-concatᵉ reflᵉ (apᵉ g₀ᵉ f₁ᵉ ∙ᵉ g₁ᵉ) ≐ᵉ reflᵉ
                 \ᵉ   /ᵉ
                  ∨ᵉ ∨ᵉ
       reflᵉ ∙ᵉ (apᵉ g₀ᵉ f₁ᵉ ∙ᵉ g₁ᵉ)
```

commutes.ᵉ Here,ᵉ theᵉ identificationᵉ `H₁`ᵉ isᵉ theᵉ verticalᵉ pastingᵉ ofᵉ theᵉ upperᵉ
squareᵉ andᵉ theᵉ lowerᵉ triangleᵉ in theᵉ diagramᵉ

```text
                reflᵉ
  g₀ᵉ (f₀ᵉ *ᵉ) ------------>ᵉ g₀ᵉ (f₀ᵉ *ᵉ)
           \ᵉ             /ᵉ
   apᵉ g₀ᵉ f₁ᵉ \ᵉ           /ᵉ apᵉ g₀ᵉ f₁ᵉ
             ∨ᵉ  reflᵉ   ∨ᵉ
           g₀ᵉ *ᵉ ---->ᵉ g₀ᵉ *ᵉ
               \ᵉ     /ᵉ
             g₁ᵉ \ᵉ   /ᵉ g₁ᵉ
                 ∨ᵉ ∨ᵉ
                  ∗.ᵉ
```

Theᵉ upperᵉ squareᵉ in thisᵉ diagramᵉ isᵉ theᵉ inverseᵉ naturalityᵉ ofᵉ theᵉ reflexiveᵉ
homotopyᵉ `refl-htpy`ᵉ andᵉ theᵉ lowerᵉ triangleᵉ in thisᵉ diagramᵉ isᵉ theᵉ reflexiveᵉ
identification.ᵉ

Recallᵉ thatᵉ theᵉ inverseᵉ naturalityᵉ ofᵉ theᵉ reflexiveᵉ homotopyᵉ
`inv-nat-htpyᵉ refl-htpyᵉ f₁`ᵉ computesᵉ to theᵉ horizontallyᵉ constantᵉ squareᵉ ofᵉ
identifications.ᵉ Furthermore,ᵉ theᵉ verticalᵉ pastingᵉ ofᵉ theᵉ horizontallyᵉ constantᵉ
squareᵉ `right-unit`ᵉ andᵉ anyᵉ commutingᵉ triangleᵉ `refl`ᵉ computesᵉ to `refl`.ᵉ
Thereforeᵉ itᵉ followsᵉ thatᵉ theᵉ identificationᵉ `H₁`ᵉ aboveᵉ isᵉ equalᵉ to `refl`,ᵉ asᵉ
wasᵉ requiredᵉ to show.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  (hᵉ : Bᵉ →∗ᵉ Cᵉ) (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  htpy-compute-refl-right-whisker-comp-pointed-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ
      ( right-whisker-comp-pointed-htpyᵉ hᵉ hᵉ (refl-pointed-htpyᵉ hᵉ) fᵉ)
      ( refl-pointed-htpyᵉ (hᵉ ∘∗ᵉ fᵉ))
  htpy-compute-refl-right-whisker-comp-pointed-htpyᵉ = refl-htpyᵉ

  coherence-point-compute-refl-right-whisker-comp-pointed-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( right-whisker-comp-pointed-htpyᵉ hᵉ hᵉ (refl-pointed-htpyᵉ hᵉ) fᵉ)
      ( refl-pointed-htpyᵉ (hᵉ ∘∗ᵉ fᵉ))
      ( htpy-compute-refl-right-whisker-comp-pointed-htpyᵉ)
  coherence-point-compute-refl-right-whisker-comp-pointed-htpyᵉ =
    invᵉ
      ( ( right-unitᵉ) ∙ᵉ
        ( ( apᵉ
            ( λ tᵉ →
              vertical-pasting-coherence-square-coherence-triangle-identificationsᵉ
                ( reflᵉ)
                ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ fᵉ))
                ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ fᵉ))
                ( reflᵉ)
                ( preserves-point-pointed-mapᵉ hᵉ)
                ( preserves-point-pointed-mapᵉ hᵉ)
                ( tᵉ)
                ( reflᵉ))
            ( inv-nat-refl-htpyᵉ
              ( map-pointed-mapᵉ hᵉ)
              ( preserves-point-pointed-mapᵉ fᵉ))) ∙ᵉ
          ( right-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
            ( apᵉ (map-pointed-mapᵉ hᵉ) (preserves-point-pointed-mapᵉ fᵉ))
            ( preserves-point-pointed-mapᵉ hᵉ))))

  compute-refl-right-whisker-comp-pointed-htpyᵉ :
    pointed-2-htpyᵉ
      ( right-whisker-comp-pointed-htpyᵉ hᵉ hᵉ (refl-pointed-htpyᵉ hᵉ) fᵉ)
      ( refl-pointed-htpyᵉ (hᵉ ∘∗ᵉ fᵉ))
  pr1ᵉ compute-refl-right-whisker-comp-pointed-htpyᵉ =
    htpy-compute-refl-right-whisker-comp-pointed-htpyᵉ
  pr2ᵉ compute-refl-right-whisker-comp-pointed-htpyᵉ =
    coherence-point-compute-refl-right-whisker-comp-pointed-htpyᵉ
```