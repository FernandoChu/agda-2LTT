# Whiskering pointed homotopies with respect to concatenation

```agda
module structured-types.whiskering-pointed-2-homotopies-concatenationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-concatenationᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-2-homotopiesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ [whiskeringᵉ operations](foundation.whiskering-operations.mdᵉ) ofᵉ
[pointedᵉ `2`-homotopies](structured-types.pointed-2-homotopies.mdᵉ) with respectᵉ
to concatenationᵉ ofᵉ [pointedᵉ homotopies](structured-types.pointed-homotopies.mdᵉ)
areᵉ twoᵉ operationsᵉ thatᵉ produceᵉ pointedᵉ 2-homotopiesᵉ betweenᵉ concatenationsᵉ ofᵉ
pointedᵉ homotopiesᵉ fromᵉ eitherᵉ aᵉ pointedᵉ 2-homotopyᵉ onᵉ theᵉ leftᵉ orᵉ onᵉ theᵉ rightᵉ
ofᵉ theᵉ concatenations.ᵉ

-ᵉ Theᵉ
  {{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="pointedᵉ `2`-homotopiesᵉ with respectᵉ to concatenation"ᵉ Agda=left-whisker-concat-pointed-2-htpyᵉ}}
  isᵉ anᵉ operationᵉ thatᵉ takesᵉ aᵉ pointedᵉ homotopyᵉ `Hᵉ : fᵉ ~∗ᵉ g`ᵉ andᵉ aᵉ pointedᵉ
  `2`-homotopyᵉ `αᵉ : Kᵉ ~²∗ᵉ L`ᵉ betweenᵉ twoᵉ pointedᵉ homotopiesᵉ `Kᵉ Lᵉ : gᵉ ~∗ᵉ h`ᵉ asᵉ
  indicatedᵉ in theᵉ diagramᵉ

  ```text
                 Kᵉ
        Hᵉ      ----->ᵉ
    fᵉ ----->ᵉ gᵉ ----->ᵉ h,ᵉ
                 Lᵉ
  ```

  andᵉ returnsᵉ aᵉ pointedᵉ `2`-homotopyᵉ `Hᵉ ∙hᵉ Kᵉ ~²∗ᵉ Hᵉ ∙hᵉ L`.ᵉ

-ᵉ Theᵉ
  {{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="pointedᵉ `2`-homotopiesᵉ with respectᵉ to concatenation"ᵉ Agda=right-whisker-concat-pointed-2-htpyᵉ}}
  isᵉ anᵉ operationᵉ thatᵉ takesᵉ aᵉ pointedᵉ `2`-homotopyᵉ `αᵉ : Hᵉ ~²∗ᵉ K`ᵉ betweenᵉ twoᵉ
  pointedᵉ homotopiesᵉ `Hᵉ Kᵉ : fᵉ ~∗ᵉ g`ᵉ andᵉ aᵉ pointedᵉ homotopyᵉ `Lᵉ : gᵉ ~∗ᵉ h`ᵉ asᵉ
  indicatedᵉ in theᵉ diagramᵉ

  ```text
        Hᵉ
      ----->ᵉ
    fᵉ ----->ᵉ gᵉ ----->ᵉ h,ᵉ
        Kᵉ        Lᵉ
  ```

  andᵉ returnsᵉ aᵉ pointedᵉ `2`-homotopyᵉ `Hᵉ ∙hᵉ Lᵉ ~²∗ᵉ Kᵉ ∙hᵉ L`.ᵉ

## Definitions

### Left whiskering of pointed `2`-homotopies with respect to concatenation

Considerᵉ threeᵉ pointedᵉ mapsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`,ᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`,ᵉ andᵉ
`hᵉ :=ᵉ (h₀ᵉ ,ᵉ h₁)`ᵉ fromᵉ `A`ᵉ to `B`,ᵉ aᵉ pointedᵉ homotopyᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁ᵉ) : fᵉ ~∗ᵉ g`ᵉ
andᵉ aᵉ pointedᵉ `2`-homotopyᵉ `αᵉ :=ᵉ (α₀ᵉ ,ᵉ α₁ᵉ) : Kᵉ ~²∗ᵉ L`ᵉ betweenᵉ twoᵉ pointedᵉ
homotopiesᵉ `Kᵉ :=ᵉ (K₀ᵉ ,ᵉ K₁)`ᵉ andᵉ `Lᵉ :=ᵉ (L₀ᵉ ,ᵉ L₁)`ᵉ fromᵉ `g`ᵉ to `h`ᵉ asᵉ indicatedᵉ in
theᵉ diagramᵉ

```text
               Kᵉ
      Hᵉ      ----->ᵉ
  fᵉ ----->ᵉ gᵉ ----->ᵉ h.ᵉ
               Lᵉ
```

Theᵉ underlyingᵉ homotopyᵉ ofᵉ theᵉ leftᵉ whiskeringᵉ `Hᵉ ·l∗ᵉ αᵉ : Hᵉ ∙hᵉ Kᵉ ~²∗ᵉ Hᵉ ∙hᵉ L`ᵉ isᵉ
theᵉ homotopyᵉ

```text
  H₀ᵉ ·lᵉ α₀ᵉ : H₀ᵉ ∙hᵉ K₀ᵉ ~ᵉ H₀ᵉ ∙hᵉ L₀.ᵉ
```

Theᵉ baseᵉ pointᵉ coherenceᵉ ofᵉ thisᵉ homotopyᵉ isᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ
theᵉ triangleᵉ

```text
           (Hᵉ ∙hᵉ K)₁ᵉ
        f₁ᵉ -------->ᵉ ((H₀ᵉ *ᵉ) ∙ᵉ (K₀ᵉ *ᵉ)) ∙ᵉ h₁ᵉ
           \ᵉ       /ᵉ
  (Hᵉ ∙hᵉ L)₁ᵉ \ᵉ     /ᵉ right-whiskerᵉ (left-whiskerᵉ (H₀ᵉ *ᵉ) (α₀ᵉ *ᵉ)) h₁ᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
    ((H₀ᵉ *ᵉ) ∙ᵉ (L₀ᵉ *ᵉ)) ∙ᵉ h₁ᵉ
```

commutes.ᵉ Here,ᵉ theᵉ identificationsᵉ `(Hᵉ ∙hᵉ K)₁`ᵉ andᵉ `(Hᵉ ∙hᵉ L)₁`ᵉ areᵉ theᵉ
horizontalᵉ pastingsᵉ ofᵉ theᵉ
[commutingᵉ trianglesᵉ ofᵉ identifications](foundation.commuting-triangles-of-identifications.mdᵉ)

```text
       H₀ᵉ *ᵉ      K₀ᵉ *ᵉ                   H₀ᵉ *ᵉ      L₀ᵉ *ᵉ
  f₀ᵉ *ᵉ --->ᵉ g₀ᵉ *ᵉ ---->ᵉ h₀ᵉ *ᵉ        f₀ᵉ *ᵉ --->ᵉ g₀ᵉ *ᵉ ---->ᵉ h₀ᵉ *ᵉ
       \ᵉ      |      /ᵉ                  \ᵉ      |      /ᵉ
        \ᵉ  H₁ᵉ |  K₁ᵉ /ᵉ                    \ᵉ  H₁ᵉ |  L₁ᵉ /ᵉ
     f₁ᵉ  \ᵉ    |g₁ᵉ  /ᵉ h₁ᵉ               f₁ᵉ  \ᵉ    |g₁ᵉ  /ᵉ h₁ᵉ
          \ᵉ   |   /ᵉ                        \ᵉ   |   /ᵉ
           \ᵉ  |  /ᵉ                          \ᵉ  |  /ᵉ
            ∨ᵉ ∨ᵉ ∨ᵉ                            ∨ᵉ ∨ᵉ ∨ᵉ
              *ᵉ                                *.ᵉ
```

Thenᵉ theᵉ triangleᵉ

```text
                   horizontal-pastingᵉ H₁ᵉ K₁ᵉ
                       f₁ᵉ -------->ᵉ (H₀ᵉ *ᵉ ∙ᵉ K₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
                         \ᵉ         /ᵉ
                          \ᵉ       /ᵉ
  horizontal-pastingᵉ H₁ᵉ L₁ᵉ \ᵉ     /ᵉ right-whiskerᵉ (left-whiskerᵉ (H₀ᵉ *ᵉ) (α₀ᵉ *ᵉ)) h₁ᵉ
                            \ᵉ   /ᵉ
                             ∨ᵉ ∨ᵉ
                        (H₀ᵉ *ᵉ ∙ᵉ K₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
```

commutesᵉ byᵉ leftᵉ whiskeringᵉ ofᵉ horizontalᵉ pastingᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ
identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : Aᵉ →∗ᵉ Bᵉ} (Hᵉ : fᵉ ~∗ᵉ gᵉ) (Kᵉ Lᵉ : gᵉ ~∗ᵉ hᵉ) (αᵉ : Kᵉ ~²∗ᵉ Lᵉ)
  where

  htpy-left-whisker-concat-pointed-2-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ Kᵉ)
      ( concat-pointed-htpyᵉ Hᵉ Lᵉ)
  htpy-left-whisker-concat-pointed-2-htpyᵉ =
    left-whisker-concat-htpyᵉ (htpy-pointed-htpyᵉ Hᵉ) (htpy-pointed-2-htpyᵉ αᵉ)

  coherence-point-left-whisker-concat-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ Kᵉ)
      ( concat-pointed-htpyᵉ Hᵉ Lᵉ)
      ( htpy-left-whisker-concat-pointed-2-htpyᵉ)
  coherence-point-left-whisker-concat-pointed-2-htpyᵉ =
    left-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( preserves-point-pointed-mapᵉ gᵉ)
      ( preserves-point-pointed-mapᵉ hᵉ)
      ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( htpy-pointed-htpyᵉ Kᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( htpy-pointed-htpyᵉ Lᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( coherence-point-pointed-htpyᵉ Hᵉ)
      ( coherence-point-pointed-htpyᵉ Kᵉ)
      ( coherence-point-pointed-htpyᵉ Lᵉ)
      ( htpy-pointed-2-htpyᵉ αᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( coherence-point-pointed-2-htpyᵉ αᵉ)

  left-whisker-concat-pointed-2-htpyᵉ :
    concat-pointed-htpyᵉ Hᵉ Kᵉ ~²∗ᵉ concat-pointed-htpyᵉ Hᵉ Lᵉ
  pr1ᵉ left-whisker-concat-pointed-2-htpyᵉ =
    htpy-left-whisker-concat-pointed-2-htpyᵉ
  pr2ᵉ left-whisker-concat-pointed-2-htpyᵉ =
    coherence-point-left-whisker-concat-pointed-2-htpyᵉ
```

### Right whiskering of pointed `2`-homotopies with respect to concatenation

Considerᵉ threeᵉ pointedᵉ mapsᵉ `fᵉ :=ᵉ (f₀ᵉ ,ᵉ f₁)`,ᵉ `gᵉ :=ᵉ (g₀ᵉ ,ᵉ g₁)`,ᵉ andᵉ
`hᵉ :=ᵉ (h₀ᵉ ,ᵉ h₁)`ᵉ fromᵉ `A`ᵉ to `B`,ᵉ aᵉ pointedᵉ `2`-homotopyᵉ
`αᵉ :=ᵉ (α₀ᵉ ,ᵉ α₁ᵉ) : Hᵉ ~²∗ᵉ K`ᵉ betweenᵉ twoᵉ pointedᵉ homotopiesᵉ `Hᵉ :=ᵉ (H₀ᵉ ,ᵉ H₁)`ᵉ andᵉ
`Kᵉ :=ᵉ (K₀ᵉ ,ᵉ K₁)`ᵉ fromᵉ `f`ᵉ to `g`ᵉ andᵉ aᵉ pointedᵉ homotopyᵉ
`Lᵉ :=ᵉ (L₀ᵉ ,ᵉ L₁ᵉ) : gᵉ ~∗ᵉ h`ᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
      Hᵉ
    ----->ᵉ
  fᵉ ----->ᵉ gᵉ ----->ᵉ h.ᵉ
      Kᵉ        Lᵉ
```

Theᵉ underlyingᵉ homotopyᵉ ofᵉ theᵉ rightᵉ whiskeringᵉ `αᵉ ·r∗ᵉ Lᵉ : Hᵉ ∙hᵉ Lᵉ ~²∗ᵉ Kᵉ ∙hᵉ L`ᵉ isᵉ
theᵉ homotopyᵉ

```text
  α₀ᵉ ·rᵉ L₀ᵉ : H₀ᵉ ∙hᵉ L₀ᵉ ~ᵉ K₀ᵉ ∙hᵉ L₀.ᵉ
```

Theᵉ baseᵉ pointᵉ coherenceᵉ ofᵉ thisᵉ homotopyᵉ isᵉ anᵉ identificationᵉ witnessingᵉ thatᵉ
theᵉ triangleᵉ

```text
           (Hᵉ ∙hᵉ L)₁ᵉ
         f₁ᵉ -------->ᵉ ((H₀ᵉ *ᵉ) ∙ᵉ (L₀ᵉ *ᵉ)) ∙ᵉ h₁ᵉ
           \ᵉ         /ᵉ
  (Kᵉ ∙hᵉ L)₁ᵉ \ᵉ       /ᵉ right-whiskerᵉ (right-whiskerᵉ (α₀ᵉ *ᵉ) (L₀ᵉ *ᵉ)) h₁ᵉ
             \ᵉ     /ᵉ
              ∨ᵉ   ∨ᵉ
      ((K₀ᵉ *ᵉ) ∙ᵉ (L₀ᵉ *ᵉ)) ∙ᵉ h₁ᵉ
```

commutes.ᵉ Here,ᵉ theᵉ identificationsᵉ `(Hᵉ ∙hᵉ L)₁`ᵉ andᵉ `(Kᵉ ∙hᵉ L)₁`ᵉ areᵉ theᵉ
horizontalᵉ pastingsᵉ ofᵉ theᵉ
[commutingᵉ trianglesᵉ ofᵉ identifications](foundation.commuting-triangles-of-identifications.mdᵉ)

```text
       H₀ᵉ *ᵉ      L₀ᵉ *ᵉ                   K₀ᵉ *ᵉ      L₀ᵉ *ᵉ
  f₀ᵉ *ᵉ --->ᵉ g₀ᵉ *ᵉ ---->ᵉ h₀ᵉ *ᵉ        f₀ᵉ *ᵉ --->ᵉ g₀ᵉ *ᵉ ---->ᵉ h₀ᵉ *ᵉ
       \ᵉ      |      /ᵉ                  \ᵉ      |      /ᵉ
        \ᵉ  H₁ᵉ |  L₁ᵉ /ᵉ                    \ᵉ  K₁ᵉ |  L₁ᵉ /ᵉ
     f₁ᵉ  \ᵉ    |g₁ᵉ  /ᵉ h₁ᵉ               f₁ᵉ  \ᵉ    |g₁ᵉ  /ᵉ h₁ᵉ
          \ᵉ   |   /ᵉ                        \ᵉ   |   /ᵉ
           \ᵉ  |  /ᵉ                          \ᵉ  |  /ᵉ
            ∨ᵉ ∨ᵉ ∨ᵉ                            ∨ᵉ ∨ᵉ ∨ᵉ
              *ᵉ                                *.ᵉ
```

Thenᵉ theᵉ triangleᵉ

```text
                   horizontal-pastingᵉ H₁ᵉ L₁ᵉ
                       f₁ᵉ -------->ᵉ (H₀ᵉ *ᵉ ∙ᵉ L₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
                         \ᵉ         /ᵉ
                          \ᵉ       /ᵉ
  horizontal-pastingᵉ K₁ᵉ L₁ᵉ \ᵉ     /ᵉ right-whiskerᵉ (right-whiskerᵉ (α₀ᵉ *ᵉ) (L₀ᵉ *ᵉ)) h₁ᵉ
                            \ᵉ   /ᵉ
                             ∨ᵉ ∨ᵉ
                        (K₀ᵉ *ᵉ ∙ᵉ L₀ᵉ *ᵉ) ∙ᵉ h₁ᵉ
```

commutesᵉ byᵉ rightᵉ whiskeringᵉ ofᵉ horizontalᵉ pastingᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ
identifications.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : Aᵉ →∗ᵉ Bᵉ} (Hᵉ Kᵉ : fᵉ ~∗ᵉ gᵉ) (αᵉ : Hᵉ ~²∗ᵉ Kᵉ) (Lᵉ : gᵉ ~∗ᵉ hᵉ)
  where

  htpy-right-whisker-concat-pointed-2-htpyᵉ :
    unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ Lᵉ)
      ( concat-pointed-htpyᵉ Kᵉ Lᵉ)
  htpy-right-whisker-concat-pointed-2-htpyᵉ =
    right-whisker-concat-htpyᵉ (htpy-pointed-2-htpyᵉ αᵉ) (htpy-pointed-htpyᵉ Lᵉ)

  coherence-point-right-whisker-concat-pointed-2-htpyᵉ :
    coherence-point-unpointed-htpy-pointed-htpyᵉ
      ( concat-pointed-htpyᵉ Hᵉ Lᵉ)
      ( concat-pointed-htpyᵉ Kᵉ Lᵉ)
      ( htpy-right-whisker-concat-pointed-2-htpyᵉ)
  coherence-point-right-whisker-concat-pointed-2-htpyᵉ =
    right-whisker-horizontal-pasting-coherence-triangle-identificationsᵉ
      ( preserves-point-pointed-mapᵉ fᵉ)
      ( preserves-point-pointed-mapᵉ gᵉ)
      ( preserves-point-pointed-mapᵉ hᵉ)
      ( htpy-pointed-htpyᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( htpy-pointed-htpyᵉ Kᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( htpy-pointed-htpyᵉ Lᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( coherence-point-pointed-htpyᵉ Hᵉ)
      ( coherence-point-pointed-htpyᵉ Kᵉ)
      ( coherence-point-pointed-htpyᵉ Lᵉ)
      ( htpy-pointed-2-htpyᵉ αᵉ (point-Pointed-Typeᵉ Aᵉ))
      ( coherence-point-pointed-2-htpyᵉ αᵉ)

  right-whisker-concat-pointed-2-htpyᵉ :
    concat-pointed-htpyᵉ Hᵉ Lᵉ ~²∗ᵉ concat-pointed-htpyᵉ Kᵉ Lᵉ
  pr1ᵉ right-whisker-concat-pointed-2-htpyᵉ =
    htpy-right-whisker-concat-pointed-2-htpyᵉ
  pr2ᵉ right-whisker-concat-pointed-2-htpyᵉ =
    coherence-point-right-whisker-concat-pointed-2-htpyᵉ
```