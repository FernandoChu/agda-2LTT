# Commuting triangles of maps

```agda
module foundation.commuting-triangles-of-mapsᵉ where

open import foundation-core.commuting-triangles-of-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Aᵉ triangleᵉ ofᵉ mapsᵉ

```text
 Aᵉ ---->ᵉ Bᵉ
  \ᵉ     /ᵉ
   \ᵉ   /ᵉ
    ∨ᵉ ∨ᵉ
     Xᵉ
```

isᵉ saidᵉ to **commute**ᵉ ifᵉ thereᵉ isᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ)
betweenᵉ theᵉ mapᵉ onᵉ theᵉ leftᵉ andᵉ theᵉ compositeᵉ map.ᵉ

## Properties

### Top map is an equivalence

Ifᵉ theᵉ topᵉ mapᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.md),ᵉ thenᵉ thereᵉ
isᵉ anᵉ equivalenceᵉ betweenᵉ theᵉ coherenceᵉ triangleᵉ with theᵉ mapᵉ ofᵉ theᵉ equivalenceᵉ
asᵉ with theᵉ inverseᵉ mapᵉ ofᵉ theᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  equiv-coherence-triangle-maps-inv-top'ᵉ :
    coherence-triangle-mapsᵉ leftᵉ rightᵉ (map-equivᵉ eᵉ) ≃ᵉ
    coherence-triangle-maps'ᵉ rightᵉ leftᵉ (map-inv-equivᵉ eᵉ)
  equiv-coherence-triangle-maps-inv-top'ᵉ =
    equiv-Πᵉ
      ( λ bᵉ → leftᵉ (map-inv-equivᵉ eᵉ bᵉ) ＝ᵉ rightᵉ bᵉ)
      ( eᵉ)
      ( λ aᵉ →
        equiv-concatᵉ
          ( apᵉ leftᵉ (is-retraction-map-inv-equivᵉ eᵉ aᵉ))
          ( rightᵉ (map-equivᵉ eᵉ aᵉ)))

  equiv-coherence-triangle-maps-inv-topᵉ :
    coherence-triangle-mapsᵉ leftᵉ rightᵉ (map-equivᵉ eᵉ) ≃ᵉ
    coherence-triangle-mapsᵉ rightᵉ leftᵉ (map-inv-equivᵉ eᵉ)
  equiv-coherence-triangle-maps-inv-topᵉ =
    ( equiv-inv-htpyᵉ
      ( leftᵉ ∘ᵉ (map-inv-equivᵉ eᵉ))
      ( rightᵉ)) ∘eᵉ
    ( equiv-coherence-triangle-maps-inv-top'ᵉ)

  coherence-triangle-maps-inv-topᵉ :
    coherence-triangle-mapsᵉ leftᵉ rightᵉ (map-equivᵉ eᵉ) →
    coherence-triangle-mapsᵉ rightᵉ leftᵉ (map-inv-equivᵉ eᵉ)
  coherence-triangle-maps-inv-topᵉ =
    map-equivᵉ equiv-coherence-triangle-maps-inv-topᵉ
```

### Commuting triangles of maps induce commuting triangles of precomposition maps

Givenᵉ aᵉ commutingᵉ triangleᵉ ofᵉ mapsᵉ

```text
       fᵉ
   Aᵉ ---->ᵉ Bᵉ
    \ᵉ  ⇗ᵉ  /ᵉ
   hᵉ \ᵉ   /ᵉ gᵉ
      ∨ᵉ ∨ᵉ
       Xᵉ
```

thereᵉ isᵉ anᵉ inducedᵉ commutingᵉ triangleᵉ ofᵉ
[precompositionᵉ maps](foundation-core.precomposition-functions.mdᵉ)

```text
         (-ᵉ ∘ᵉ gᵉ)
  (Xᵉ → Sᵉ) ---->ᵉ (Bᵉ → Sᵉ)
        \ᵉ   ⇗ᵉ  /ᵉ
  (-ᵉ ∘ᵉ hᵉ) \ᵉ   /ᵉ (-ᵉ ∘ᵉ fᵉ)
           ∨ᵉ ∨ᵉ
         (Aᵉ → S).ᵉ
```

Noteᵉ theᵉ changeᵉ ofᵉ orderᵉ ofᵉ `f`ᵉ andᵉ `g`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  ( leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ)
  where

  precomp-coherence-triangle-mapsᵉ :
    coherence-triangle-mapsᵉ leftᵉ rightᵉ topᵉ →
    (Sᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-mapsᵉ
      ( precompᵉ leftᵉ Sᵉ)
      ( precompᵉ topᵉ Sᵉ)
      ( precompᵉ rightᵉ Sᵉ)
  precomp-coherence-triangle-mapsᵉ = htpy-precompᵉ

  precomp-coherence-triangle-maps'ᵉ :
    coherence-triangle-maps'ᵉ leftᵉ rightᵉ topᵉ →
    (Sᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-maps'ᵉ
      ( precompᵉ leftᵉ Sᵉ)
      ( precompᵉ topᵉ Sᵉ)
      ( precompᵉ rightᵉ Sᵉ)
  precomp-coherence-triangle-maps'ᵉ = htpy-precompᵉ
```

### Commuting triangles of maps induce commuting triangles of postcomposition maps

Givenᵉ aᵉ commutingᵉ triangleᵉ ofᵉ mapsᵉ

```text
       fᵉ
   Aᵉ ---->ᵉ Bᵉ
    \ᵉ  ⇗ᵉ  /ᵉ
   hᵉ \ᵉ   /ᵉ gᵉ
      ∨ᵉ ∨ᵉ
       Xᵉ
```

thereᵉ isᵉ anᵉ inducedᵉ commutingᵉ triangleᵉ ofᵉ
[postcompositionᵉ maps](foundation-core.postcomposition-functions.mdᵉ)

```text
         (fᵉ ∘ᵉ -ᵉ)
  (Sᵉ → Aᵉ) ---->ᵉ (Sᵉ → Bᵉ)
        \ᵉ   ⇗ᵉ  /ᵉ
  (hᵉ ∘ᵉ -ᵉ) \ᵉ   /ᵉ (gᵉ ∘ᵉ -ᵉ)
           ∨ᵉ ∨ᵉ
         (Sᵉ → X).ᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  ( leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ)
  where

  postcomp-coherence-triangle-mapsᵉ :
    (Sᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-mapsᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-mapsᵉ
      ( postcompᵉ Sᵉ leftᵉ)
      ( postcompᵉ Sᵉ rightᵉ)
      ( postcompᵉ Sᵉ topᵉ)
  postcomp-coherence-triangle-mapsᵉ Sᵉ = htpy-postcompᵉ Sᵉ

  postcomp-coherence-triangle-maps'ᵉ :
    (Sᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-maps'ᵉ leftᵉ rightᵉ topᵉ →
    coherence-triangle-maps'ᵉ
      ( postcompᵉ Sᵉ leftᵉ)
      ( postcompᵉ Sᵉ rightᵉ)
      ( postcompᵉ Sᵉ topᵉ)
  postcomp-coherence-triangle-maps'ᵉ Sᵉ = htpy-postcompᵉ Sᵉ
```

### Coherences of commuting triangles of maps with fixed vertices

Thisᵉ orᵉ itsᵉ oppositeᵉ shouldᵉ beᵉ theᵉ coherenceᵉ in theᵉ characterizationᵉ ofᵉ
identificationsᵉ ofᵉ commutingᵉ trianglesᵉ ofᵉ mapsᵉ with fixedᵉ endᵉ vertices.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ)
  (left'ᵉ : Aᵉ → Xᵉ) (right'ᵉ : Bᵉ → Xᵉ) (top'ᵉ : Aᵉ → Bᵉ)
  (cᵉ : coherence-triangle-mapsᵉ leftᵉ rightᵉ topᵉ)
  (c'ᵉ : coherence-triangle-mapsᵉ left'ᵉ right'ᵉ top'ᵉ)
  where

  coherence-htpy-triangle-mapsᵉ :
    leftᵉ ~ᵉ left'ᵉ → rightᵉ ~ᵉ right'ᵉ → topᵉ ~ᵉ top'ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-triangle-mapsᵉ Lᵉ Rᵉ Tᵉ =
    cᵉ ∙hᵉ horizontal-concat-htpyᵉ Rᵉ Tᵉ ~ᵉ Lᵉ ∙hᵉ c'ᵉ
```

### Pasting commuting triangles into commuting squares along homotopic diagonals

Twoᵉ [commutingᵉ triangles](foundation-core.commuting-triangles-of-maps.mdᵉ)

```text
   Aᵉ         Aᵉ -->ᵉ Xᵉ
  | \ᵉ         \ᵉ    |
  |  \ᵉ Hᵉ  Lᵉ  Kᵉ \ᵉ   |
  |   \ᵉ         \ᵉ  |
  ∨ᵉ    ∨ᵉ         ∨ᵉ ∨ᵉ
  Bᵉ -->ᵉ Yᵉ         Yᵉ
```

with aᵉ [homotopic](foundation-core.homotopies.mdᵉ) diagonalᵉ mayᵉ beᵉ pastedᵉ intoᵉ aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
  Aᵉ ----->ᵉ Xᵉ
  |        |
  |        |
  ∨ᵉ        ∨ᵉ
  Bᵉ ----->ᵉ Y.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Xᵉ → Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  where

  horizontal-pasting-htpy-coherence-triangle-mapsᵉ :
    {diagonal-leftᵉ diagonal-rightᵉ : Aᵉ → Yᵉ} →
    diagonal-leftᵉ ~ᵉ diagonal-rightᵉ →
    coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ →
    coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  horizontal-pasting-htpy-coherence-triangle-mapsᵉ Lᵉ Hᵉ Kᵉ = (Hᵉ ∙hᵉ Lᵉ) ∙hᵉ Kᵉ

  horizontal-pasting-htpy-coherence-triangle-maps'ᵉ :
    {diagonal-leftᵉ diagonal-rightᵉ : Aᵉ → Yᵉ} →
    diagonal-leftᵉ ~ᵉ diagonal-rightᵉ →
    coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ →
    coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  horizontal-pasting-htpy-coherence-triangle-maps'ᵉ Lᵉ Hᵉ Kᵉ = Hᵉ ∙hᵉ (Lᵉ ∙hᵉ Kᵉ)

  horizontal-pasting-coherence-triangle-mapsᵉ :
    (diagonalᵉ : Aᵉ → Yᵉ) →
    coherence-triangle-maps'ᵉ diagonalᵉ bottomᵉ leftᵉ →
    coherence-triangle-mapsᵉ diagonalᵉ rightᵉ topᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  horizontal-pasting-coherence-triangle-mapsᵉ diagonalᵉ Hᵉ Kᵉ = Hᵉ ∙hᵉ Kᵉ

  compute-refl-htpy-horizontal-pasting-coherence-triangle-mapsᵉ :
    (diagonalᵉ : Aᵉ → Yᵉ) →
    (Hᵉ : coherence-triangle-maps'ᵉ diagonalᵉ bottomᵉ leftᵉ) →
    (Kᵉ : coherence-triangle-mapsᵉ diagonalᵉ rightᵉ topᵉ) →
    horizontal-pasting-htpy-coherence-triangle-mapsᵉ refl-htpyᵉ Hᵉ Kᵉ ~ᵉ
    horizontal-pasting-coherence-triangle-mapsᵉ diagonalᵉ Hᵉ Kᵉ
  compute-refl-htpy-horizontal-pasting-coherence-triangle-mapsᵉ diagonalᵉ Hᵉ Kᵉ xᵉ =
    right-whisker-concatᵉ right-unitᵉ (Kᵉ xᵉ)
```

Weᵉ canᵉ alsoᵉ considerᵉ pastingᵉ trianglesᵉ ofᵉ theᵉ formᵉ

```text
  Aᵉ -->ᵉ Xᵉ      Xᵉ
  |    ∧ᵉ     ∧ᵉ |
  | Hᵉ /ᵉ     /ᵉ  |
  |  /ᵉ     /ᵉ Kᵉ |
  ∨ᵉ /ᵉ     /ᵉ    ∨ᵉ
  Bᵉ      Bᵉ -->ᵉ Yᵉ .ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Xᵉ → Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  {diagonalᵉ : Bᵉ → Xᵉ}
  where

  horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ :
    coherence-triangle-maps'ᵉ topᵉ diagonalᵉ leftᵉ →
    coherence-triangle-mapsᵉ bottomᵉ rightᵉ diagonalᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ Hᵉ Kᵉ =
    (Kᵉ ·rᵉ leftᵉ) ∙hᵉ (rightᵉ ·lᵉ Hᵉ)
```