# Commuting squares of maps

```agda
module foundation-core.commuting-squares-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ mapsᵉ

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Yᵉ
          bottomᵉ
```

isᵉ saidᵉ to beᵉ aᵉ {{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="maps"ᵉ}} ofᵉ mapsᵉ ifᵉ
thereᵉ isᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ)

```text
  bottomᵉ ∘ᵉ leftᵉ ~ᵉ rightᵉ ∘ᵉ top.ᵉ
```

Suchᵉ aᵉ homotopyᵉ isᵉ calledᵉ theᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ maps"ᵉ Agda=coherence-square-mapsᵉ}}
ofᵉ theᵉ commutingᵉ square.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (topᵉ : Cᵉ → Bᵉ) (leftᵉ : Cᵉ → Aᵉ) (rightᵉ : Bᵉ → Xᵉ) (bottomᵉ : Aᵉ → Xᵉ)
  where

  coherence-square-mapsᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-square-mapsᵉ = bottomᵉ ∘ᵉ leftᵉ ~ᵉ rightᵉ ∘ᵉ topᵉ

  coherence-square-maps'ᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-square-maps'ᵉ = rightᵉ ∘ᵉ topᵉ ~ᵉ bottomᵉ ∘ᵉ leftᵉ
```

## Properties

### Pasting commuting squares horizontally

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (top-leftᵉ : Aᵉ → Bᵉ) (top-rightᵉ : Bᵉ → Cᵉ)
  (leftᵉ : Aᵉ → Xᵉ) (midᵉ : Bᵉ → Yᵉ) (rightᵉ : Cᵉ → Zᵉ)
  (bottom-leftᵉ : Xᵉ → Yᵉ) (bottom-rightᵉ : Yᵉ → Zᵉ)
  where

  pasting-horizontal-coherence-square-mapsᵉ :
    coherence-square-mapsᵉ top-leftᵉ leftᵉ midᵉ bottom-leftᵉ →
    coherence-square-mapsᵉ top-rightᵉ midᵉ rightᵉ bottom-rightᵉ →
    coherence-square-mapsᵉ
      (top-rightᵉ ∘ᵉ top-leftᵉ) leftᵉ rightᵉ (bottom-rightᵉ ∘ᵉ bottom-leftᵉ)
  pasting-horizontal-coherence-square-mapsᵉ sq-leftᵉ sq-rightᵉ =
    (bottom-rightᵉ ·lᵉ sq-leftᵉ) ∙hᵉ (sq-rightᵉ ·rᵉ top-leftᵉ)

  pasting-horizontal-up-to-htpy-coherence-square-mapsᵉ :
    {topᵉ : Aᵉ → Cᵉ} (Hᵉ : coherence-triangle-mapsᵉ topᵉ top-rightᵉ top-leftᵉ)
    {bottomᵉ : Xᵉ → Zᵉ}
    (Kᵉ : coherence-triangle-mapsᵉ bottomᵉ bottom-rightᵉ bottom-leftᵉ) →
    coherence-square-mapsᵉ top-leftᵉ leftᵉ midᵉ bottom-leftᵉ →
    coherence-square-mapsᵉ top-rightᵉ midᵉ rightᵉ bottom-rightᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  pasting-horizontal-up-to-htpy-coherence-square-mapsᵉ Hᵉ Kᵉ sq-leftᵉ sq-rightᵉ =
    ( ( Kᵉ ·rᵉ leftᵉ) ∙hᵉ
      ( pasting-horizontal-coherence-square-mapsᵉ sq-leftᵉ sq-rightᵉ)) ∙hᵉ
    ( inv-htpyᵉ (rightᵉ ·lᵉ Hᵉ))
```

### Pasting commuting squares vertically

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (topᵉ : Aᵉ → Xᵉ)
  (left-topᵉ : Aᵉ → Bᵉ) (right-topᵉ : Xᵉ → Yᵉ)
  (midᵉ : Bᵉ → Yᵉ)
  (left-bottomᵉ : Bᵉ → Cᵉ) (right-bottomᵉ : Yᵉ → Zᵉ)
  (bottomᵉ : Cᵉ → Zᵉ)
  where

  pasting-vertical-coherence-square-mapsᵉ :
    coherence-square-mapsᵉ topᵉ left-topᵉ right-topᵉ midᵉ →
    coherence-square-mapsᵉ midᵉ left-bottomᵉ right-bottomᵉ bottomᵉ →
    coherence-square-mapsᵉ
      topᵉ (left-bottomᵉ ∘ᵉ left-topᵉ) (right-bottomᵉ ∘ᵉ right-topᵉ) bottomᵉ
  pasting-vertical-coherence-square-mapsᵉ sq-topᵉ sq-bottomᵉ =
    (sq-bottomᵉ ·rᵉ left-topᵉ) ∙hᵉ (right-bottomᵉ ·lᵉ sq-topᵉ)

  pasting-vertical-up-to-htpy-coherence-square-mapsᵉ :
    {leftᵉ : Aᵉ → Cᵉ} (Hᵉ : coherence-triangle-mapsᵉ leftᵉ left-bottomᵉ left-topᵉ)
    {rightᵉ : Xᵉ → Zᵉ} (Kᵉ : coherence-triangle-mapsᵉ rightᵉ right-bottomᵉ right-topᵉ) →
    coherence-square-mapsᵉ topᵉ left-topᵉ right-topᵉ midᵉ →
    coherence-square-mapsᵉ midᵉ left-bottomᵉ right-bottomᵉ bottomᵉ →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  pasting-vertical-up-to-htpy-coherence-square-mapsᵉ Hᵉ Kᵉ sq-topᵉ sq-bottomᵉ =
    ( ( bottomᵉ ·lᵉ Hᵉ) ∙hᵉ
      ( pasting-vertical-coherence-square-mapsᵉ sq-topᵉ sq-bottomᵉ)) ∙hᵉ
    ( inv-htpyᵉ (Kᵉ ·rᵉ topᵉ))
```

### Associativity of horizontal pasting

**Proof:**ᵉ Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
        α₀ᵉ       β₀ᵉ       γ₀ᵉ
    Aᵉ ----->ᵉ Xᵉ ----->ᵉ Uᵉ ----->ᵉ Kᵉ
    |        |        |        |
  fᵉ |   αᵉ  gᵉ |   βᵉ  hᵉ |   γᵉ    | iᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ ----->ᵉ Vᵉ ----->ᵉ L.ᵉ
        α₁ᵉ       β₁ᵉ       γ₁ᵉ
```

Thenᵉ weᵉ canᵉ makeᵉ theᵉ followingᵉ calculation,ᵉ in whichᵉ weᵉ writeᵉ `□`ᵉ forᵉ horizontalᵉ
pastingᵉ ofᵉ squaresᵉ:

```text
  (αᵉ □ᵉ βᵉ) □ᵉ γᵉ
  ＝ᵉ (γ₁ᵉ ·lᵉ ((β₁ᵉ ·lᵉ αᵉ) ∙hᵉ (βᵉ ·rᵉ α₀ᵉ))) ∙hᵉ (γᵉ ·rᵉ (β₀ᵉ ∘ᵉ α₀ᵉ))
  ＝ᵉ ((γ₁ᵉ ·lᵉ (β₁ᵉ ·lᵉ αᵉ)) ∙hᵉ (γ₁ᵉ ·lᵉ (βᵉ ·rᵉ α₀ᵉ))) ∙hᵉ (γᵉ ·rᵉ (β₀ᵉ ∘ᵉ α₀ᵉ))
  ＝ᵉ ((γ₁ᵉ ∘ᵉ β₁ᵉ) ·lᵉ αᵉ) ∙hᵉ (((γ₁ᵉ ·lᵉ βᵉ) ·rᵉ α₀ᵉ) ∙hᵉ ((γᵉ ·rᵉ β₀ᵉ) ·rᵉ α₀ᵉ))
  ＝ᵉ ((γ₁ᵉ ∘ᵉ β₁ᵉ) ·lᵉ αᵉ) ∙hᵉ (((γ₁ᵉ ·lᵉ βᵉ) ∙hᵉ (γᵉ ·rᵉ β₀ᵉ)) ·rᵉ α₀ᵉ)
  ＝ᵉ αᵉ □ᵉ (βᵉ □ᵉ γᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  {Kᵉ : UUᵉ l7ᵉ} {Lᵉ : UUᵉ l8ᵉ}
  (α₀ᵉ : Aᵉ → Xᵉ) (β₀ᵉ : Xᵉ → Uᵉ) (γ₀ᵉ : Uᵉ → Kᵉ)
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (iᵉ : Kᵉ → Lᵉ)
  (α₁ᵉ : Bᵉ → Yᵉ) (β₁ᵉ : Yᵉ → Vᵉ) (γ₁ᵉ : Vᵉ → Lᵉ)
  (αᵉ : coherence-square-mapsᵉ α₀ᵉ fᵉ gᵉ α₁ᵉ)
  (βᵉ : coherence-square-mapsᵉ β₀ᵉ gᵉ hᵉ β₁ᵉ)
  (γᵉ : coherence-square-mapsᵉ γ₀ᵉ hᵉ iᵉ γ₁ᵉ)
  where

  assoc-pasting-horizontal-coherence-square-mapsᵉ :
    pasting-horizontal-coherence-square-mapsᵉ
      ( β₀ᵉ ∘ᵉ α₀ᵉ)
      ( γ₀ᵉ)
      ( fᵉ)
      ( hᵉ)
      ( iᵉ)
      ( β₁ᵉ ∘ᵉ α₁ᵉ)
      ( γ₁ᵉ)
      ( pasting-horizontal-coherence-square-mapsᵉ α₀ᵉ β₀ᵉ fᵉ gᵉ hᵉ α₁ᵉ β₁ᵉ αᵉ βᵉ)
      ( γᵉ) ~ᵉ
    pasting-horizontal-coherence-square-mapsᵉ
      ( α₀ᵉ)
      ( γ₀ᵉ ∘ᵉ β₀ᵉ)
      ( fᵉ)
      ( gᵉ)
      ( iᵉ)
      ( α₁ᵉ)
      ( γ₁ᵉ ∘ᵉ β₁ᵉ)
      ( αᵉ)
      ( pasting-horizontal-coherence-square-mapsᵉ β₀ᵉ γ₀ᵉ gᵉ hᵉ iᵉ β₁ᵉ γ₁ᵉ βᵉ γᵉ)
  assoc-pasting-horizontal-coherence-square-mapsᵉ aᵉ =
    ( apᵉ
      ( _∙ᵉ _)
      ( ( ap-concatᵉ γ₁ᵉ (apᵉ β₁ᵉ (αᵉ aᵉ)) (βᵉ (α₀ᵉ aᵉ))) ∙ᵉ
        ( invᵉ (apᵉ (_∙ᵉ _) (ap-compᵉ γ₁ᵉ β₁ᵉ (αᵉ aᵉ)))))) ∙ᵉ
    ( assocᵉ (apᵉ (γ₁ᵉ ∘ᵉ β₁ᵉ) (αᵉ aᵉ)) (apᵉ γ₁ᵉ (βᵉ (α₀ᵉ aᵉ))) (γᵉ (β₀ᵉ (α₀ᵉ aᵉ))))
```

### The unit laws for horizontal pasting of commuting squares of maps

#### The left unit law

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (iᵉ : Aᵉ → Xᵉ) (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (jᵉ : Bᵉ → Yᵉ)
  (αᵉ : coherence-square-mapsᵉ iᵉ fᵉ gᵉ jᵉ)
  where

  left-unit-law-pasting-horizontal-coherence-square-mapsᵉ :
    pasting-horizontal-coherence-square-mapsᵉ idᵉ iᵉ fᵉ fᵉ gᵉ idᵉ jᵉ refl-htpyᵉ αᵉ ~ᵉ αᵉ
  left-unit-law-pasting-horizontal-coherence-square-mapsᵉ = refl-htpyᵉ
```

### The right unit law

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (iᵉ : Aᵉ → Xᵉ) (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (jᵉ : Bᵉ → Yᵉ)
  (αᵉ : coherence-square-mapsᵉ iᵉ fᵉ gᵉ jᵉ)
  where

  right-unit-law-pasting-horizontal-coherence-square-mapsᵉ :
    pasting-horizontal-coherence-square-mapsᵉ iᵉ idᵉ fᵉ gᵉ gᵉ jᵉ idᵉ αᵉ refl-htpyᵉ ~ᵉ αᵉ
  right-unit-law-pasting-horizontal-coherence-square-mapsᵉ aᵉ =
    right-unitᵉ ∙ᵉ ap-idᵉ (αᵉ aᵉ)
```

### Inverting squares horizontally and vertically

Ifᵉ theᵉ horizontal/verticalᵉ mapsᵉ in aᵉ commutingᵉ squareᵉ areᵉ bothᵉ
[equivalences](foundation-core.equivalences.md),ᵉ thenᵉ theᵉ squareᵉ remainsᵉ
commutingᵉ ifᵉ weᵉ invertᵉ thoseᵉ equivalences.ᵉ

```agda
horizontal-inv-equiv-coherence-square-mapsᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ ≃ᵉ Bᵉ) (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Yᵉ) (bottomᵉ : Xᵉ ≃ᵉ Yᵉ) →
  coherence-square-mapsᵉ (map-equivᵉ topᵉ) leftᵉ rightᵉ (map-equivᵉ bottomᵉ) →
  coherence-square-mapsᵉ (map-inv-equivᵉ topᵉ) rightᵉ leftᵉ (map-inv-equivᵉ bottomᵉ)
horizontal-inv-equiv-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ bᵉ =
  map-eq-transpose-equiv-invᵉ
    ( bottomᵉ)
    ( ( apᵉ rightᵉ (invᵉ (is-section-map-inv-equivᵉ topᵉ bᵉ))) ∙ᵉ
      ( invᵉ (Hᵉ (map-inv-equivᵉ topᵉ bᵉ))))

vertical-inv-equiv-coherence-square-mapsᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Bᵉ) (leftᵉ : Aᵉ ≃ᵉ Xᵉ) (rightᵉ : Bᵉ ≃ᵉ Yᵉ) (bottomᵉ : Xᵉ → Yᵉ) →
  coherence-square-mapsᵉ topᵉ (map-equivᵉ leftᵉ) (map-equivᵉ rightᵉ) bottomᵉ →
  coherence-square-mapsᵉ bottomᵉ (map-inv-equivᵉ leftᵉ) (map-inv-equivᵉ rightᵉ) topᵉ
vertical-inv-equiv-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
  map-eq-transpose-equivᵉ
    ( rightᵉ)
    ( ( invᵉ (Hᵉ (map-inv-equivᵉ leftᵉ xᵉ))) ∙ᵉ
      ( apᵉ bottomᵉ (is-section-map-inv-equivᵉ leftᵉ xᵉ)))

coherence-square-maps-inv-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ ≃ᵉ Bᵉ) (leftᵉ : Aᵉ ≃ᵉ Xᵉ) (rightᵉ : Bᵉ ≃ᵉ Yᵉ) (bottomᵉ : Xᵉ ≃ᵉ Yᵉ) →
  coherence-square-mapsᵉ
    ( map-equivᵉ topᵉ)
    ( map-equivᵉ leftᵉ)
    ( map-equivᵉ rightᵉ)
    ( map-equivᵉ bottomᵉ) →
  coherence-square-mapsᵉ
    ( map-inv-equivᵉ bottomᵉ)
    ( map-inv-equivᵉ rightᵉ)
    ( map-inv-equivᵉ leftᵉ)
    ( map-inv-equivᵉ topᵉ)
coherence-square-maps-inv-equivᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ =
  vertical-inv-equiv-coherence-square-mapsᵉ
    ( map-inv-equivᵉ topᵉ)
    ( rightᵉ)
    ( leftᵉ)
    ( map-inv-equivᵉ bottomᵉ)
    ( horizontal-inv-equiv-coherence-square-mapsᵉ
      ( topᵉ)
      ( map-equivᵉ leftᵉ)
      ( map-equivᵉ rightᵉ)
      ( bottomᵉ)
      ( Hᵉ))
```

## See also

Severalᵉ structuresᵉ makeᵉ essentialᵉ useᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ mapsᵉ:

-ᵉ [Conesᵉ overᵉ cospanᵉ diagrams](foundation.cones-over-cospan-diagrams.mdᵉ)
-ᵉ [Coconesᵉ underᵉ spanᵉ diagrams](synthetic-homotopy-theory.cocones-under-spans.mdᵉ)
-ᵉ [Morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)