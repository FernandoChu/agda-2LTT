# Commuting triangles of homotopies

```agda
module foundation.commuting-triangles-of-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ triangleᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ) ofᵉ dependentᵉ functionsᵉ

```text
      topᵉ
    fᵉ ---->ᵉ gᵉ
     \ᵉ     /ᵉ
 leftᵉ \ᵉ   /ᵉ rightᵉ
       ∨ᵉ ∨ᵉ
        hᵉ
```

isᵉ saidᵉ to
{{#conceptᵉ "commute"ᵉ Disambiguation="triangleᵉ ofᵉ homotopies"ᵉ Agda=coherence-triangle-homotopiesᵉ}}
ifᵉ thereᵉ isᵉ aᵉ homotopyᵉ `leftᵉ ~ᵉ topᵉ ∙hᵉ right`.ᵉ

## Definitions

### Coherences of commuting triangles of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  coherence-triangle-homotopiesᵉ :
    (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-triangle-homotopiesᵉ leftᵉ rightᵉ topᵉ = leftᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ

  coherence-triangle-homotopies'ᵉ :
    (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-triangle-homotopies'ᵉ leftᵉ rightᵉ topᵉ = topᵉ ∙hᵉ rightᵉ ~ᵉ leftᵉ
```

## Properties

### Left whiskering commuting triangles of homotopies with respect to concatenation of homotopies

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
        topᵉ
     fᵉ ---->ᵉ gᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         hᵉ
```

where `fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ x`,ᵉ andᵉ considerᵉ aᵉ homotopyᵉ `Hᵉ : iᵉ ~ᵉ f`ᵉ forᵉ aᵉ fourthᵉ
dependentᵉ functionᵉ `iᵉ : (xᵉ : Aᵉ) → Bᵉ x`.ᵉ Thenᵉ theᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
           Hᵉ ∙hᵉ topᵉ
         iᵉ -------->ᵉ gᵉ
           \ᵉ       /ᵉ
  Hᵉ ∙hᵉ leftᵉ \ᵉ     /ᵉ rightᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
               hᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : iᵉ ~ᵉ fᵉ)
  (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ)
  where

  left-whisker-concat-coherence-triangle-homotopiesᵉ :
    (Tᵉ : coherence-triangle-homotopiesᵉ leftᵉ rightᵉ topᵉ) →
    coherence-triangle-homotopiesᵉ (Hᵉ ∙hᵉ leftᵉ) rightᵉ (Hᵉ ∙hᵉ topᵉ)
  left-whisker-concat-coherence-triangle-homotopiesᵉ Tᵉ xᵉ =
    left-whisker-concat-coherence-triangle-identificationsᵉ
      ( Hᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( topᵉ xᵉ)
      ( Tᵉ xᵉ)
```

### Right whiskering triangles of homotopies with respect to concatenation of homotopies

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
        topᵉ
     fᵉ ---->ᵉ gᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         hᵉ
```

where `fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ x`,ᵉ andᵉ considerᵉ aᵉ homotopyᵉ `Hᵉ : hᵉ ~ᵉ i`ᵉ forᵉ aᵉ fourthᵉ
dependentᵉ functionᵉ `iᵉ : (xᵉ : Aᵉ) → Bᵉ x`.ᵉ Thenᵉ theᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
              topᵉ
         fᵉ -------->ᵉ gᵉ
           \ᵉ       /ᵉ
  leftᵉ ∙hᵉ Hᵉ \ᵉ     /ᵉ rightᵉ ∙hᵉ Hᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
               iᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ)
  where

  right-whisker-concat-coherence-triangle-homotopiesᵉ :
    coherence-triangle-homotopiesᵉ leftᵉ rightᵉ topᵉ →
    {iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-triangle-homotopiesᵉ (leftᵉ ∙hᵉ Hᵉ) (rightᵉ ∙hᵉ Hᵉ) topᵉ
  right-whisker-concat-coherence-triangle-homotopiesᵉ Tᵉ Hᵉ xᵉ =
    right-whisker-concat-coherence-triangle-identificationsᵉ
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( topᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Tᵉ xᵉ)
```

### Left whiskering of commuting triangles of homotopies with respect to composition

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
        topᵉ
     fᵉ ---->ᵉ gᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         hᵉ
```

where `f`,ᵉ `g`,ᵉ andᵉ `h`ᵉ areᵉ mapsᵉ `Aᵉ → B`.ᵉ Furthermore,ᵉ considerᵉ aᵉ mapᵉ
`iᵉ : Bᵉ → X`.ᵉ Thenᵉ weᵉ obtainᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
           iᵉ ·lᵉ topᵉ
     iᵉ ∘ᵉ fᵉ -------->ᵉ iᵉ ∘ᵉ gᵉ
           \ᵉ       /ᵉ
  iᵉ ·lᵉ leftᵉ \ᵉ     /ᵉ iᵉ ·lᵉ rightᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
             iᵉ ∘ᵉ h.ᵉ
```

Thisᵉ notionᵉ ofᵉ whiskeringᵉ shouldᵉ beᵉ comparedᵉ to
[whiskeringᵉ higherᵉ homotopiesᵉ with respectᵉ to composition](foundation.whiskering-higher-homotopies-composition.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (iᵉ : Bᵉ → Xᵉ)
  {fᵉ gᵉ hᵉ : Aᵉ → Bᵉ} (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ)
  where

  left-whisker-comp-coherence-triangle-homotopiesᵉ :
    (Tᵉ : coherence-triangle-homotopiesᵉ leftᵉ rightᵉ topᵉ) →
    coherence-triangle-homotopiesᵉ (iᵉ ·lᵉ leftᵉ) (iᵉ ·lᵉ rightᵉ) (iᵉ ·lᵉ topᵉ)
  left-whisker-comp-coherence-triangle-homotopiesᵉ Tᵉ xᵉ =
    map-coherence-triangle-identificationsᵉ iᵉ (leftᵉ xᵉ) (rightᵉ xᵉ) (topᵉ xᵉ) (Tᵉ xᵉ)
```

### Right whiskering commuting triangles of homotopies with respect to composition

Considerᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
        topᵉ
     fᵉ ---->ᵉ gᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         hᵉ
```

where `f`,ᵉ `g`,ᵉ andᵉ `h`ᵉ areᵉ mapsᵉ `Aᵉ → B`.ᵉ Furthermore,ᵉ considerᵉ aᵉ mapᵉ
`iᵉ : Xᵉ → A`.ᵉ Thenᵉ weᵉ obtainᵉ aᵉ commutingᵉ triangleᵉ ofᵉ homotopiesᵉ

```text
           topᵉ ·rᵉ iᵉ
     fᵉ ∘ᵉ iᵉ -------->ᵉ gᵉ ∘ᵉ iᵉ
           \ᵉ       /ᵉ
  leftᵉ ·rᵉ iᵉ \ᵉ     /ᵉ rightᵉ ·rᵉ iᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
             hᵉ ∘ᵉ i.ᵉ
```

Thisᵉ notionᵉ ofᵉ whiskeringᵉ shouldᵉ beᵉ comparedᵉ to
[whiskeringᵉ higherᵉ homotopiesᵉ with respectᵉ to composition](foundation.whiskering-higher-homotopies-composition.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  {fᵉ gᵉ hᵉ : Aᵉ → Bᵉ} (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ hᵉ) (topᵉ : fᵉ ~ᵉ gᵉ)
  where

  right-whisker-comp-coherence-triangle-homotopiesᵉ :
    (Tᵉ : coherence-triangle-homotopiesᵉ leftᵉ rightᵉ topᵉ) (iᵉ : Xᵉ → Aᵉ) →
    coherence-triangle-homotopiesᵉ (leftᵉ ·rᵉ iᵉ) (rightᵉ ·rᵉ iᵉ) (topᵉ ·rᵉ iᵉ)
  right-whisker-comp-coherence-triangle-homotopiesᵉ Tᵉ iᵉ = Tᵉ ∘ᵉ iᵉ
```