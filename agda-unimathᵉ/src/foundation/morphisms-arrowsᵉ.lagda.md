# Morphisms of arrows

```agda
module foundation.morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.postcomposition-functionsᵉ
open import foundation-core.precomposition-functionsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "morphismᵉ ofᵉ arrows"ᵉ Agda=hom-arrowᵉ}} fromᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ
to aᵉ functionᵉ `gᵉ : Xᵉ → Y`ᵉ isᵉ aᵉ [triple](foundation.dependent-pair-types.mdᵉ)
`(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ consistingᵉ ofᵉ mapsᵉ `iᵉ : Aᵉ → X`ᵉ andᵉ `jᵉ : Bᵉ → Y`ᵉ andᵉ aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) `Hᵉ : jᵉ ∘ᵉ fᵉ ~ᵉ gᵉ ∘ᵉ i`ᵉ witnessingᵉ thatᵉ
theᵉ squareᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ Morphismsᵉ ofᵉ arrowsᵉ
canᵉ beᵉ composedᵉ horizontallyᵉ orᵉ verticallyᵉ byᵉ pastingᵉ ofᵉ squares.ᵉ

## Definitions

### Morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  coherence-hom-arrowᵉ : (Aᵉ → Xᵉ) → (Bᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-hom-arrowᵉ iᵉ = coherence-square-mapsᵉ iᵉ fᵉ gᵉ

  hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-arrowᵉ = Σᵉ (Aᵉ → Xᵉ) (λ iᵉ → Σᵉ (Bᵉ → Yᵉ) (coherence-hom-arrowᵉ iᵉ))

  map-domain-hom-arrowᵉ : hom-arrowᵉ → Aᵉ → Xᵉ
  map-domain-hom-arrowᵉ = pr1ᵉ

  map-codomain-hom-arrowᵉ : hom-arrowᵉ → Bᵉ → Yᵉ
  map-codomain-hom-arrowᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  coh-hom-arrowᵉ :
    (hᵉ : hom-arrowᵉ) →
    coherence-hom-arrowᵉ (map-domain-hom-arrowᵉ hᵉ) (map-codomain-hom-arrowᵉ hᵉ)
  coh-hom-arrowᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

## Operations

### The identity morphism of arrows

Theᵉ identityᵉ morphismᵉ ofᵉ arrowsᵉ isᵉ definedᵉ asᵉ

```text
        idᵉ
    Aᵉ ----->ᵉ Aᵉ
    |        |
  fᵉ |        | fᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Bᵉ
        idᵉ
```

where theᵉ homotopyᵉ `idᵉ ∘ᵉ fᵉ ~ᵉ fᵉ ∘ᵉ id`ᵉ isᵉ theᵉ reflexivityᵉ homotopy.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  id-hom-arrowᵉ : hom-arrowᵉ fᵉ fᵉ
  pr1ᵉ id-hom-arrowᵉ = idᵉ
  pr1ᵉ (pr2ᵉ id-hom-arrowᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ id-hom-arrowᵉ) = refl-htpyᵉ
```

### Composition of morphisms of arrows

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
        α₀ᵉ       β₀ᵉ
    Aᵉ ----->ᵉ Xᵉ ----->ᵉ Uᵉ
    |        |        |
  fᵉ |   αᵉ  gᵉ |   βᵉ    | hᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ ----->ᵉ V.ᵉ
        α₁ᵉ       β₁ᵉ
```

Thenᵉ theᵉ outerᵉ rectangleᵉ commutesᵉ byᵉ horizontalᵉ pastingᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ
maps.ᵉ Theᵉ {{#conceptᵉ "composition"ᵉ Disambiguation="morphismᵉ ofᵉ arrows"ᵉ}} ofᵉ
`βᵉ : gᵉ → h`ᵉ with `αᵉ : fᵉ → g`ᵉ isᵉ thereforeᵉ definedᵉ to beᵉ

```text
        β₀ᵉ ∘ᵉ α₀ᵉ
    Aᵉ ---------->ᵉ Uᵉ
    |             |
  fᵉ |    αᵉ □ᵉ βᵉ    | hᵉ
    ∨ᵉ             ∨ᵉ
    Bᵉ ---------->ᵉ V.ᵉ
        β₁ᵉ ∘ᵉ α₁ᵉ
```

**Note.**ᵉ Associativityᵉ andᵉ theᵉ unitᵉ lawsᵉ forᵉ compositionᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ
areᵉ provenᵉ in
[Homotopiesᵉ ofᵉ morphismsᵉ ofᵉ arrows](foundation.homotopies-morphisms-arrows.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (bᵉ : hom-arrowᵉ gᵉ hᵉ) (aᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  map-domain-comp-hom-arrowᵉ : Aᵉ → Uᵉ
  map-domain-comp-hom-arrowᵉ =
    map-domain-hom-arrowᵉ gᵉ hᵉ bᵉ ∘ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ aᵉ

  map-codomain-comp-hom-arrowᵉ : Bᵉ → Vᵉ
  map-codomain-comp-hom-arrowᵉ =
    map-codomain-hom-arrowᵉ gᵉ hᵉ bᵉ ∘ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ aᵉ

  coh-comp-hom-arrowᵉ :
    coherence-hom-arrowᵉ fᵉ hᵉ
      ( map-domain-comp-hom-arrowᵉ)
      ( map-codomain-comp-hom-arrowᵉ)
  coh-comp-hom-arrowᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ aᵉ)
      ( map-domain-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( fᵉ)
      ( gᵉ)
      ( hᵉ)
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ aᵉ)
      ( map-codomain-hom-arrowᵉ gᵉ hᵉ bᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ aᵉ)
      ( coh-hom-arrowᵉ gᵉ hᵉ bᵉ)

  comp-hom-arrowᵉ : hom-arrowᵉ fᵉ hᵉ
  pr1ᵉ comp-hom-arrowᵉ =
    map-domain-comp-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ comp-hom-arrowᵉ) =
    map-codomain-comp-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ comp-hom-arrowᵉ) =
    coh-comp-hom-arrowᵉ
```

### Transposing morphisms of arrows

Theᵉ {{#conceptᵉ "transposition"ᵉ Disambiguation="morphismᵉ ofᵉ arrows"ᵉ}} ofᵉ aᵉ
morphismᵉ ofᵉ arrowsᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

isᵉ theᵉ morphismᵉ ofᵉ arrowsᵉ

```text
        fᵉ
    Aᵉ ----->ᵉ Bᵉ
    |        |
  iᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Xᵉ ----->ᵉ Y.ᵉ
        gᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  map-domain-transpose-hom-arrowᵉ : Aᵉ → Bᵉ
  map-domain-transpose-hom-arrowᵉ = fᵉ

  map-codomain-transpose-hom-arrowᵉ : Xᵉ → Yᵉ
  map-codomain-transpose-hom-arrowᵉ = gᵉ

  coh-transpose-hom-arrowᵉ :
    coherence-hom-arrowᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-domain-transpose-hom-arrowᵉ)
      ( map-codomain-transpose-hom-arrowᵉ)
  coh-transpose-hom-arrowᵉ =
    inv-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ)

  transpose-hom-arrowᵉ :
    hom-arrowᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ) (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr1ᵉ transpose-hom-arrowᵉ = map-domain-transpose-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ transpose-hom-arrowᵉ) = map-codomain-transpose-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ transpose-hom-arrowᵉ) = coh-transpose-hom-arrowᵉ
```

### Morphisms of arrows obtained from cones over cospans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  hom-arrow-coneᵉ : hom-arrowᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) gᵉ
  pr1ᵉ hom-arrow-coneᵉ = horizontal-map-coneᵉ fᵉ gᵉ cᵉ
  pr1ᵉ (pr2ᵉ hom-arrow-coneᵉ) = fᵉ
  pr2ᵉ (pr2ᵉ hom-arrow-coneᵉ) = coherence-square-coneᵉ fᵉ gᵉ cᵉ

  hom-arrow-cone'ᵉ : hom-arrowᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) fᵉ
  hom-arrow-cone'ᵉ =
    transpose-hom-arrowᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) gᵉ hom-arrow-coneᵉ
```

### Cones over cospans obtained from morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  cone-hom-arrowᵉ : coneᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ) gᵉ Aᵉ
  pr1ᵉ cone-hom-arrowᵉ = fᵉ
  pr1ᵉ (pr2ᵉ cone-hom-arrowᵉ) = map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ
  pr2ᵉ (pr2ᵉ cone-hom-arrowᵉ) = coh-hom-arrowᵉ fᵉ gᵉ hᵉ
```

### Morphisms of arrows are preserved under homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  where

  hom-arrow-htpy-sourceᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) (gᵉ : Xᵉ → Yᵉ) →
    hom-arrowᵉ fᵉ gᵉ → hom-arrowᵉ f'ᵉ gᵉ
  hom-arrow-htpy-sourceᵉ F'ᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) = (iᵉ ,ᵉ jᵉ ,ᵉ (jᵉ ·lᵉ F'ᵉ) ∙hᵉ Hᵉ)

  hom-arrow-htpy-targetᵉ :
    (fᵉ : Aᵉ → Bᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    hom-arrowᵉ fᵉ gᵉ → hom-arrowᵉ fᵉ g'ᵉ
  hom-arrow-htpy-targetᵉ fᵉ Gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) = (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ ∙hᵉ (Gᵉ ·rᵉ iᵉ))

  hom-arrow-htpyᵉ :
    {fᵉ f'ᵉ : Aᵉ → Bᵉ} (F'ᵉ : f'ᵉ ~ᵉ fᵉ) {gᵉ g'ᵉ : Xᵉ → Yᵉ} (Gᵉ : gᵉ ~ᵉ g'ᵉ) →
    hom-arrowᵉ fᵉ gᵉ → hom-arrowᵉ f'ᵉ g'ᵉ
  hom-arrow-htpyᵉ F'ᵉ Gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) = (iᵉ ,ᵉ jᵉ ,ᵉ (jᵉ ·lᵉ F'ᵉ) ∙hᵉ Hᵉ ∙hᵉ (Gᵉ ·rᵉ iᵉ))
```

### Dependent products of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Iᵉ : UUᵉ l5ᵉ} {Aᵉ : Iᵉ → UUᵉ l1ᵉ} {Bᵉ : Iᵉ → UUᵉ l2ᵉ} {Xᵉ : Iᵉ → UUᵉ l3ᵉ} {Yᵉ : Iᵉ → UUᵉ l4ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (gᵉ : (iᵉ : Iᵉ) → Xᵉ iᵉ → Yᵉ iᵉ)
  (αᵉ : (iᵉ : Iᵉ) → hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ))
  where

  Π-hom-arrowᵉ : hom-arrowᵉ (map-Πᵉ fᵉ) (map-Πᵉ gᵉ)
  pr1ᵉ Π-hom-arrowᵉ =
    map-Πᵉ (λ iᵉ → map-domain-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
  pr1ᵉ (pr2ᵉ Π-hom-arrowᵉ) =
    map-Πᵉ (λ iᵉ → map-codomain-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
  pr2ᵉ (pr2ᵉ Π-hom-arrowᵉ) =
    htpy-map-Πᵉ (λ iᵉ → coh-hom-arrowᵉ (fᵉ iᵉ) (gᵉ iᵉ) (αᵉ iᵉ))
```

### Morphisms of arrows give morphisms of precomposition arrows

Aᵉ morphismᵉ ofᵉ arrowsᵉ `αᵉ : fᵉ → g`ᵉ givesᵉ aᵉ morphismᵉ ofᵉ precompositionᵉ arrowsᵉ
`(-)^αᵉ : (–)^gᵉ → (–)^f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  precomp-hom-arrowᵉ :
    {lᵉ : Level} (Sᵉ : UUᵉ lᵉ) → hom-arrowᵉ (precompᵉ gᵉ Sᵉ) (precompᵉ fᵉ Sᵉ)
  pr1ᵉ (precomp-hom-arrowᵉ Sᵉ) =
    precompᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) Sᵉ
  pr1ᵉ (pr2ᵉ (precomp-hom-arrowᵉ Sᵉ)) =
    precompᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ) Sᵉ
  pr2ᵉ (pr2ᵉ (precomp-hom-arrowᵉ Sᵉ)) hᵉ =
    invᵉ (eq-htpyᵉ (hᵉ ·lᵉ coh-hom-arrowᵉ fᵉ gᵉ αᵉ))
```

### Morphisms of arrows give morphisms of postcomposition arrows

Aᵉ morphismᵉ ofᵉ arrowsᵉ `αᵉ : fᵉ → g`ᵉ givesᵉ aᵉ morphismᵉ ofᵉ postcompositionᵉ arrowsᵉ
`α^(-ᵉ) : f^(-ᵉ) → g^(-)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  postcomp-hom-arrowᵉ :
    {lᵉ : Level} (Sᵉ : UUᵉ lᵉ) → hom-arrowᵉ (postcompᵉ Sᵉ fᵉ) (postcompᵉ Sᵉ gᵉ)
  pr1ᵉ (postcomp-hom-arrowᵉ Sᵉ) =
    postcompᵉ Sᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr1ᵉ (pr2ᵉ (postcomp-hom-arrowᵉ Sᵉ)) =
    postcompᵉ Sᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr2ᵉ (pr2ᵉ (postcomp-hom-arrowᵉ Sᵉ)) hᵉ =
    eq-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ ·rᵉ hᵉ)
```

## See also

-ᵉ [Equivalencesᵉ ofᵉ arrows](foundation.equivalences-arrows.mdᵉ)
-ᵉ [Morphismsᵉ ofᵉ twistedᵉ arrows](foundation.morphisms-twisted-arrows.md).ᵉ
-ᵉ [Fiberedᵉ maps](foundation.fibered-maps.mdᵉ) forᵉ theᵉ sameᵉ conceptᵉ underᵉ aᵉ
  differentᵉ name.ᵉ
-ᵉ [Theᵉ pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ) isᵉ anᵉ
  operationᵉ thatᵉ returnsᵉ aᵉ morphismᵉ ofᵉ arrowsᵉ fromᵉ aᵉ diagonalᵉ map.ᵉ
-ᵉ [Homotopiesᵉ ofᵉ morphismsᵉ ofᵉ arrows](foundation.homotopies-morphisms-arrows.mdᵉ)