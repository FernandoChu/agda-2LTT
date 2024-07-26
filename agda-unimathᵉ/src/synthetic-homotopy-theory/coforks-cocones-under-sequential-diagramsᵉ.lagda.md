# Correspondence between cocones under sequential diagrams and certain coforks

```agda
module synthetic-homotopy-theory.coforks-cocones-under-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-prisms-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-double-arrowsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-double-arrowsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-concatenationᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-coforksᵉ
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrowsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrowsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)

```text
      a₀ᵉ      a₁ᵉ      a₂ᵉ
  A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
```

inducesᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ)

```text
  Σᵉ (nᵉ : ℕᵉ) Aₙᵉ
      | |
   idᵉ | | totᵉ ₍₊₁₎ᵉ aᵉ
      | |
      ∨ᵉ ∨ᵉ
  Σᵉ (nᵉ : ℕᵉ) Aₙᵉ
```

where `totᵉ ₍₊₁₎ᵉ a`ᵉ computesᵉ theᵉ successorᵉ onᵉ theᵉ baseᵉ andᵉ appliesᵉ theᵉ mapᵉ
`aₙᵉ : Aₙᵉ → Aₙ₊₁`ᵉ onᵉ theᵉ fiber.ᵉ

[Morphisms](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ) andᵉ
[equivalences](synthetic-homotopy-theory.equivalences-sequential-diagrams.mdᵉ) ofᵉ
sequentialᵉ diagramsᵉ induceᵉ [morphisms](foundation.morphisms-double-arrows.mdᵉ)
andᵉ [equivalences](foundation.equivalences-double-arrows.mdᵉ) ofᵉ theᵉ
corresepondingᵉ doubleᵉ arrows,ᵉ respectively.ᵉ

Theᵉ data ofᵉ aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ) underᵉ
`A`ᵉ:

```text
        aₙᵉ
  Aₙᵉ ------>ᵉ Aₙ₊₁ᵉ
    \ᵉ       /ᵉ
     \ᵉ  Hₙᵉ /ᵉ
   iₙᵉ \ᵉ   /ᵉ iₙ₊₁ᵉ
       ∨ᵉ ∨ᵉ
        Xᵉ
```

canᵉ beᵉ [uncurried](foundation.dependent-pair-types.mdᵉ) to getᵉ theᵉ equivalentᵉ
diagramᵉ comprisingᵉ ofᵉ theᵉ singleᵉ triangleᵉ

```text
           totᵉ ₍₊₁₎ᵉ aᵉ
  (Σᵉ ℕᵉ Aᵉ) ------------>ᵉ (Σᵉ ℕᵉ Aᵉ)
         \ᵉ             /ᵉ
           \ᵉ         /ᵉ
          iᵉ  \ᵉ     /ᵉ  iᵉ
               ∨ᵉ ∨ᵉ
                Xᵉ
```

whichᵉ isᵉ exactlyᵉ aᵉ [cofork](synthetic-homotopy-theory.coforks.mdᵉ) ofᵉ theᵉ
identityᵉ mapᵉ andᵉ `totᵉ ₍₊₁₎ᵉ a`.ᵉ

Underᵉ thisᵉ mappingᵉ
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
correspondᵉ to
[coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md),ᵉ
whichᵉ isᵉ formalizedᵉ in
[universal-property-sequential-colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).ᵉ

Inᵉ theᵉ dependentᵉ setting,ᵉ
[dependentᵉ cocones](synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams.mdᵉ)
overᵉ aᵉ coconeᵉ `c`ᵉ correspondᵉ to
[dependentᵉ coforks](synthetic-homotopy-theory.dependent-coforks.mdᵉ) overᵉ theᵉ
coforkᵉ inducedᵉ byᵉ `c`.ᵉ

Additionally,ᵉ
[morphisms](synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams.mdᵉ)
ofᵉ coconesᵉ underᵉ morphismsᵉ ofᵉ sequentialᵉ diagramsᵉ induceᵉ
[morphisms](synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows.mdᵉ)
ofᵉ coforksᵉ underᵉ theᵉ inducedᵉ morphismsᵉ ofᵉ doubleᵉ arrows.ᵉ Itᵉ followsᵉ thatᵉ
[equivalences](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.mdᵉ)
ofᵉ coconesᵉ underᵉ equivalencesᵉ ofᵉ sequentialᵉ diagramsᵉ induceᵉ
[equivalences](synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.mdᵉ)
ofᵉ coforksᵉ underᵉ theᵉ inducedᵉ equivalencesᵉ ofᵉ doubleᵉ arrows.ᵉ

## Definitions

### Double arrows induced by sequential diagrams

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  left-map-cofork-cocone-sequential-diagramᵉ :
    Σᵉ ℕᵉ (family-sequential-diagramᵉ Aᵉ) → Σᵉ ℕᵉ (family-sequential-diagramᵉ Aᵉ)
  left-map-cofork-cocone-sequential-diagramᵉ = idᵉ

  right-map-cofork-cocone-sequential-diagramᵉ :
    Σᵉ ℕᵉ (family-sequential-diagramᵉ Aᵉ) → Σᵉ ℕᵉ (family-sequential-diagramᵉ Aᵉ)
  right-map-cofork-cocone-sequential-diagramᵉ (nᵉ ,ᵉ aᵉ) =
    (succ-ℕᵉ nᵉ ,ᵉ map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)

  double-arrow-sequential-diagramᵉ : double-arrowᵉ l1ᵉ l1ᵉ
  double-arrow-sequential-diagramᵉ =
    make-double-arrowᵉ
      ( left-map-cofork-cocone-sequential-diagramᵉ)
      ( right-map-cofork-cocone-sequential-diagramᵉ)
```

### Morphisms of double arrows induced by morphisms of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  hom-double-arrow-hom-sequential-diagramᵉ :
    hom-sequential-diagramᵉ Aᵉ Bᵉ →
    hom-double-arrowᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( double-arrow-sequential-diagramᵉ Bᵉ)
  pr1ᵉ (hom-double-arrow-hom-sequential-diagramᵉ hᵉ) =
    totᵉ (map-hom-sequential-diagramᵉ Bᵉ hᵉ)
  pr1ᵉ (pr2ᵉ (hom-double-arrow-hom-sequential-diagramᵉ hᵉ)) =
    totᵉ (map-hom-sequential-diagramᵉ Bᵉ hᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (hom-double-arrow-hom-sequential-diagramᵉ hᵉ))) =
    refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-double-arrow-hom-sequential-diagramᵉ hᵉ))) =
    coherence-square-maps-Σᵉ
      ( family-sequential-diagramᵉ Bᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ hᵉ)
      ( map-sequential-diagramᵉ Aᵉ)
      ( map-sequential-diagramᵉ Bᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ hᵉ)
      ( λ nᵉ → inv-htpyᵉ (naturality-map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ))
```

### Equivalences of double arrows induced by equivalences of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  equiv-double-arrow-equiv-sequential-diagramᵉ :
    equiv-sequential-diagramᵉ Aᵉ Bᵉ →
    equiv-double-arrowᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( double-arrow-sequential-diagramᵉ Bᵉ)
  equiv-double-arrow-equiv-sequential-diagramᵉ eᵉ =
    equiv-hom-double-arrowᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( double-arrow-sequential-diagramᵉ Bᵉ)
      ( hom-double-arrow-hom-sequential-diagramᵉ Aᵉ Bᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( is-equiv-map-equiv-sequential-diagramᵉ Bᵉ eᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( is-equiv-map-equiv-sequential-diagramᵉ Bᵉ eᵉ))
```

### Coforks induced by cocones under sequential diagrams

Furtherᵉ downᵉ weᵉ showᵉ thatᵉ thereᵉ isᵉ anᵉ inverseᵉ map,ᵉ givingᵉ anᵉ equivalenceᵉ betweenᵉ
coconesᵉ underᵉ aᵉ sequentialᵉ diagramᵉ andᵉ coforksᵉ underᵉ theᵉ inducedᵉ doubleᵉ arrow.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  where

  cofork-cocone-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ Aᵉ Xᵉ →
    coforkᵉ (double-arrow-sequential-diagramᵉ Aᵉ) Xᵉ
  pr1ᵉ (cofork-cocone-sequential-diagramᵉ cᵉ) =
    ind-Σᵉ (map-cocone-sequential-diagramᵉ cᵉ)
  pr2ᵉ (cofork-cocone-sequential-diagramᵉ cᵉ) =
    ind-Σᵉ (coherence-cocone-sequential-diagramᵉ cᵉ)
```

### Dependent coforks induced by dependent cocones under sequential diagrams

Furtherᵉ downᵉ weᵉ showᵉ thatᵉ thereᵉ isᵉ anᵉ inverseᵉ map,ᵉ givingᵉ anᵉ equivalenceᵉ betweenᵉ
dependentᵉ coconesᵉ overᵉ aᵉ coconeᵉ underᵉ aᵉ sequentialᵉ diagramᵉ andᵉ dependentᵉ coforksᵉ
overᵉ theᵉ coforkᵉ inducedᵉ byᵉ theᵉ baseᵉ cocone.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  dependent-cofork-dependent-cocone-sequential-diagramᵉ :
    dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ →
    dependent-coforkᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( Pᵉ)
  pr1ᵉ (dependent-cofork-dependent-cocone-sequential-diagramᵉ dᵉ) =
    ind-Σᵉ (map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ)
  pr2ᵉ (dependent-cofork-dependent-cocone-sequential-diagramᵉ dᵉ) =
    ind-Σᵉ (coherence-triangle-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ)
```

### Morphisms of coforks under morphisms of double arrows induced by morphisms of cocones under morphisms of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (hᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  coh-map-hom-cofork-hom-cocone-hom-sequential-diagramᵉ :
    (uᵉ : Xᵉ → Yᵉ) →
    coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ uᵉ →
    coherence-map-cofork-hom-cofork-hom-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
      ( hom-double-arrow-hom-sequential-diagramᵉ Aᵉ Bᵉ hᵉ)
      ( uᵉ)
  coh-map-hom-cofork-hom-cocone-hom-sequential-diagramᵉ uᵉ Hᵉ =
    inv-htpyᵉ (ind-Σᵉ Hᵉ)

  coh-hom-cofork-hom-cocone-hom-sequential-diagramᵉ :
    (uᵉ : Xᵉ → Yᵉ) →
    (Hᵉ : coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ uᵉ) →
    coherence-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ uᵉ Hᵉ →
    coherence-hom-cofork-hom-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
      ( hom-double-arrow-hom-sequential-diagramᵉ Aᵉ Bᵉ hᵉ)
      ( uᵉ)
      ( coh-map-hom-cofork-hom-cocone-hom-sequential-diagramᵉ uᵉ Hᵉ)
  coh-hom-cofork-hom-cocone-hom-sequential-diagramᵉ uᵉ Hᵉ Kᵉ =
    ( right-whisker-concat-htpyᵉ
      ( right-unit-htpyᵉ)
      ( λ (nᵉ ,ᵉ aᵉ) →
        coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ
          ( map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ aᵉ))) ∙hᵉ
    ( ind-Σᵉ
      ( λ nᵉ →
        ( vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-mapsᵉ
          ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Aᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Bᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Bᵉ hᵉ (succ-ℕᵉ nᵉ))
          ( uᵉ)
          ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( Hᵉ nᵉ)
          ( Hᵉ (succ-ℕᵉ nᵉ))
          ( naturality-map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)
          ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
          ( Kᵉ nᵉ)) ∙hᵉ
        ( inv-htpy-assoc-htpyᵉ
          ( uᵉ ·lᵉ coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( inv-htpyᵉ (Hᵉ (succ-ℕᵉ nᵉ) ·rᵉ map-sequential-diagramᵉ Aᵉ nᵉ))
          ( ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ)) ·lᵉ
            ( inv-htpyᵉ (naturality-map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)))) ∙hᵉ
        ( left-whisker-concat-htpyᵉ _
          ( inv-htpyᵉ
            ( λ aᵉ →
              compute-ap-ind-Σ-eq-pair-eq-fiberᵉ
                ( map-cocone-sequential-diagramᵉ c'ᵉ)
                ( inv-htpyᵉ (naturality-map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ) aᵉ))))))

  hom-cofork-hom-cocone-hom-sequential-diagramᵉ :
    hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ →
    hom-cofork-hom-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
      ( hom-double-arrow-hom-sequential-diagramᵉ Aᵉ Bᵉ hᵉ)
  hom-cofork-hom-cocone-hom-sequential-diagramᵉ =
    totᵉ
      ( λ uᵉ →
        map-Σᵉ _
          ( coh-map-hom-cofork-hom-cocone-hom-sequential-diagramᵉ uᵉ)
          ( coh-hom-cofork-hom-cocone-hom-sequential-diagramᵉ uᵉ))
```

### Equivalences of coforks under equivalences of double arrows induced by equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  equiv-cofork-equiv-cocone-equiv-sequential-diagramᵉ :
    equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ →
    equiv-cofork-equiv-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
      ( equiv-double-arrow-equiv-sequential-diagramᵉ Aᵉ Bᵉ eᵉ)
  equiv-cofork-equiv-cocone-equiv-sequential-diagramᵉ e'ᵉ =
    equiv-hom-cofork-equiv-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
      ( equiv-double-arrow-equiv-sequential-diagramᵉ Aᵉ Bᵉ eᵉ)
      ( hom-cofork-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
        ( hom-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ))
      ( is-equiv-map-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
```

## Properties

### The type of cocones under a sequential diagram is equivalent to the type of coforks under the induced double arrow

Furthermore,ᵉ forᵉ everyᵉ coconeᵉ `c`ᵉ underᵉ `A`ᵉ with vertexᵉ `X`ᵉ thereᵉ isᵉ aᵉ
[commutingᵉ triangle](foundation.commuting-triangles-of-maps.mdᵉ)

```text
              cofork-mapᵉ
      (Xᵉ → Yᵉ) ---------->ᵉ coforkᵉ (double-arrowᵉ Aᵉ) Yᵉ
            \ᵉ             /ᵉ
  cocone-mapᵉ  \ᵉ         /ᵉ  cocone-coforkᵉ
                \ᵉ     /ᵉ
                 ∨ᵉ   ∨ᵉ
               coconeᵉ Aᵉ Yᵉ .ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  where

  cocone-sequential-diagram-coforkᵉ :
    coforkᵉ (double-arrow-sequential-diagramᵉ Aᵉ) Xᵉ →
    cocone-sequential-diagramᵉ Aᵉ Xᵉ
  pr1ᵉ (cocone-sequential-diagram-coforkᵉ eᵉ) =
    ev-pairᵉ (map-coforkᵉ (double-arrow-sequential-diagramᵉ Aᵉ) eᵉ)
  pr2ᵉ (cocone-sequential-diagram-coforkᵉ eᵉ) =
    ev-pairᵉ (coh-coforkᵉ (double-arrow-sequential-diagramᵉ Aᵉ) eᵉ)

  abstract
    is-section-cocone-sequential-diagram-coforkᵉ :
      is-sectionᵉ
        ( cofork-cocone-sequential-diagramᵉ)
        ( cocone-sequential-diagram-coforkᵉ)
    is-section-cocone-sequential-diagram-coforkᵉ eᵉ =
      eq-htpy-coforkᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ
          ( cocone-sequential-diagram-coforkᵉ eᵉ))
        ( eᵉ)
        ( refl-htpy-coforkᵉ _ _)

    is-retraction-cocone-sequential-diagram-coforkᵉ :
      is-retractionᵉ
        ( cofork-cocone-sequential-diagramᵉ)
        ( cocone-sequential-diagram-coforkᵉ)
    is-retraction-cocone-sequential-diagram-coforkᵉ cᵉ =
      eq-htpy-cocone-sequential-diagramᵉ Aᵉ
        ( cocone-sequential-diagram-coforkᵉ
          ( cofork-cocone-sequential-diagramᵉ cᵉ))
        ( cᵉ)
        ( refl-htpy-cocone-sequential-diagramᵉ _ _)

  is-equiv-cocone-sequential-diagram-coforkᵉ :
    is-equivᵉ cocone-sequential-diagram-coforkᵉ
  is-equiv-cocone-sequential-diagram-coforkᵉ =
    is-equiv-is-invertibleᵉ
      ( cofork-cocone-sequential-diagramᵉ)
      ( is-retraction-cocone-sequential-diagram-coforkᵉ)
      ( is-section-cocone-sequential-diagram-coforkᵉ)

  equiv-cocone-sequential-diagram-coforkᵉ :
    coforkᵉ (double-arrow-sequential-diagramᵉ Aᵉ) Xᵉ ≃ᵉ
    cocone-sequential-diagramᵉ Aᵉ Xᵉ
  pr1ᵉ equiv-cocone-sequential-diagram-coforkᵉ =
    cocone-sequential-diagram-coforkᵉ
  pr2ᵉ equiv-cocone-sequential-diagram-coforkᵉ =
    is-equiv-cocone-sequential-diagram-coforkᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  triangle-cocone-sequential-diagram-coforkᵉ :
    {l3ᵉ : Level} {Yᵉ : UUᵉ l3ᵉ} →
    coherence-triangle-mapsᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ {Yᵉ = Yᵉ})
      ( cocone-sequential-diagram-coforkᵉ)
      ( cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
  triangle-cocone-sequential-diagram-coforkᵉ hᵉ =
    eq-htpy-cocone-sequential-diagramᵉ Aᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ hᵉ)
      ( cocone-sequential-diagram-coforkᵉ
        ( cofork-mapᵉ
          ( double-arrow-sequential-diagramᵉ Aᵉ)
          ( cofork-cocone-sequential-diagramᵉ cᵉ)
          ( hᵉ)))
      ( refl-htpy-cocone-sequential-diagramᵉ _ _)
```

### The type of dependent cocones over a cocone is equivalent to the type of dependent coforks over the induced cofork

Furthermore,ᵉ forᵉ everyᵉ coconeᵉ `c`ᵉ underᵉ `A`ᵉ with vertexᵉ `X`ᵉ thereᵉ isᵉ aᵉ commutingᵉ
triangleᵉ

```text
                      dependent-cofork-mapᵉ
      ((xᵉ : Xᵉ) → Pᵉ xᵉ) ------------------->ᵉ dependent-coforkᵉ (cofork-coconeᵉ cᵉ) Yᵉ
                      \ᵉ                  /ᵉ
  dependent-cocone-mapᵉ  \ᵉ              /ᵉ  dependent-cocone-dependent-coforkᵉ
                          \ᵉ          /ᵉ
                           ∨ᵉ        ∨ᵉ
                      dependent-coconeᵉ cᵉ Pᵉ .ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  dependent-cocone-sequential-diagram-dependent-coforkᵉ :
    dependent-coforkᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( Pᵉ) →
    dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ
  pr1ᵉ (dependent-cocone-sequential-diagram-dependent-coforkᵉ eᵉ) =
    ev-pairᵉ
      ( map-dependent-coforkᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( Pᵉ)
        ( eᵉ))
  pr2ᵉ (dependent-cocone-sequential-diagram-dependent-coforkᵉ eᵉ) =
    ev-pairᵉ
      ( coherence-dependent-coforkᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( Pᵉ)
        ( eᵉ))

  abstract
    is-section-dependent-cocone-sequential-diagram-dependent-coforkᵉ :
      is-sectionᵉ
        ( dependent-cofork-dependent-cocone-sequential-diagramᵉ Pᵉ)
        ( dependent-cocone-sequential-diagram-dependent-coforkᵉ)
    is-section-dependent-cocone-sequential-diagram-dependent-coforkᵉ eᵉ =
      eq-htpy-dependent-coforkᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( Pᵉ)
        ( dependent-cofork-dependent-cocone-sequential-diagramᵉ Pᵉ
          ( dependent-cocone-sequential-diagram-dependent-coforkᵉ eᵉ))
        ( eᵉ)
        ( refl-htpy-dependent-coforkᵉ _ _ _)

    is-retraction-dependent-cocone-sequential-diagram-dependent-coforkᵉ :
      is-retractionᵉ
        ( dependent-cofork-dependent-cocone-sequential-diagramᵉ Pᵉ)
        ( dependent-cocone-sequential-diagram-dependent-coforkᵉ)
    is-retraction-dependent-cocone-sequential-diagram-dependent-coforkᵉ dᵉ =
      eq-htpy-dependent-cocone-sequential-diagramᵉ Pᵉ
        ( dependent-cocone-sequential-diagram-dependent-coforkᵉ
          ( dependent-cofork-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ))
        ( dᵉ)
        ( refl-htpy-dependent-cocone-sequential-diagramᵉ _ _)

  is-equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ :
    is-equivᵉ dependent-cocone-sequential-diagram-dependent-coforkᵉ
  is-equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ =
    is-equiv-is-invertibleᵉ
      ( dependent-cofork-dependent-cocone-sequential-diagramᵉ Pᵉ)
      ( is-retraction-dependent-cocone-sequential-diagram-dependent-coforkᵉ)
      ( is-section-dependent-cocone-sequential-diagram-dependent-coforkᵉ)

  equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ :
    dependent-coforkᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
      ( Pᵉ) ≃ᵉ
    dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ
  pr1ᵉ equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ =
    dependent-cocone-sequential-diagram-dependent-coforkᵉ
  pr2ᵉ equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ =
    is-equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  triangle-dependent-cocone-sequential-diagram-dependent-coforkᵉ :
    coherence-triangle-mapsᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ)
      ( dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( dependent-cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
  triangle-dependent-cocone-sequential-diagram-dependent-coforkᵉ hᵉ =
    eq-htpy-dependent-cocone-sequential-diagramᵉ Pᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ hᵉ)
      ( dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ
        ( dependent-cofork-mapᵉ
          ( double-arrow-sequential-diagramᵉ Aᵉ)
          ( cofork-cocone-sequential-diagramᵉ cᵉ)
          ( hᵉ)))
      ( refl-htpy-dependent-cocone-sequential-diagramᵉ _ _)
```