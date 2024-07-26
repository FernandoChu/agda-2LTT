# Morphisms of sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-homotopiesᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ betweenᵉ
[sequentialᵉ diagrams](synthetic-homotopy-theory.sequential-diagrams.md)**ᵉ
`fᵉ : (A,ᵉ aᵉ) → (B,ᵉ b)`ᵉ isᵉ aᵉ [sequence](foundation.dependent-sequences.mdᵉ) ofᵉ mapsᵉ
`fₙᵉ : Aₙᵉ → Bₙ`ᵉ satisfyingᵉ theᵉ naturalityᵉ conditionᵉ thatᵉ allᵉ squaresᵉ ofᵉ theᵉ formᵉ

```text
        aₙᵉ
    Aₙᵉ --->ᵉ Aₙ₊₁ᵉ
    |       |
 fₙᵉ |       | fₙ₊₁ᵉ
    ∨ᵉ       ∨ᵉ
    Bₙᵉ --->ᵉ Bₙ₊₁ᵉ
        bₙᵉ
```

[commute](foundation.commuting-squares-of-maps.md).ᵉ

## Definitions

### Morphisms of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  naturality-hom-sequential-diagramᵉ :
    ( hᵉ :
      ( nᵉ : ℕᵉ) →
      family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  naturality-hom-sequential-diagramᵉ hᵉ =
    ( nᵉ : ℕᵉ) →
    ( map-sequential-diagramᵉ Bᵉ nᵉ ∘ᵉ hᵉ nᵉ) ~ᵉ
    ( hᵉ (succ-ℕᵉ nᵉ) ∘ᵉ map-sequential-diagramᵉ Aᵉ nᵉ)

  hom-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-sequential-diagramᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ)
      ( naturality-hom-sequential-diagramᵉ)
```

### Components of morphisms of sequential diagrams

_Implementationᵉ noteᵉ:_ Ideallyᵉ weᵉ wouldᵉ haveᵉ bothᵉ theᵉ domainᵉ andᵉ codomainᵉ ofᵉ aᵉ
morphismᵉ ofᵉ sequentialᵉ diagramsᵉ inferredᵉ byᵉ Agda.ᵉ Unfortunatelyᵉ that'sᵉ notᵉ theᵉ
caseᵉ with theᵉ currentᵉ implementation,ᵉ andᵉ theᵉ codomainᵉ needsᵉ to beᵉ providedᵉ
explicitly.ᵉ Thisᵉ arisesᵉ alsoᵉ in
[equivalencesᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( hᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-hom-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ
  map-hom-sequential-diagramᵉ = pr1ᵉ hᵉ

  naturality-map-hom-sequential-diagramᵉ :
    naturality-hom-sequential-diagramᵉ Aᵉ Bᵉ map-hom-sequential-diagramᵉ
  naturality-map-hom-sequential-diagramᵉ = pr2ᵉ hᵉ
```

### The identity morphism of sequential diagrams

Allᵉ sequentialᵉ diagramsᵉ haveᵉ anᵉ **identityᵉ morphism**ᵉ constructedᵉ fromᵉ theᵉ
identityᵉ functionᵉ onᵉ theᵉ underlyingᵉ types.ᵉ

```agda
module _
  { l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  id-hom-sequential-diagramᵉ : hom-sequential-diagramᵉ Aᵉ Aᵉ
  pr1ᵉ id-hom-sequential-diagramᵉ nᵉ = idᵉ
  pr2ᵉ id-hom-sequential-diagramᵉ nᵉ = refl-htpyᵉ
```

### Composition of morphisms of sequential diagrams

**Compositionᵉ ofᵉ morphisms**ᵉ isᵉ inducedᵉ byᵉ compositionᵉ ofᵉ theᵉ underlyingᵉ mapsᵉ
andᵉ byᵉ pastingᵉ diagrams.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( Cᵉ : sequential-diagramᵉ l3ᵉ)
  ( gᵉ : hom-sequential-diagramᵉ Bᵉ Cᵉ) (fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-comp-hom-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Cᵉ nᵉ
  map-comp-hom-sequential-diagramᵉ nᵉ =
    map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ ∘ᵉ map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ

  naturality-comp-hom-sequential-diagramᵉ :
    naturality-hom-sequential-diagramᵉ Aᵉ Cᵉ map-comp-hom-sequential-diagramᵉ
  naturality-comp-hom-sequential-diagramᵉ nᵉ =
    pasting-vertical-coherence-square-mapsᵉ
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Cᵉ gᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Cᵉ nᵉ)
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( naturality-map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ)

  comp-hom-sequential-diagramᵉ :
    hom-sequential-diagramᵉ Aᵉ Cᵉ
  pr1ᵉ comp-hom-sequential-diagramᵉ = map-comp-hom-sequential-diagramᵉ
  pr2ᵉ comp-hom-sequential-diagramᵉ = naturality-comp-hom-sequential-diagramᵉ
```

### Homotopies between morphisms of sequential diagrams

Aᵉ **homotopy**ᵉ betweenᵉ morphismsᵉ `f,ᵉ gᵉ : (A,ᵉ aᵉ) → (B,ᵉ b)`ᵉ consistsᵉ ofᵉ aᵉ
[sequence](foundation.dependent-sequences.mdᵉ) ofᵉ
[homotopies](foundation.homotopies.mdᵉ) `Hₙᵉ : fₙᵉ ~ᵉ gₙ`ᵉ andᵉ aᵉ coherenceᵉ datumᵉ
fillingᵉ theᵉ cylindersᵉ

```text
              aₙᵉ
      Aₙᵉ ---------->ᵉ Aₙ₊₁ᵉ
      /ᵉ \ᵉ            /ᵉ \ᵉ
     /ᵉ Hₙ\ᵉ          /Hₙ₊₁\ᵉ
 fₙᵉ |  =>ᵉ | gₙᵉ fₙ₊₁ᵉ |  =>ᵉ | gₙ₊₁ᵉ
     \ᵉ   /ᵉ          \ᵉ   /ᵉ
      \ᵉ /ᵉ            \ᵉ /ᵉ
      Bₙᵉ ---------->ᵉ Bₙ₊₁.ᵉ
              bₙᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( fᵉ gᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  coherence-htpy-hom-sequential-diagramᵉ :
    ( Hᵉ :
      ( nᵉ : ℕᵉ) →
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ) ~ᵉ
      ( map-hom-sequential-diagramᵉ Bᵉ gᵉ nᵉ)) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-hom-sequential-diagramᵉ Hᵉ =
    ( nᵉ : ℕᵉ) →
    coherence-square-homotopiesᵉ
      ( map-sequential-diagramᵉ Bᵉ nᵉ ·lᵉ Hᵉ nᵉ)
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ gᵉ nᵉ)
      ( Hᵉ (succ-ℕᵉ nᵉ) ·rᵉ map-sequential-diagramᵉ Aᵉ nᵉ)

  htpy-hom-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) →
        ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ) ~ᵉ
        ( map-hom-sequential-diagramᵉ Bᵉ gᵉ nᵉ))
      ( coherence-htpy-hom-sequential-diagramᵉ)
```

### Components of homotopies between morphisms of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  { fᵉ gᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ}
  ( Hᵉ : htpy-hom-sequential-diagramᵉ Bᵉ fᵉ gᵉ)
  where

  htpy-htpy-hom-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ) ~ᵉ
    ( map-hom-sequential-diagramᵉ Bᵉ gᵉ nᵉ)
  htpy-htpy-hom-sequential-diagramᵉ = pr1ᵉ Hᵉ

  coherence-htpy-htpy-hom-sequential-diagramᵉ :
    coherence-htpy-hom-sequential-diagramᵉ Bᵉ fᵉ gᵉ htpy-htpy-hom-sequential-diagramᵉ
  coherence-htpy-htpy-hom-sequential-diagramᵉ = pr2ᵉ Hᵉ
```

## Properties

### Characterization of equality of morphisms of sequential diagrams

[Equality](foundation.identity-types.mdᵉ) ofᵉ morphismsᵉ ofᵉ sequentialᵉ diagramsᵉ isᵉ
capturedᵉ byᵉ aᵉ homotopyᵉ betweenᵉ them.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  refl-htpy-hom-sequential-diagramᵉ :
    ( fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) → htpy-hom-sequential-diagramᵉ Bᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-hom-sequential-diagramᵉ fᵉ) = ev-pairᵉ refl-htpyᵉ
  pr2ᵉ (refl-htpy-hom-sequential-diagramᵉ fᵉ) = ev-pairᵉ right-unit-htpyᵉ

  htpy-eq-sequential-diagramᵉ :
    ( fᵉ f'ᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) →
    ( fᵉ ＝ᵉ f'ᵉ) → htpy-hom-sequential-diagramᵉ Bᵉ fᵉ f'ᵉ
  htpy-eq-sequential-diagramᵉ fᵉ .fᵉ reflᵉ = refl-htpy-hom-sequential-diagramᵉ fᵉ

  abstract
    is-torsorial-htpy-sequential-diagramᵉ :
      ( fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) →
      is-torsorialᵉ (htpy-hom-sequential-diagramᵉ Bᵉ fᵉ)
    is-torsorial-htpy-sequential-diagramᵉ fᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-binary-htpyᵉ (map-hom-sequential-diagramᵉ Bᵉ fᵉ))
        ( map-hom-sequential-diagramᵉ Bᵉ fᵉ ,ᵉ ev-pairᵉ refl-htpyᵉ)
        ( is-torsorial-Eq-Πᵉ
          ( λ nᵉ →
            is-torsorial-htpyᵉ
              ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ ∙hᵉ refl-htpyᵉ)))

    is-equiv-htpy-eq-sequential-diagramᵉ :
      ( fᵉ f'ᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) →
      is-equivᵉ (htpy-eq-sequential-diagramᵉ fᵉ f'ᵉ)
    is-equiv-htpy-eq-sequential-diagramᵉ fᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-sequential-diagramᵉ fᵉ)
        ( htpy-eq-sequential-diagramᵉ fᵉ)

  extensionality-hom-sequential-diagramᵉ :
    ( fᵉ f'ᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) →
    ( fᵉ ＝ᵉ f'ᵉ) ≃ᵉ htpy-hom-sequential-diagramᵉ Bᵉ fᵉ f'ᵉ
  pr1ᵉ (extensionality-hom-sequential-diagramᵉ fᵉ f'ᵉ) =
    htpy-eq-sequential-diagramᵉ fᵉ f'ᵉ
  pr2ᵉ (extensionality-hom-sequential-diagramᵉ fᵉ f'ᵉ) =
    is-equiv-htpy-eq-sequential-diagramᵉ fᵉ f'ᵉ

  eq-htpy-sequential-diagramᵉ :
    ( fᵉ f'ᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) →
    htpy-hom-sequential-diagramᵉ Bᵉ fᵉ f'ᵉ → (fᵉ ＝ᵉ f'ᵉ)
  eq-htpy-sequential-diagramᵉ fᵉ f'ᵉ =
    map-inv-equivᵉ (extensionality-hom-sequential-diagramᵉ fᵉ f'ᵉ)
```