# Equivalences of sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

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
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.retracts-of-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Anᵉ **equivalenceᵉ ofᵉ sequentialᵉ diagrams**ᵉ `(A,ᵉ a)`ᵉ andᵉ `(B,ᵉ b)`ᵉ isᵉ aᵉ
[sequence](foundation.dependent-sequences.mdᵉ) ofᵉ
[equivalences](foundation.equivalences.mdᵉ) `eₙᵉ : Aₙᵉ ≃ᵉ Bₙ`ᵉ suchᵉ thatᵉ theirᵉ
underlyingᵉ mapsᵉ formᵉ aᵉ
[morphismᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md).ᵉ

Specifically,ᵉ theᵉ underlyingᵉ mapsᵉ needᵉ to satisfyᵉ theᵉ sameᵉ naturalityᵉ condition.ᵉ

## Definitions

### Equivalences of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  equiv-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) →
        family-sequential-diagramᵉ Aᵉ nᵉ ≃ᵉ family-sequential-diagramᵉ Bᵉ nᵉ)
      ( λ eᵉ → naturality-hom-sequential-diagramᵉ Aᵉ Bᵉ (map-equivᵉ ∘ᵉ eᵉ))
```

### Components of equivalences of sequential diagrams

_Implementationᵉ noteᵉ:_ Asᵉ mentionedᵉ in
[`morphisms-sequential-diagrams`](synthetic-homotopy-theory.morphisms-sequential-diagrams.md),ᵉ
Agdaᵉ can'tᵉ inferᵉ bothᵉ theᵉ domainᵉ andᵉ theᵉ codomainᵉ whenᵉ weᵉ useᵉ accessorsᵉ forᵉ theᵉ
equivalences,ᵉ andᵉ theᵉ codomainᵉ needsᵉ to beᵉ providedᵉ explicitly.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  equiv-equiv-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Aᵉ nᵉ ≃ᵉ family-sequential-diagramᵉ Bᵉ nᵉ
  equiv-equiv-sequential-diagramᵉ = pr1ᵉ eᵉ

  map-equiv-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ
  map-equiv-sequential-diagramᵉ nᵉ = map-equivᵉ (equiv-equiv-sequential-diagramᵉ nᵉ)

  naturality-equiv-sequential-diagramᵉ :
    naturality-hom-sequential-diagramᵉ Aᵉ Bᵉ map-equiv-sequential-diagramᵉ
  naturality-equiv-sequential-diagramᵉ = pr2ᵉ eᵉ

  hom-equiv-sequential-diagramᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ
  pr1ᵉ hom-equiv-sequential-diagramᵉ = map-equiv-sequential-diagramᵉ
  pr2ᵉ hom-equiv-sequential-diagramᵉ = naturality-equiv-sequential-diagramᵉ

  is-equiv-map-equiv-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    is-equivᵉ (map-equiv-sequential-diagramᵉ nᵉ)
  is-equiv-map-equiv-sequential-diagramᵉ nᵉ =
    is-equiv-map-equivᵉ (equiv-equiv-sequential-diagramᵉ nᵉ)
```

### The identity equivalence of sequential diagrams

```agda
module _
  { l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  id-equiv-sequential-diagramᵉ : equiv-sequential-diagramᵉ Aᵉ Aᵉ
  pr1ᵉ id-equiv-sequential-diagramᵉ nᵉ = id-equivᵉ
  pr2ᵉ id-equiv-sequential-diagramᵉ nᵉ = refl-htpyᵉ
```

### Composition of equivalences of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( Cᵉ : sequential-diagramᵉ l3ᵉ)
  where

  comp-equiv-sequential-diagramᵉ :
    equiv-sequential-diagramᵉ Bᵉ Cᵉ →
    equiv-sequential-diagramᵉ Aᵉ Bᵉ →
    equiv-sequential-diagramᵉ Aᵉ Cᵉ
  pr1ᵉ (comp-equiv-sequential-diagramᵉ eᵉ e'ᵉ) nᵉ =
    ( equiv-equiv-sequential-diagramᵉ Cᵉ eᵉ nᵉ) ∘eᵉ
    ( equiv-equiv-sequential-diagramᵉ Bᵉ e'ᵉ nᵉ)
  pr2ᵉ (comp-equiv-sequential-diagramᵉ eᵉ e'ᵉ) =
    naturality-map-hom-sequential-diagramᵉ Cᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ
        ( hom-equiv-sequential-diagramᵉ Cᵉ eᵉ)
        ( hom-equiv-sequential-diagramᵉ Bᵉ e'ᵉ))
```

### Inverses of equivalences of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  inv-equiv-sequential-diagramᵉ : equiv-sequential-diagramᵉ Bᵉ Aᵉ
  pr1ᵉ inv-equiv-sequential-diagramᵉ nᵉ =
    inv-equivᵉ (equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
  pr2ᵉ inv-equiv-sequential-diagramᵉ nᵉ =
    vertical-inv-equiv-coherence-square-mapsᵉ
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
      ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
        ( nᵉ))

  map-inv-equiv-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Bᵉ nᵉ → family-sequential-diagramᵉ Aᵉ nᵉ
  map-inv-equiv-sequential-diagramᵉ =
    map-equiv-sequential-diagramᵉ Aᵉ inv-equiv-sequential-diagramᵉ

  hom-inv-equiv-sequential-diagramᵉ : hom-sequential-diagramᵉ Bᵉ Aᵉ
  hom-inv-equiv-sequential-diagramᵉ =
    hom-equiv-sequential-diagramᵉ Aᵉ inv-equiv-sequential-diagramᵉ
```

## Properties

### Characterization of equality of sequential diagrams

[Equality](foundation.identity-types.mdᵉ) ofᵉ sequentialᵉ diagramsᵉ isᵉ capturedᵉ byᵉ
anᵉ equivalenceᵉ betweenᵉ them.ᵉ

```agda
equiv-eq-sequential-diagramᵉ :
  { l1ᵉ : Level} (Aᵉ Bᵉ : sequential-diagramᵉ l1ᵉ) →
  Aᵉ ＝ᵉ Bᵉ → equiv-sequential-diagramᵉ Aᵉ Bᵉ
equiv-eq-sequential-diagramᵉ Aᵉ .Aᵉ reflᵉ = id-equiv-sequential-diagramᵉ Aᵉ

abstract
  is-torsorial-equiv-sequential-diagramᵉ :
    { l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) →
    is-torsorialᵉ (equiv-sequential-diagramᵉ {l2ᵉ = l1ᵉ} Aᵉ)
  is-torsorial-equiv-sequential-diagramᵉ Aᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Eq-Πᵉ
        ( λ nᵉ → is-torsorial-equivᵉ (family-sequential-diagramᵉ Aᵉ nᵉ)))
      ( family-sequential-diagramᵉ Aᵉ ,ᵉ λ nᵉ → id-equivᵉ)
      ( is-torsorial-Eq-Πᵉ
        ( λ nᵉ → is-torsorial-htpy'ᵉ (map-sequential-diagramᵉ Aᵉ nᵉ)))

  is-equiv-equiv-eq-sequential-diagramᵉ :
    { l1ᵉ : Level} (Aᵉ Bᵉ : sequential-diagramᵉ l1ᵉ) →
    is-equivᵉ (equiv-eq-sequential-diagramᵉ Aᵉ Bᵉ)
  is-equiv-equiv-eq-sequential-diagramᵉ Aᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-sequential-diagramᵉ Aᵉ)
      ( equiv-eq-sequential-diagramᵉ Aᵉ)

extensionality-sequential-diagramᵉ :
  { l1ᵉ : Level} (Aᵉ Bᵉ : sequential-diagramᵉ l1ᵉ) →
  ( Aᵉ ＝ᵉ Bᵉ) ≃ᵉ equiv-sequential-diagramᵉ Aᵉ Bᵉ
pr1ᵉ (extensionality-sequential-diagramᵉ Aᵉ Bᵉ) = equiv-eq-sequential-diagramᵉ Aᵉ Bᵉ
pr2ᵉ (extensionality-sequential-diagramᵉ Aᵉ Bᵉ) =
  is-equiv-equiv-eq-sequential-diagramᵉ Aᵉ Bᵉ

eq-equiv-sequential-diagramᵉ :
  { l1ᵉ : Level} (Aᵉ Bᵉ : sequential-diagramᵉ l1ᵉ) →
  equiv-sequential-diagramᵉ Aᵉ Bᵉ → (Aᵉ ＝ᵉ Bᵉ)
eq-equiv-sequential-diagramᵉ Aᵉ Bᵉ =
  map-inv-equivᵉ (extensionality-sequential-diagramᵉ Aᵉ Bᵉ)
```

### Inverses of equivalences are inverses with respect to composition of morphisms of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  is-section-inv-equiv-sequential-diagramᵉ :
    htpy-hom-sequential-diagramᵉ Bᵉ
      ( comp-hom-sequential-diagramᵉ Bᵉ Aᵉ Bᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
        ( hom-inv-equiv-sequential-diagramᵉ Bᵉ eᵉ))
      ( id-hom-sequential-diagramᵉ Bᵉ)
  pr1ᵉ is-section-inv-equiv-sequential-diagramᵉ nᵉ =
    is-section-map-inv-equivᵉ (equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
  pr2ᵉ is-section-inv-equiv-sequential-diagramᵉ nᵉ =
    inv-htpyᵉ
      ( right-inverse-law-pasting-vertical-coherence-square-mapsᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ)
        ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
        ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ (succ-ℕᵉ nᵉ))
        ( map-sequential-diagramᵉ Bᵉ nᵉ)
        ( naturality-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ))

  is-retraction-inv-equiv-sequential-diagramᵉ :
    htpy-hom-sequential-diagramᵉ Aᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Aᵉ
        ( hom-inv-equiv-sequential-diagramᵉ Bᵉ eᵉ)
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ))
      ( id-hom-sequential-diagramᵉ Aᵉ)
  pr1ᵉ is-retraction-inv-equiv-sequential-diagramᵉ nᵉ =
    is-retraction-map-inv-equivᵉ (equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
  pr2ᵉ is-retraction-inv-equiv-sequential-diagramᵉ nᵉ =
    inv-htpyᵉ
      ( left-inverse-law-pasting-vertical-coherence-square-mapsᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ)
        ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
        ( equiv-equiv-sequential-diagramᵉ Bᵉ eᵉ (succ-ℕᵉ nᵉ))
        ( map-sequential-diagramᵉ Bᵉ nᵉ)
        ( naturality-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ))

  retraction-equiv-sequential-diagramᵉ :
    retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ
      ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
  pr1ᵉ retraction-equiv-sequential-diagramᵉ = hom-inv-equiv-sequential-diagramᵉ Bᵉ eᵉ
  pr2ᵉ retraction-equiv-sequential-diagramᵉ =
    is-retraction-inv-equiv-sequential-diagramᵉ
```

### Equivalences of sequential diagrams induce retracts of sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  retract-equiv-sequential-diagramᵉ : retract-sequential-diagramᵉ Bᵉ Aᵉ
  pr1ᵉ retract-equiv-sequential-diagramᵉ = hom-equiv-sequential-diagramᵉ Bᵉ eᵉ
  pr2ᵉ retract-equiv-sequential-diagramᵉ = retraction-equiv-sequential-diagramᵉ Bᵉ eᵉ
```