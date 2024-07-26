# Dependent cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.dependent-cocones-under-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-homotopiesᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.dependent-homotopiesᵉ
open import foundation.dependent-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-coforksᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`,ᵉ aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ) `c`ᵉ
with vertexᵉ `X`ᵉ underᵉ it,ᵉ andᵉ aᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`,ᵉ weᵉ mayᵉ constructᵉ
_dependentᵉ_ coconesᵉ onᵉ `P`ᵉ overᵉ `c`.ᵉ

Aᵉ **dependentᵉ coconeᵉ underᵉ aᵉ
[sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.md)**ᵉ onᵉ `P`ᵉ
overᵉ `cᵉ ≐ᵉ (X,ᵉ i,ᵉ H)`ᵉ consistsᵉ ofᵉ aᵉ [sequence](foundation.dependent-sequences.mdᵉ)
ofᵉ dependentᵉ mapsᵉ `i'ₙᵉ : (xᵉ : Aₙᵉ) → Pᵉ (iₙᵉ x)`ᵉ andᵉ aᵉ sequenceᵉ ofᵉ
[dependentᵉ homotopies](foundation.dependent-homotopies.mdᵉ)
`H'ₙᵉ : i'ₙᵉ ~ᵉ i'ₙ₊₁ᵉ ∘ᵉ aₙ`ᵉ overᵉ `H`.ᵉ

## Definitions

### Dependent cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  dependent-cocone-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  dependent-cocone-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
        Pᵉ (map-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ))
      ( λ iᵉ →
        ( nᵉ : ℕᵉ) →
        dependent-homotopyᵉ (λ _ → Pᵉ)
          ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( iᵉ nᵉ)
          ( iᵉ (succ-ℕᵉ nᵉ) ∘ᵉ map-sequential-diagramᵉ Aᵉ nᵉ))
```

### Components of dependent cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  ( dᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ)
  where

  map-dependent-cocone-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    Pᵉ (map-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
  map-dependent-cocone-sequential-diagramᵉ = pr1ᵉ dᵉ

  coherence-triangle-dependent-cocone-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) → (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    dependent-identificationᵉ Pᵉ
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
      ( map-dependent-cocone-sequential-diagramᵉ nᵉ aᵉ)
      ( map-dependent-cocone-sequential-diagramᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))
  coherence-triangle-dependent-cocone-sequential-diagramᵉ = pr2ᵉ dᵉ
```

### Homotopies of dependent cocones under sequential diagrams

Aᵉ **homotopy**ᵉ ofᵉ dependentᵉ coconesᵉ `(P,ᵉ i',ᵉ H')`ᵉ andᵉ `(P,ᵉ j',ᵉ L')`ᵉ consistsᵉ ofᵉ
aᵉ sequenceᵉ ofᵉ [homotopies](foundation.homotopies.mdᵉ) `Kₙᵉ : i'ₙᵉ ~ᵉ j'ₙ`ᵉ andᵉ aᵉ
coherenceᵉ datum.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  coherence-htpy-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    ( Kᵉ :
      ( nᵉ : ℕᵉ) →
      ( map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ nᵉ) ~ᵉ
      ( map-dependent-cocone-sequential-diagramᵉ Pᵉ d'ᵉ nᵉ)) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-htpy-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ Kᵉ =
    ( nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    ( ( coherence-triangle-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ nᵉ aᵉ) ∙ᵉ
      ( Kᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))) ＝ᵉ
    ( ( apᵉ
        ( trᵉ Pᵉ (coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ))
        ( Kᵉ nᵉ aᵉ)) ∙ᵉ
      ( coherence-triangle-dependent-cocone-sequential-diagramᵉ Pᵉ d'ᵉ nᵉ aᵉ))

  htpy-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) →
        ( map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ nᵉ) ~ᵉ
        ( map-dependent-cocone-sequential-diagramᵉ Pᵉ d'ᵉ nᵉ))
      ( coherence-htpy-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ)
```

### Components of homotopies of dependent cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  { dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ}
  ( Hᵉ : htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ d'ᵉ)
  where

  htpy-htpy-dependent-cocone-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    ( map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ nᵉ) ~ᵉ
    ( map-dependent-cocone-sequential-diagramᵉ Pᵉ d'ᵉ nᵉ)
  htpy-htpy-dependent-cocone-sequential-diagramᵉ = pr1ᵉ Hᵉ

  coherence-htpy-htpy-dependent-cocone-sequential-diagramᵉ :
    coherence-htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ d'ᵉ
      ( htpy-htpy-dependent-cocone-sequential-diagramᵉ)
  coherence-htpy-htpy-dependent-cocone-sequential-diagramᵉ = pr2ᵉ Hᵉ
```

### Obtaining dependent cocones under sequential diagrams by postcomposing cocones under sequential diagrams with dependent maps

Givenᵉ aᵉ coconeᵉ `c`ᵉ with vertexᵉ `X`,ᵉ andᵉ aᵉ dependentᵉ mapᵉ `hᵉ : (xᵉ : Xᵉ) → Pᵉ x`,ᵉ weᵉ
mayᵉ extendᵉ `c`ᵉ to aᵉ dependentᵉ coconeᵉ onᵉ `P`ᵉ overᵉ `c`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  dependent-cocone-map-sequential-diagramᵉ :
    { lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
    ( (xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ
  pr1ᵉ (dependent-cocone-map-sequential-diagramᵉ Pᵉ hᵉ) nᵉ =
    hᵉ ∘ᵉ map-cocone-sequential-diagramᵉ cᵉ nᵉ
  pr2ᵉ (dependent-cocone-map-sequential-diagramᵉ Pᵉ hᵉ) nᵉ =
    apdᵉ hᵉ ∘ᵉ coherence-cocone-sequential-diagramᵉ cᵉ nᵉ
```

## Properties

### Characterization of identity types of dependent cocones under sequential diagrams

[Equality](foundation.identity-types.mdᵉ) ofᵉ dependentᵉ coconesᵉ isᵉ capturedᵉ byᵉ aᵉ
homotopyᵉ betweenᵉ them.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  refl-htpy-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ dᵉ
  pr1ᵉ (refl-htpy-dependent-cocone-sequential-diagramᵉ dᵉ) nᵉ = refl-htpyᵉ
  pr2ᵉ (refl-htpy-dependent-cocone-sequential-diagramᵉ dᵉ) nᵉ = right-unit-htpyᵉ

  htpy-eq-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    ( dᵉ ＝ᵉ d'ᵉ) → htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ d'ᵉ
  htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ .dᵉ reflᵉ =
    refl-htpy-dependent-cocone-sequential-diagramᵉ dᵉ

  abstract
    is-torsorial-htpy-dependent-cocone-sequential-diagramᵉ :
      ( dᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
      is-torsorialᵉ (htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ)
    is-torsorial-htpy-dependent-cocone-sequential-diagramᵉ dᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-binary-htpyᵉ
          ( map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ))
        ( map-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ ,ᵉ
          ev-pairᵉ refl-htpyᵉ)
        ( is-torsorial-binary-htpyᵉ
          ( λ nᵉ →
            ( coherence-triangle-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ nᵉ) ∙hᵉ
            ( refl-htpyᵉ)))

    is-equiv-htpy-eq-dependent-cocone-sequential-diagramᵉ :
      ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
      is-equivᵉ (htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ)
    is-equiv-htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-dependent-cocone-sequential-diagramᵉ dᵉ)
        ( htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ)

  extensionality-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    ( dᵉ ＝ᵉ d'ᵉ) ≃ᵉ htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ d'ᵉ
  pr1ᵉ (extensionality-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ) =
    htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ
  pr2ᵉ (extensionality-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ) =
    is-equiv-htpy-eq-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ

  eq-htpy-dependent-cocone-sequential-diagramᵉ :
    ( dᵉ d'ᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ) →
    htpy-dependent-cocone-sequential-diagramᵉ Pᵉ dᵉ d'ᵉ → (dᵉ ＝ᵉ d'ᵉ)
  eq-htpy-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ =
    map-inv-equivᵉ (extensionality-dependent-cocone-sequential-diagramᵉ dᵉ d'ᵉ)
```

### Dependent cocones under sequential diagrams on fiberwise constant type families are equivalent to regular cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} (Yᵉ : UUᵉ l3ᵉ)
  where

  compute-dependent-cocone-sequential-diagram-constant-familyᵉ :
    ( dependent-cocone-sequential-diagramᵉ cᵉ (λ _ → Yᵉ)) ≃ᵉ
    ( cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  compute-dependent-cocone-sequential-diagram-constant-familyᵉ =
    equiv-totᵉ
      ( λ iᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ nᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ aᵉ →
                equiv-concatᵉ
                  ( invᵉ
                    ( tr-constant-type-familyᵉ
                      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
                      ( iᵉ nᵉ aᵉ)))
                  ( iᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)))))

  map-compute-dependent-cocone-sequential-diagram-constant-familyᵉ :
    dependent-cocone-sequential-diagramᵉ cᵉ (λ _ → Yᵉ) →
    cocone-sequential-diagramᵉ Aᵉ Yᵉ
  map-compute-dependent-cocone-sequential-diagram-constant-familyᵉ =
    map-equivᵉ compute-dependent-cocone-sequential-diagram-constant-familyᵉ

  triangle-compute-dependent-cocone-sequential-diagram-constant-familyᵉ :
    coherence-triangle-mapsᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( map-compute-dependent-cocone-sequential-diagram-constant-familyᵉ)
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ (λ _ → Yᵉ))
  triangle-compute-dependent-cocone-sequential-diagram-constant-familyᵉ hᵉ =
    eq-htpy-cocone-sequential-diagramᵉ Aᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ hᵉ)
      ( map-compute-dependent-cocone-sequential-diagram-constant-familyᵉ
        ( dependent-cocone-map-sequential-diagramᵉ cᵉ (λ _ → Yᵉ) hᵉ))
      ( ( ev-pairᵉ refl-htpyᵉ) ,ᵉ
        ( λ nᵉ aᵉ →
          right-unitᵉ ∙ᵉ
          left-transpose-eq-concatᵉ _ _ _
            ( invᵉ
              ( apd-constant-type-familyᵉ hᵉ
                ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)))))
```