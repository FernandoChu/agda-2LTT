# Dependent universal property of suspensions

```agda
module synthetic-homotopy-theory.dependent-universal-property-suspensionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.constant-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-suspension-structuresᵉ
open import synthetic-homotopy-theory.suspension-structuresᵉ
```

</details>

## Idea

Thisᵉ isᵉ theᵉ dependentᵉ analogᵉ ofᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ suspensions](synthetic-homotopy-theory.universal-property-suspensions.md).ᵉ

## Definition

### The dependent universal property of suspensions

```agda
dependent-ev-suspensionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (sᵉ : suspension-structureᵉ Xᵉ Yᵉ) (Bᵉ : Yᵉ → UUᵉ l3ᵉ) →
  ((yᵉ : Yᵉ) → Bᵉ yᵉ) →
  dependent-suspension-structureᵉ Bᵉ sᵉ
pr1ᵉ (dependent-ev-suspensionᵉ sᵉ Bᵉ fᵉ) =
  fᵉ (north-suspension-structureᵉ sᵉ)
pr1ᵉ (pr2ᵉ (dependent-ev-suspensionᵉ sᵉ Bᵉ fᵉ)) =
  fᵉ (south-suspension-structureᵉ sᵉ)
pr2ᵉ (pr2ᵉ (dependent-ev-suspensionᵉ sᵉ Bᵉ fᵉ)) =
  apdᵉ fᵉ ∘ᵉ meridian-suspension-structureᵉ sᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (sᵉ : suspension-structureᵉ Xᵉ Yᵉ)
  where

  dependent-universal-property-suspensionᵉ : UUωᵉ
  dependent-universal-property-suspensionᵉ =
    {lᵉ : Level} (Bᵉ : Yᵉ → UUᵉ lᵉ) → is-equivᵉ (dependent-ev-suspensionᵉ sᵉ Bᵉ)
```

#### Coherence between `dependent-ev-suspension` and `dependent-cocone-map`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  where

  triangle-dependent-ev-suspensionᵉ :
    (sᵉ : suspension-structureᵉ Xᵉ Yᵉ) →
    (Bᵉ : Yᵉ → UUᵉ l3ᵉ) →
    ( ( map-equivᵉ
        ( equiv-dependent-suspension-structure-suspension-coconeᵉ sᵉ Bᵉ)) ∘ᵉ
      ( dependent-cocone-mapᵉ
        ( terminal-mapᵉ Xᵉ)
        ( terminal-mapᵉ Xᵉ)
        ( suspension-cocone-suspension-structureᵉ sᵉ)
        ( Bᵉ))) ~ᵉ
    ( dependent-ev-suspensionᵉ sᵉ Bᵉ)
  triangle-dependent-ev-suspensionᵉ sᵉ Bᵉ = refl-htpyᵉ
```