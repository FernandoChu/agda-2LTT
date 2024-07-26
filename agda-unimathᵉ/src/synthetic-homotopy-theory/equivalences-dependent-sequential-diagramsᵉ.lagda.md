# Equivalances of dependent sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-dependent-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[dependentᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.mdᵉ)

```text
     b₀ᵉ      b₁ᵉ      b₂ᵉ            c₀ᵉ      c₁ᵉ      c₂ᵉ
 B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ     C₀ᵉ --->ᵉ C₁ᵉ --->ᵉ C₂ᵉ --->ᵉ ⋯ᵉ
 |       |       |             |       |       |
 |       |       |             |       |       |
 ↡ᵉ       ↡ᵉ       ↡ᵉ             ↡ᵉ       ↡ᵉ       ↡ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ     A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ .ᵉ
     a₀ᵉ      a₁ᵉ      a₂ᵉ            a₀ᵉ      a₁ᵉ      a₂ᵉ
```

Anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ dependentᵉ sequentialᵉ diagrams"ᵉ Agda=equiv-dependent-sequential-diagramᵉ}}
betweenᵉ themᵉ isᵉ aᵉ familyᵉ ofᵉ
[fiberwiseᵉ equivalences](foundation-core.families-of-equivalences.mdᵉ)

```text
eₙᵉ : (aᵉ : Aₙᵉ) → Bₙᵉ aᵉ ≃ᵉ Cₙᵉ aᵉ
```

[equipped](foundation.structure.mdᵉ) with aᵉ familyᵉ ofᵉ fiberwiseᵉ
[homotopies](foundation-core.homotopies.mdᵉ) makingᵉ theᵉ squaresᵉ

```text
                 eₙᵉ aᵉ
     Bₙᵉ aᵉ ----------------->ᵉ Cₙᵉ aᵉ
       |          ≃ᵉ            |
  bₙᵉ aᵉ |                       | cₙᵉ aᵉ
       |                       |
       ∨ᵉ          ≃ᵉ            ∨ᵉ
  Bₙ₊₁ᵉ (aₙᵉ aᵉ) ---------->ᵉ Cₙ₊₁ᵉ (aₙᵉ aᵉ)
              eₙ₊₁ᵉ (aₙᵉ aᵉ)
```

[commute](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

### Equivalences of dependent sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  where

  coherence-equiv-dependent-sequential-diagramᵉ :
    ( (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ ≃ᵉ
      family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coherence-equiv-dependent-sequential-diagramᵉ hᵉ =
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    coherence-square-mapsᵉ
      ( map-equivᵉ (hᵉ nᵉ aᵉ))
      ( map-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ)
      ( map-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ)
      ( map-equivᵉ (hᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)))

  equiv-dependent-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-dependent-sequential-diagramᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
        family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ ≃ᵉ
        family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ)
      ( coherence-equiv-dependent-sequential-diagramᵉ)
```

### Components of an equivalence of dependent sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ}
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  (eᵉ : equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ)
  where

  equiv-equiv-dependent-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ ≃ᵉ
    family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ
  equiv-equiv-dependent-sequential-diagramᵉ = pr1ᵉ eᵉ

  map-equiv-dependent-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ →
    family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ
  map-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ =
    map-equivᵉ (equiv-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ)

  is-equiv-map-equiv-dependent-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ)
  is-equiv-map-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ =
    is-equiv-map-equivᵉ (equiv-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ)

  coh-equiv-dependent-sequential-diagramᵉ :
    coherence-equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ
      ( equiv-equiv-dependent-sequential-diagramᵉ)
  coh-equiv-dependent-sequential-diagramᵉ = pr2ᵉ eᵉ

  hom-equiv-dependent-sequential-diagramᵉ :
    hom-dependent-sequential-diagramᵉ Bᵉ Cᵉ
  pr1ᵉ hom-equiv-dependent-sequential-diagramᵉ =
    map-equiv-dependent-sequential-diagramᵉ
  pr2ᵉ hom-equiv-dependent-sequential-diagramᵉ =
    coh-equiv-dependent-sequential-diagramᵉ
```

### The predicate on morphisms of dependent sequential daigrams of being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ}
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  where

  is-equiv-hom-dependent-sequential-diagramᵉ :
    hom-dependent-sequential-diagramᵉ Bᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-equiv-hom-dependent-sequential-diagramᵉ hᵉ =
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-hom-dependent-sequential-diagramᵉ Cᵉ hᵉ nᵉ aᵉ)

  is-equiv-hom-equiv-dependent-sequential-diagramᵉ :
    (eᵉ : equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ) →
    is-equiv-hom-dependent-sequential-diagramᵉ
      ( hom-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ)
  is-equiv-hom-equiv-dependent-sequential-diagramᵉ eᵉ =
    is-equiv-map-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ
```

### The identity equivalence of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  id-equiv-dependent-sequential-diagramᵉ : equiv-dependent-sequential-diagramᵉ Bᵉ Bᵉ
  pr1ᵉ id-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ = id-equivᵉ
  pr2ᵉ id-equiv-dependent-sequential-diagramᵉ nᵉ aᵉ = refl-htpyᵉ
```

## Properties

### Morphisms of dependent sequential diagrams which are equivalences are equivalences of dependent sequential diagrams

Toᵉ constructᵉ anᵉ equivalenceᵉ ofᵉ dependentᵉ sequentialᵉ diagramsᵉ `eᵉ : Bᵉ ≃ᵉ C`,ᵉ itᵉ
sufficesᵉ to constructᵉ aᵉ morphismᵉ `hᵉ : Bᵉ → C`ᵉ andᵉ aᵉ proofᵉ thatᵉ theᵉ mapsᵉ `hₙ`ᵉ areᵉ
fiberwiseᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ}
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  (hᵉ : hom-dependent-sequential-diagramᵉ Bᵉ Cᵉ)
  where

  equiv-hom-dependent-sequential-diagramᵉ :
    is-equiv-hom-dependent-sequential-diagramᵉ Cᵉ hᵉ →
    equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ
  pr1ᵉ (equiv-hom-dependent-sequential-diagramᵉ is-equiv-mapᵉ) nᵉ aᵉ =
    (map-hom-dependent-sequential-diagramᵉ Cᵉ hᵉ nᵉ aᵉ ,ᵉ is-equiv-mapᵉ nᵉ aᵉ)
  pr2ᵉ (equiv-hom-dependent-sequential-diagramᵉ is-equiv-mapᵉ) =
    coh-hom-dependent-sequential-diagramᵉ Cᵉ hᵉ
```

### Characterization of identity types of dependent sequential diagrams

Theᵉ typeᵉ ofᵉ equivalencesᵉ ofᵉ dependentᵉ sequentialᵉ diagramsᵉ characterizesᵉ theᵉ
identityᵉ typeᵉ ofᵉ dependentᵉ sequentialᵉ diagrams.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  equiv-eq-dependent-sequential-diagramᵉ :
    (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ) →
    (Bᵉ ＝ᵉ Cᵉ) → equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ
  equiv-eq-dependent-sequential-diagramᵉ .Bᵉ reflᵉ =
    id-equiv-dependent-sequential-diagramᵉ Bᵉ

  abstract
    is-torsorial-equiv-dependent-sequential-diagramᵉ :
      is-torsorialᵉ (equiv-dependent-sequential-diagramᵉ {l3ᵉ = l2ᵉ} Bᵉ)
    is-torsorial-equiv-dependent-sequential-diagramᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ nᵉ →
            is-torsorial-Eq-Πᵉ
              ( λ aᵉ →
                is-torsorial-equivᵉ
                  ( family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ))))
        ( family-dependent-sequential-diagramᵉ Bᵉ ,ᵉ λ nᵉ aᵉ → id-equivᵉ)
        ( is-torsorial-Eq-Πᵉ
          ( λ nᵉ →
            is-torsorial-Eq-Πᵉ
              ( λ aᵉ →
                is-torsorial-htpyᵉ (map-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ))))

  is-equiv-equiv-eq-dependent-sequential-diagramᵉ :
    (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ) →
    is-equivᵉ (equiv-eq-dependent-sequential-diagramᵉ Cᵉ)
  is-equiv-equiv-eq-dependent-sequential-diagramᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-dependent-sequential-diagramᵉ)
      ( equiv-eq-dependent-sequential-diagramᵉ)

  extensionality-dependent-sequential-diagramᵉ :
    (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ) →
    (Bᵉ ＝ᵉ Cᵉ) ≃ᵉ equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ
  pr1ᵉ (extensionality-dependent-sequential-diagramᵉ Cᵉ) =
    equiv-eq-dependent-sequential-diagramᵉ Cᵉ
  pr2ᵉ (extensionality-dependent-sequential-diagramᵉ Cᵉ) =
    is-equiv-equiv-eq-dependent-sequential-diagramᵉ Cᵉ

  eq-equiv-dependent-sequential-diagramᵉ :
    (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ) →
    equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ → (Bᵉ ＝ᵉ Cᵉ)
  eq-equiv-dependent-sequential-diagramᵉ Cᵉ =
    map-inv-equivᵉ (extensionality-dependent-sequential-diagramᵉ Cᵉ)
```