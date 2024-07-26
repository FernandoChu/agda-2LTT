# Functoriality of set quotients

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.functoriality-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.surjective-mapsᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Setᵉ quotientsᵉ actᵉ functoriallyᵉ onᵉ typesᵉ equippedᵉ with equivalenceᵉ relations.ᵉ

## Definition

### Maps preserving equivalence relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  preserves-sim-prop-equivalence-relationᵉ : (fᵉ : Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-sim-prop-equivalence-relationᵉ fᵉ =
    implicit-Π-Propᵉ Aᵉ
      ( λ xᵉ →
        implicit-Π-Propᵉ Aᵉ
          ( λ yᵉ →
            function-Propᵉ
              ( sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ)
              ( prop-equivalence-relationᵉ Sᵉ (fᵉ xᵉ) (fᵉ yᵉ))))

  preserves-sim-equivalence-relationᵉ : (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-sim-equivalence-relationᵉ fᵉ =
    type-Propᵉ (preserves-sim-prop-equivalence-relationᵉ fᵉ)

  is-prop-preserves-sim-equivalence-relationᵉ :
    (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (preserves-sim-equivalence-relationᵉ fᵉ)
  is-prop-preserves-sim-equivalence-relationᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-sim-prop-equivalence-relationᵉ fᵉ)

  hom-equivalence-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-equivalence-relationᵉ =
    type-subtypeᵉ preserves-sim-prop-equivalence-relationᵉ

  map-hom-equivalence-relationᵉ : hom-equivalence-relationᵉ → Aᵉ → Bᵉ
  map-hom-equivalence-relationᵉ = pr1ᵉ

  preserves-sim-hom-equivalence-relationᵉ :
    (fᵉ : hom-equivalence-relationᵉ) {xᵉ yᵉ : Aᵉ} →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
    sim-equivalence-relationᵉ
      ( Sᵉ)
      ( map-hom-equivalence-relationᵉ fᵉ xᵉ)
      ( map-hom-equivalence-relationᵉ fᵉ yᵉ)
  preserves-sim-hom-equivalence-relationᵉ = pr2ᵉ

id-hom-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
  hom-equivalence-relationᵉ Rᵉ Rᵉ
pr1ᵉ (id-hom-equivalence-relationᵉ Rᵉ) = idᵉ
pr2ᵉ (id-hom-equivalence-relationᵉ Rᵉ) = idᵉ
```

### Equivalences preserving equivalence relations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  equiv-equivalence-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-equivalence-relationᵉ =
    Σᵉ ( Aᵉ ≃ᵉ Bᵉ)
      ( λ eᵉ →
        {xᵉ yᵉ : Aᵉ} →
        sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ↔ᵉ
        sim-equivalence-relationᵉ Sᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))

  equiv-equiv-equivalence-relationᵉ : equiv-equivalence-relationᵉ → Aᵉ ≃ᵉ Bᵉ
  equiv-equiv-equivalence-relationᵉ = pr1ᵉ

  map-equiv-equivalence-relationᵉ : equiv-equivalence-relationᵉ → Aᵉ → Bᵉ
  map-equiv-equivalence-relationᵉ eᵉ =
    map-equivᵉ (equiv-equiv-equivalence-relationᵉ eᵉ)

  map-inv-equiv-equivalence-relationᵉ : equiv-equivalence-relationᵉ → Bᵉ → Aᵉ
  map-inv-equiv-equivalence-relationᵉ eᵉ =
    map-inv-equivᵉ (equiv-equiv-equivalence-relationᵉ eᵉ)

  is-equiv-map-equiv-equivalence-relationᵉ :
    (eᵉ : equiv-equivalence-relationᵉ) →
    is-equivᵉ (map-equiv-equivalence-relationᵉ eᵉ)
  is-equiv-map-equiv-equivalence-relationᵉ eᵉ =
    is-equiv-map-equivᵉ (equiv-equiv-equivalence-relationᵉ eᵉ)

  equiv-sim-equiv-equivalence-relationᵉ :
    (eᵉ : equiv-equivalence-relationᵉ) {xᵉ yᵉ : Aᵉ} →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ↔ᵉ
    sim-equivalence-relationᵉ
      ( Sᵉ)
      ( map-equiv-equivalence-relationᵉ eᵉ xᵉ)
      ( map-equiv-equivalence-relationᵉ eᵉ yᵉ)
  equiv-sim-equiv-equivalence-relationᵉ = pr2ᵉ

  preserves-sim-equiv-equivalence-relationᵉ :
    (eᵉ : equiv-equivalence-relationᵉ) {xᵉ yᵉ : Aᵉ} →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
    sim-equivalence-relationᵉ
      ( Sᵉ)
      ( map-equiv-equivalence-relationᵉ eᵉ xᵉ)
      ( map-equiv-equivalence-relationᵉ eᵉ yᵉ)
  preserves-sim-equiv-equivalence-relationᵉ eᵉ =
    pr1ᵉ (equiv-sim-equiv-equivalence-relationᵉ eᵉ)

  hom-equiv-equivalence-relationᵉ :
    equiv-equivalence-relationᵉ → hom-equivalence-relationᵉ Rᵉ Sᵉ
  pr1ᵉ (hom-equiv-equivalence-relationᵉ eᵉ) = map-equiv-equivalence-relationᵉ eᵉ
  pr2ᵉ (hom-equiv-equivalence-relationᵉ eᵉ) =
    preserves-sim-equiv-equivalence-relationᵉ eᵉ

id-equiv-equivalence-relationᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) →
  equiv-equivalence-relationᵉ Rᵉ Rᵉ
pr1ᵉ (id-equiv-equivalence-relationᵉ Rᵉ) = id-equivᵉ
pr1ᵉ (pr2ᵉ (id-equiv-equivalence-relationᵉ Rᵉ)) = idᵉ
pr2ᵉ (pr2ᵉ (id-equiv-equivalence-relationᵉ Rᵉ)) = idᵉ
```

### Maps between types satisfying the universal property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  {Bᵉ : UUᵉ l4ᵉ} (Sᵉ : equivalence-relationᵉ l5ᵉ Bᵉ)
  (QSᵉ : Setᵉ l6ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Sᵉ (type-Setᵉ QSᵉ))
  where

  unique-map-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ QRᵉ fᵉ → is-set-quotientᵉ Sᵉ QSᵉ gᵉ →
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    is-contrᵉ
      ( Σᵉ ( type-Setᵉ QRᵉ → type-Setᵉ QSᵉ)
          ( coherence-square-mapsᵉ
            ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
            ( map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ)))
  unique-map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    universal-property-set-quotient-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ QSᵉ
      ( pairᵉ
        ( map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ ∘ᵉ
          map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
        ( λ rᵉ →
          reflects-map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ
          ( preserves-sim-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ rᵉ)))

  map-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ QRᵉ fᵉ → is-set-quotientᵉ Sᵉ QSᵉ gᵉ →
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    type-Setᵉ QRᵉ → type-Setᵉ QSᵉ
  map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    pr1ᵉ (centerᵉ (unique-map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ))

  coherence-square-map-is-set-quotientᵉ :
    (Ufᵉ : is-set-quotientᵉ Rᵉ QRᵉ fᵉ) →
    (Ugᵉ : is-set-quotientᵉ Sᵉ QSᵉ gᵉ) →
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ)
      ( map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ)
  coherence-square-map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    pr2ᵉ (centerᵉ (unique-map-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ))
```

### Functoriality of the set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  unique-map-set-quotientᵉ :
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    is-contrᵉ
      ( Σᵉ ( set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ)
          ( coherence-square-mapsᵉ
            ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
            ( quotient-mapᵉ Rᵉ)
            ( quotient-mapᵉ Sᵉ)))
  unique-map-set-quotientᵉ =
    unique-map-is-set-quotientᵉ
      ( Rᵉ)
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( is-set-quotient-set-quotientᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)

  map-set-quotientᵉ :
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) → set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ
  map-set-quotientᵉ =
    map-is-set-quotientᵉ
      ( Rᵉ)
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( is-set-quotient-set-quotientᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)

  coherence-square-map-set-quotientᵉ :
    (hᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
      ( quotient-mapᵉ Rᵉ)
      ( quotient-mapᵉ Sᵉ)
      ( map-set-quotientᵉ hᵉ)
  coherence-square-map-set-quotientᵉ =
    coherence-square-map-is-set-quotientᵉ
      ( Rᵉ)
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( is-set-quotient-set-quotientᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)
```

## Properties

### Composition of reflecting maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  {Cᵉ : UUᵉ l5ᵉ}
  where

  comp-reflecting-map-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ Sᵉ Cᵉ → hom-equivalence-relationᵉ Rᵉ Sᵉ →
    reflecting-map-equivalence-relationᵉ Rᵉ Cᵉ
  pr1ᵉ (comp-reflecting-map-equivalence-relationᵉ gᵉ fᵉ) =
    map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ ∘ᵉ
    map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ
  pr2ᵉ (comp-reflecting-map-equivalence-relationᵉ gᵉ fᵉ) rᵉ =
    reflects-map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ
      ( preserves-sim-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ rᵉ)
```

### Characterizing equality of `hom-equivalence-relation`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  htpy-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-hom-equivalence-relationᵉ fᵉ gᵉ =
    map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ ~ᵉ map-hom-equivalence-relationᵉ Rᵉ Sᵉ gᵉ

  refl-htpy-hom-equivalence-relationᵉ :
    (fᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) → htpy-hom-equivalence-relationᵉ fᵉ fᵉ
  refl-htpy-hom-equivalence-relationᵉ fᵉ = refl-htpyᵉ

  htpy-eq-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-equivalence-relationᵉ fᵉ gᵉ
  htpy-eq-hom-equivalence-relationᵉ fᵉ .fᵉ reflᵉ =
    refl-htpy-hom-equivalence-relationᵉ fᵉ

  is-torsorial-htpy-hom-equivalence-relationᵉ :
    (fᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    is-torsorialᵉ (htpy-hom-equivalence-relationᵉ fᵉ)
  is-torsorial-htpy-hom-equivalence-relationᵉ fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ))
      ( is-prop-preserves-sim-equivalence-relationᵉ Rᵉ Sᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( refl-htpy-hom-equivalence-relationᵉ fᵉ)
      ( preserves-sim-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)

  is-equiv-htpy-eq-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    is-equivᵉ (htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-equivalence-relationᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-equivalence-relationᵉ fᵉ)
      ( htpy-eq-hom-equivalence-relationᵉ fᵉ)

  extensionality-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-equivalence-relationᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-equivalence-relationᵉ fᵉ gᵉ) =
    htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-equivalence-relationᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-equivalence-relationᵉ fᵉ gᵉ

  eq-htpy-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    htpy-hom-equivalence-relationᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-hom-equivalence-relationᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-equivalence-relationᵉ fᵉ gᵉ)
```

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  {Bᵉ : UUᵉ l4ᵉ} (Sᵉ : equivalence-relationᵉ l5ᵉ Bᵉ)
  (QSᵉ : Setᵉ l6ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Sᵉ (type-Setᵉ QSᵉ))
  where

  unique-equiv-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ QRᵉ fᵉ → is-set-quotientᵉ Sᵉ QSᵉ gᵉ →
    (hᵉ : equiv-equivalence-relationᵉ Rᵉ Sᵉ) →
    is-contrᵉ
      ( Σᵉ ( type-Setᵉ QRᵉ ≃ᵉ type-Setᵉ QSᵉ)
          ( λ h'ᵉ →
            coherence-square-mapsᵉ
              ( map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
              ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
              ( map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ)
              ( map-equivᵉ h'ᵉ)))
  unique-equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    uniqueness-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ QSᵉ
      ( comp-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ gᵉ
        ( hom-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ))
      ( is-set-quotient-is-surjective-and-effectiveᵉ Rᵉ QSᵉ
        ( comp-reflecting-map-equivalence-relationᵉ Rᵉ Sᵉ gᵉ
          ( hom-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ))
        ( ( is-surjective-compᵉ
            ( is-surjective-is-set-quotientᵉ Sᵉ QSᵉ gᵉ Ugᵉ)
            ( is-surjective-is-equivᵉ
              ( is-equiv-map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ))) ,ᵉ
          ( λ xᵉ yᵉ →
            ( inv-equivᵉ
              ( equiv-iff'ᵉ
                ( prop-equivalence-relationᵉ Rᵉ xᵉ yᵉ)
                ( prop-equivalence-relationᵉ Sᵉ
                  ( map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ xᵉ)
                  ( map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ yᵉ))
                ( equiv-sim-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ))) ∘eᵉ
            ( is-effective-is-set-quotientᵉ Sᵉ QSᵉ gᵉ Ugᵉ
              ( map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ xᵉ)
              ( map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ yᵉ)))))

  equiv-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ QRᵉ fᵉ →
    is-set-quotientᵉ Sᵉ QSᵉ gᵉ →
    (hᵉ : equiv-equivalence-relationᵉ Rᵉ Sᵉ) → type-Setᵉ QRᵉ ≃ᵉ type-Setᵉ QSᵉ
  equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    pr1ᵉ (centerᵉ (unique-equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ))

  coherence-square-equiv-is-set-quotientᵉ :
    (Ufᵉ : is-set-quotientᵉ Rᵉ QRᵉ fᵉ) →
    (Ugᵉ : is-set-quotientᵉ Sᵉ QSᵉ gᵉ) →
    (hᵉ : equiv-equivalence-relationᵉ Rᵉ Sᵉ) →
    coherence-square-mapsᵉ (map-equiv-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Sᵉ gᵉ)
      ( map-equivᵉ (equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ))
  coherence-square-equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ =
    pr2ᵉ (centerᵉ (unique-equiv-is-set-quotientᵉ Ufᵉ Ugᵉ hᵉ))
```

### Functoriality of set quotients preserves identity maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  where

  id-map-is-set-quotientᵉ :
    (Ufᵉ : is-set-quotientᵉ Rᵉ QRᵉ fᵉ) →
    map-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ (id-hom-equivalence-relationᵉ Rᵉ) ~ᵉ idᵉ
  id-map-is-set-quotientᵉ Ufᵉ xᵉ =
    apᵉ
      ( λ cᵉ → pr1ᵉ cᵉ xᵉ)
      { xᵉ =
        centerᵉ
          ( unique-map-is-set-quotientᵉ
              Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ (id-hom-equivalence-relationᵉ Rᵉ))}
      { yᵉ = pairᵉ idᵉ refl-htpyᵉ}
      ( eq-is-contrᵉ
        ( unique-map-is-set-quotientᵉ
            Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ (id-hom-equivalence-relationᵉ Rᵉ)))

  id-equiv-is-set-quotientᵉ :
    (Ufᵉ : is-set-quotientᵉ Rᵉ QRᵉ fᵉ) →
    htpy-equivᵉ
      ( equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ
        ( id-equiv-equivalence-relationᵉ Rᵉ))
      ( id-equivᵉ)
  id-equiv-is-set-quotientᵉ Ufᵉ xᵉ =
    apᵉ
      ( λ cᵉ → map-equivᵉ (pr1ᵉ cᵉ) xᵉ)
      { xᵉ =
        centerᵉ
          ( unique-equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ
            ( id-equiv-equivalence-relationᵉ Rᵉ))}
      { yᵉ = pairᵉ id-equivᵉ refl-htpyᵉ}
      ( eq-is-contrᵉ
        ( unique-equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ
          ( id-equiv-equivalence-relationᵉ Rᵉ)))
```