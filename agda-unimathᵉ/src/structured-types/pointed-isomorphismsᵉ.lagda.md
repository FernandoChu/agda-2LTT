# Pointed isomorphisms

```agda
module structured-types.pointed-isomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-retractionsᵉ
open import structured-types.pointed-sectionsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "pointedᵉ isomorphism"ᵉ Agda=pointed-isoᵉ}} isᵉ anᵉ isomorphismᵉ in theᵉ
wildᵉ categoryᵉ ofᵉ pointedᵉ types,ᵉ i.e.,ᵉ itᵉ isᵉ aᵉ
[pointedᵉ map](structured-types.pointed-types.mdᵉ) equippedᵉ with aᵉ
[pointedᵉ section](structured-types.pointed-sections.mdᵉ) andᵉ aᵉ
[pointedᵉ retraction](structured-types.pointed-retractions.md).ᵉ

## Definitions

### The predicate of being a pointed isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-pointed-isoᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pointed-isoᵉ = pointed-sectionᵉ fᵉ ×ᵉ pointed-retractionᵉ fᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {fᵉ : Aᵉ →∗ᵉ Bᵉ}
  (Hᵉ : is-pointed-isoᵉ fᵉ)
  where

  pointed-section-is-pointed-isoᵉ : pointed-sectionᵉ fᵉ
  pointed-section-is-pointed-isoᵉ = pr1ᵉ Hᵉ

  pointed-retraction-is-pointed-isoᵉ : pointed-retractionᵉ fᵉ
  pointed-retraction-is-pointed-isoᵉ = pr2ᵉ Hᵉ

  pointed-map-pointed-section-is-pointed-isoᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-pointed-section-is-pointed-isoᵉ =
    pointed-map-pointed-sectionᵉ fᵉ pointed-section-is-pointed-isoᵉ

  is-pointed-section-pointed-section-is-pointed-isoᵉ :
    is-pointed-sectionᵉ fᵉ pointed-map-pointed-section-is-pointed-isoᵉ
  is-pointed-section-pointed-section-is-pointed-isoᵉ =
    is-pointed-section-pointed-sectionᵉ fᵉ
      pointed-section-is-pointed-isoᵉ

  map-pointed-section-is-pointed-isoᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-pointed-section-is-pointed-isoᵉ =
    map-pointed-sectionᵉ fᵉ pointed-section-is-pointed-isoᵉ

  preserves-point-pointed-map-pointed-section-is-pointed-isoᵉ :
    map-pointed-section-is-pointed-isoᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-pointed-map-pointed-section-is-pointed-isoᵉ =
    preserves-point-pointed-map-pointed-sectionᵉ fᵉ
      pointed-section-is-pointed-isoᵉ

  is-section-pointed-section-is-pointed-isoᵉ :
    is-sectionᵉ (map-pointed-mapᵉ fᵉ) map-pointed-section-is-pointed-isoᵉ
  is-section-pointed-section-is-pointed-isoᵉ =
    is-section-pointed-sectionᵉ fᵉ pointed-section-is-pointed-isoᵉ

  section-is-pointed-isoᵉ :
    sectionᵉ (map-pointed-mapᵉ fᵉ)
  section-is-pointed-isoᵉ =
    section-pointed-sectionᵉ fᵉ pointed-section-is-pointed-isoᵉ

  coherence-point-is-section-pointed-section-is-pointed-isoᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( fᵉ ∘∗ᵉ pointed-map-pointed-section-is-pointed-isoᵉ)
      ( id-pointed-mapᵉ)
      ( is-section-pointed-section-is-pointed-isoᵉ)
  coherence-point-is-section-pointed-section-is-pointed-isoᵉ =
    coherence-point-is-section-pointed-sectionᵉ fᵉ
      pointed-section-is-pointed-isoᵉ

  pointed-map-pointed-retraction-is-pointed-isoᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-pointed-retraction-is-pointed-isoᵉ =
    pr1ᵉ pointed-retraction-is-pointed-isoᵉ

  is-pointed-retraction-pointed-retraction-is-pointed-isoᵉ :
    is-pointed-retractionᵉ fᵉ pointed-map-pointed-retraction-is-pointed-isoᵉ
  is-pointed-retraction-pointed-retraction-is-pointed-isoᵉ =
    pr2ᵉ pointed-retraction-is-pointed-isoᵉ

  map-pointed-retraction-is-pointed-isoᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-pointed-retraction-is-pointed-isoᵉ =
    map-pointed-mapᵉ pointed-map-pointed-retraction-is-pointed-isoᵉ

  preserves-point-pointed-map-pointed-retraction-is-pointed-isoᵉ :
    map-pointed-retraction-is-pointed-isoᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-pointed-map-pointed-retraction-is-pointed-isoᵉ =
    preserves-point-pointed-mapᵉ
      pointed-map-pointed-retraction-is-pointed-isoᵉ

  is-retraction-pointed-retraction-is-pointed-isoᵉ :
    is-retractionᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-retraction-is-pointed-isoᵉ)
  is-retraction-pointed-retraction-is-pointed-isoᵉ =
    htpy-pointed-htpyᵉ
      is-pointed-retraction-pointed-retraction-is-pointed-isoᵉ

  retraction-is-pointed-isoᵉ :
    retractionᵉ (map-pointed-mapᵉ fᵉ)
  retraction-is-pointed-isoᵉ =
    retraction-pointed-retractionᵉ fᵉ pointed-retraction-is-pointed-isoᵉ

  coherence-point-is-retraction-pointed-retraction-is-pointed-isoᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-pointed-retraction-is-pointed-isoᵉ ∘∗ᵉ fᵉ)
      ( id-pointed-mapᵉ)
      ( is-retraction-pointed-retraction-is-pointed-isoᵉ)
  coherence-point-is-retraction-pointed-retraction-is-pointed-isoᵉ =
    coherence-point-pointed-htpyᵉ
      is-pointed-retraction-pointed-retraction-is-pointed-isoᵉ
```

### Pointed isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  pointed-isoᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-isoᵉ = Σᵉ (Aᵉ →∗ᵉ Bᵉ) is-pointed-isoᵉ

  infix 6 _≅∗ᵉ_

  _≅∗ᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  _≅∗ᵉ_ = pointed-isoᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  (fᵉ : Aᵉ ≅∗ᵉ Bᵉ)
  where

  pointed-map-pointed-isoᵉ : Aᵉ →∗ᵉ Bᵉ
  pointed-map-pointed-isoᵉ = pr1ᵉ fᵉ

  map-pointed-isoᵉ : type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
  map-pointed-isoᵉ = map-pointed-mapᵉ pointed-map-pointed-isoᵉ

  preserves-point-pointed-isoᵉ :
    map-pointed-isoᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ
  preserves-point-pointed-isoᵉ =
    preserves-point-pointed-mapᵉ pointed-map-pointed-isoᵉ

  is-pointed-iso-pointed-isoᵉ : is-pointed-isoᵉ pointed-map-pointed-isoᵉ
  is-pointed-iso-pointed-isoᵉ = pr2ᵉ fᵉ

  pointed-section-pointed-isoᵉ : pointed-sectionᵉ pointed-map-pointed-isoᵉ
  pointed-section-pointed-isoᵉ =
    pointed-section-is-pointed-isoᵉ (is-pointed-iso-pointed-isoᵉ)

  pointed-retraction-pointed-isoᵉ : pointed-retractionᵉ pointed-map-pointed-isoᵉ
  pointed-retraction-pointed-isoᵉ =
    pointed-retraction-is-pointed-isoᵉ (is-pointed-iso-pointed-isoᵉ)

  pointed-map-pointed-section-pointed-isoᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-pointed-section-pointed-isoᵉ =
    pointed-map-pointed-section-is-pointed-isoᵉ (is-pointed-iso-pointed-isoᵉ)

  is-pointed-section-pointed-section-pointed-isoᵉ :
    is-pointed-sectionᵉ
      ( pointed-map-pointed-isoᵉ)
      ( pointed-map-pointed-section-pointed-isoᵉ)
  is-pointed-section-pointed-section-pointed-isoᵉ =
    is-pointed-section-pointed-section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  map-pointed-section-pointed-isoᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-pointed-section-pointed-isoᵉ =
    map-pointed-section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  preserves-point-pointed-map-pointed-section-pointed-isoᵉ :
    map-pointed-section-pointed-isoᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-pointed-map-pointed-section-pointed-isoᵉ =
    preserves-point-pointed-map-pointed-section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  is-section-pointed-section-pointed-isoᵉ :
    is-sectionᵉ (map-pointed-isoᵉ) map-pointed-section-pointed-isoᵉ
  is-section-pointed-section-pointed-isoᵉ =
    is-section-pointed-section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  section-pointed-isoᵉ :
    sectionᵉ (map-pointed-isoᵉ)
  section-pointed-isoᵉ =
    section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  coherence-point-is-section-pointed-section-pointed-isoᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-pointed-isoᵉ ∘∗ᵉ pointed-map-pointed-section-pointed-isoᵉ)
      ( id-pointed-mapᵉ)
      ( is-section-pointed-section-pointed-isoᵉ)
  coherence-point-is-section-pointed-section-pointed-isoᵉ =
    coherence-point-is-section-pointed-section-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  pointed-map-pointed-retraction-pointed-isoᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-pointed-retraction-pointed-isoᵉ =
    pointed-map-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  is-pointed-retraction-pointed-retraction-pointed-isoᵉ :
    is-pointed-retractionᵉ
      ( pointed-map-pointed-isoᵉ)
      ( pointed-map-pointed-retraction-pointed-isoᵉ)
  is-pointed-retraction-pointed-retraction-pointed-isoᵉ =
    is-pointed-retraction-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  map-pointed-retraction-pointed-isoᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-pointed-retraction-pointed-isoᵉ =
    map-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  preserves-point-pointed-map-pointed-retraction-pointed-isoᵉ :
    map-pointed-retraction-pointed-isoᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-pointed-map-pointed-retraction-pointed-isoᵉ =
    preserves-point-pointed-map-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  is-retraction-pointed-retraction-pointed-isoᵉ :
    is-retractionᵉ
      ( map-pointed-isoᵉ)
      ( map-pointed-retraction-pointed-isoᵉ)
  is-retraction-pointed-retraction-pointed-isoᵉ =
    is-retraction-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  retraction-pointed-isoᵉ :
    retractionᵉ (map-pointed-isoᵉ)
  retraction-pointed-isoᵉ =
    retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)

  coherence-point-is-retraction-pointed-retraction-pointed-isoᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-pointed-retraction-pointed-isoᵉ ∘∗ᵉ pointed-map-pointed-isoᵉ)
      ( id-pointed-mapᵉ)
      ( is-retraction-pointed-retraction-pointed-isoᵉ)
  coherence-point-is-retraction-pointed-retraction-pointed-isoᵉ =
    coherence-point-is-retraction-pointed-retraction-is-pointed-isoᵉ
      ( is-pointed-iso-pointed-isoᵉ)
```

## Properties

### Any pointed equivalence is a pointed isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  abstract
    is-pointed-iso-is-pointed-equivᵉ :
      is-pointed-equivᵉ fᵉ → is-pointed-isoᵉ fᵉ
    pr1ᵉ (pr1ᵉ (is-pointed-iso-is-pointed-equivᵉ Hᵉ)) =
      pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ
    pr2ᵉ (pr1ᵉ (is-pointed-iso-is-pointed-equivᵉ Hᵉ)) =
      is-pointed-section-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ
    pr1ᵉ (pr2ᵉ (is-pointed-iso-is-pointed-equivᵉ Hᵉ)) =
      pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ
    pr2ᵉ (pr2ᵉ (is-pointed-iso-is-pointed-equivᵉ Hᵉ)) =
      is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ
```

### Any pointed isomorphism is a pointed equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  abstract
    is-pointed-equiv-is-pointed-isoᵉ :
      is-pointed-isoᵉ fᵉ → is-pointed-equivᵉ fᵉ
    pr1ᵉ (is-pointed-equiv-is-pointed-isoᵉ Hᵉ) = section-is-pointed-isoᵉ Hᵉ
    pr2ᵉ (is-pointed-equiv-is-pointed-isoᵉ Hᵉ) = retraction-is-pointed-isoᵉ Hᵉ
```

### Being a pointed isomorphism is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  abstract
    is-contr-section-is-pointed-equivᵉ :
      is-pointed-equivᵉ fᵉ → is-contrᵉ (pointed-sectionᵉ fᵉ)
    is-contr-section-is-pointed-equivᵉ Hᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-contr-section-is-equivᵉ Hᵉ)
        ( map-inv-is-equivᵉ Hᵉ ,ᵉ is-section-map-inv-is-equivᵉ Hᵉ)
        ( is-contr-map-is-equivᵉ
          ( is-equiv-compᵉ _ _
            ( is-emb-is-equivᵉ Hᵉ _ _)
            ( is-equiv-concat'ᵉ _ (preserves-point-pointed-mapᵉ fᵉ)))
          ( _))

  abstract
    is-contr-retraction-is-pointed-equivᵉ :
      is-pointed-equivᵉ fᵉ → is-contrᵉ (pointed-retractionᵉ fᵉ)
    is-contr-retraction-is-pointed-equivᵉ Hᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-contr-retraction-is-equivᵉ Hᵉ)
        ( map-inv-is-equivᵉ Hᵉ ,ᵉ is-retraction-map-inv-is-equivᵉ Hᵉ)
        ( is-contr-map-is-equivᵉ
          ( is-equiv-concatᵉ _ _)
          ( _))

  abstract
    is-contr-is-pointed-iso-is-pointed-equivᵉ :
      is-pointed-equivᵉ fᵉ → is-contrᵉ (is-pointed-isoᵉ fᵉ)
    is-contr-is-pointed-iso-is-pointed-equivᵉ Hᵉ =
      is-contr-productᵉ
        ( is-contr-section-is-pointed-equivᵉ Hᵉ)
        ( is-contr-retraction-is-pointed-equivᵉ Hᵉ)

  abstract
    is-prop-is-pointed-isoᵉ : is-propᵉ (is-pointed-isoᵉ fᵉ)
    is-prop-is-pointed-isoᵉ =
      is-prop-is-proof-irrelevantᵉ
        ( λ Hᵉ →
          is-contr-is-pointed-iso-is-pointed-equivᵉ
            ( is-pointed-equiv-is-pointed-isoᵉ fᵉ Hᵉ))
```

### Being a pointed equivalence is equivalent to being a pointed isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  equiv-is-pointed-iso-is-pointed-equivᵉ :
    is-pointed-equivᵉ fᵉ ≃ᵉ (is-pointed-isoᵉ fᵉ)
  pr1ᵉ equiv-is-pointed-iso-is-pointed-equivᵉ =
    is-pointed-iso-is-pointed-equivᵉ fᵉ
  pr2ᵉ equiv-is-pointed-iso-is-pointed-equivᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-property-is-equivᵉ (map-pointed-mapᵉ fᵉ))
      ( is-prop-is-pointed-isoᵉ fᵉ)
      ( is-pointed-equiv-is-pointed-isoᵉ fᵉ)
```