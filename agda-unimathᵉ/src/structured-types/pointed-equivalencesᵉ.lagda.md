# Pointed equivalences

```agda
module structured-types.pointed-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.path-algebraᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-retractionsᵉ
open import structured-types.pointed-sectionsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.postcomposition-pointed-mapsᵉ
open import structured-types.precomposition-pointed-mapsᵉ
open import structured-types.universal-property-pointed-equivalencesᵉ
open import structured-types.whiskering-pointed-homotopies-compositionᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "pointedᵉ equivalence"ᵉ Agda=_≃∗ᵉ_}} `eᵉ : Aᵉ ≃∗ᵉ B`ᵉ consistsᵉ ofᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) `eᵉ : Aᵉ ≃ᵉ B`ᵉ equippedᵉ with anᵉ
[identification](foundation-core.identity-types.mdᵉ) `pᵉ : eᵉ *ᵉ ＝ᵉ *`ᵉ witnessingᵉ
thatᵉ theᵉ underlyingᵉ mapᵉ ofᵉ `e`ᵉ preservesᵉ theᵉ baseᵉ pointᵉ ofᵉ `A`.ᵉ

Theᵉ notionᵉ ofᵉ pointedᵉ equivalenceᵉ isᵉ describedᵉ equivalentlyᵉ asᵉ aᵉ
[pointedᵉ map](structured-types.pointed-maps.mdᵉ) ofᵉ whichᵉ theᵉ underlyingᵉ functionᵉ
isᵉ anᵉ [equivalence](foundation-core.equivalences.md),ᵉ i.e.,ᵉ

```text
  (Aᵉ ≃∗ᵉ Bᵉ) ≃ᵉ Σᵉ (fᵉ : Aᵉ →∗ᵉ B),ᵉ is-equivᵉ (map-pointed-mapᵉ fᵉ)
```

Furthermore,ᵉ aᵉ pointedᵉ equivalenceᵉ canᵉ alsoᵉ beᵉ describedᵉ equivalentlyᵉ asᵉ anᵉ
equivalenceᵉ in theᵉ categoryᵉ ofᵉ
[pointedᵉ types](structured-types.pointed-types.md).ᵉ

## Definitions

### The predicate of being a pointed equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-pointed-equivᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pointed-equivᵉ = is-equivᵉ (map-pointed-mapᵉ fᵉ)

  is-prop-is-pointed-equivᵉ : is-propᵉ is-pointed-equivᵉ
  is-prop-is-pointed-equivᵉ = is-property-is-equivᵉ (map-pointed-mapᵉ fᵉ)

  is-pointed-equiv-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-pointed-equiv-Propᵉ = is-equiv-Propᵉ (map-pointed-mapᵉ fᵉ)

  module _
    (Hᵉ : is-pointed-equivᵉ)
    where

    map-inv-is-pointed-equivᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
    map-inv-is-pointed-equivᵉ = map-inv-is-equivᵉ Hᵉ

    is-section-map-inv-is-pointed-equivᵉ :
      is-sectionᵉ (map-pointed-mapᵉ fᵉ) map-inv-is-pointed-equivᵉ
    is-section-map-inv-is-pointed-equivᵉ = is-section-map-inv-is-equivᵉ Hᵉ

    is-retraction-map-inv-is-pointed-equivᵉ :
      is-retractionᵉ (map-pointed-mapᵉ fᵉ) map-inv-is-pointed-equivᵉ
    is-retraction-map-inv-is-pointed-equivᵉ =
      is-retraction-map-inv-is-equivᵉ Hᵉ

    preserves-point-map-inv-is-pointed-equivᵉ :
      map-inv-is-pointed-equivᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ
    preserves-point-map-inv-is-pointed-equivᵉ =
      preserves-point-is-retraction-pointed-mapᵉ fᵉ
        ( map-inv-is-pointed-equivᵉ)
        ( is-retraction-map-inv-is-pointed-equivᵉ)

    pointed-map-inv-is-pointed-equivᵉ : Bᵉ →∗ᵉ Aᵉ
    pointed-map-inv-is-pointed-equivᵉ =
      pointed-map-is-retraction-pointed-mapᵉ fᵉ
        ( map-inv-is-pointed-equivᵉ)
        ( is-retraction-map-inv-is-pointed-equivᵉ)

    coherence-point-is-retraction-map-inv-is-pointed-equivᵉ :
      coherence-point-unpointed-htpy-pointed-Πᵉ
        ( pointed-map-inv-is-pointed-equivᵉ ∘∗ᵉ fᵉ)
        ( id-pointed-mapᵉ)
        ( is-retraction-map-inv-is-pointed-equivᵉ)
    coherence-point-is-retraction-map-inv-is-pointed-equivᵉ =
      coherence-point-is-retraction-pointed-mapᵉ fᵉ
        ( map-inv-is-pointed-equivᵉ)
        ( is-retraction-map-inv-is-pointed-equivᵉ)

    is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ :
      is-pointed-retractionᵉ fᵉ pointed-map-inv-is-pointed-equivᵉ
    is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ =
      is-pointed-retraction-is-retraction-pointed-mapᵉ fᵉ
        ( map-inv-is-pointed-equivᵉ)
        ( is-retraction-map-inv-is-pointed-equivᵉ)

    coherence-point-is-section-map-inv-is-pointed-equivᵉ :
      coherence-point-unpointed-htpy-pointed-Πᵉ
        ( fᵉ ∘∗ᵉ pointed-map-inv-is-pointed-equivᵉ)
        ( id-pointed-mapᵉ)
        ( is-section-map-inv-is-pointed-equivᵉ)
    coherence-point-is-section-map-inv-is-pointed-equivᵉ =
      ( right-whisker-concatᵉ
        ( ap-concatᵉ
          ( map-pointed-mapᵉ fᵉ)
          ( invᵉ (apᵉ _ (preserves-point-pointed-mapᵉ fᵉ)))
          ( _) ∙ᵉ
          ( horizontal-concat-Id²ᵉ
            ( ap-invᵉ
              ( map-pointed-mapᵉ fᵉ)
              ( apᵉ _ (preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
              ( invᵉ
                ( apᵉ
                  ( invᵉ)
                  ( ap-compᵉ
                    ( map-pointed-mapᵉ fᵉ)
                    ( map-inv-is-pointed-equivᵉ)
                    ( preserves-point-pointed-mapᵉ fᵉ)))))
            ( invᵉ (coherence-map-inv-is-equivᵉ Hᵉ (point-Pointed-Typeᵉ Aᵉ)))))
        ( preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
      ( assocᵉ
        ( invᵉ
          ( apᵉ
            ( map-pointed-mapᵉ fᵉ ∘ᵉ map-inv-is-pointed-equivᵉ)
            ( preserves-point-pointed-mapᵉ fᵉ)))
        ( is-section-map-inv-is-pointed-equivᵉ _)
        ( preserves-point-pointed-mapᵉ fᵉ)) ∙ᵉ
      ( invᵉ
        ( ( right-unitᵉ) ∙ᵉ
          ( left-transpose-eq-concatᵉ
            ( apᵉ
              ( map-pointed-mapᵉ fᵉ ∘ᵉ map-inv-is-pointed-equivᵉ)
              ( preserves-point-pointed-mapᵉ fᵉ))
            ( is-section-map-inv-is-pointed-equivᵉ _)
            ( ( is-section-map-inv-is-pointed-equivᵉ _) ∙ᵉ
              ( preserves-point-pointed-mapᵉ fᵉ))
            ( ( invᵉ (nat-htpyᵉ is-section-map-inv-is-pointed-equivᵉ _)) ∙ᵉ
              ( left-whisker-concatᵉ
                ( is-section-map-inv-is-pointed-equivᵉ _)
                ( ap-idᵉ (preserves-point-pointed-mapᵉ fᵉ)))))))

    is-pointed-section-pointed-map-inv-is-pointed-equivᵉ :
      is-pointed-sectionᵉ fᵉ pointed-map-inv-is-pointed-equivᵉ
    pr1ᵉ is-pointed-section-pointed-map-inv-is-pointed-equivᵉ =
      is-section-map-inv-is-pointed-equivᵉ
    pr2ᵉ is-pointed-section-pointed-map-inv-is-pointed-equivᵉ =
      coherence-point-is-section-map-inv-is-pointed-equivᵉ
```

### Pointed equivalences

```agda
pointed-equivᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
pointed-equivᵉ Aᵉ Bᵉ =
  Σᵉ ( type-Pointed-Typeᵉ Aᵉ ≃ᵉ type-Pointed-Typeᵉ Bᵉ)
    ( λ eᵉ → map-equivᵉ eᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ)

infix 6 _≃∗ᵉ_

_≃∗ᵉ_ = pointed-equivᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (eᵉ : Aᵉ ≃∗ᵉ Bᵉ)
  where

  equiv-pointed-equivᵉ : type-Pointed-Typeᵉ Aᵉ ≃ᵉ type-Pointed-Typeᵉ Bᵉ
  equiv-pointed-equivᵉ = pr1ᵉ eᵉ

  map-pointed-equivᵉ : type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Bᵉ
  map-pointed-equivᵉ = map-equivᵉ equiv-pointed-equivᵉ

  preserves-point-pointed-equivᵉ :
    map-pointed-equivᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ point-Pointed-Typeᵉ Bᵉ
  preserves-point-pointed-equivᵉ = pr2ᵉ eᵉ

  pointed-map-pointed-equivᵉ : Aᵉ →∗ᵉ Bᵉ
  pr1ᵉ pointed-map-pointed-equivᵉ = map-pointed-equivᵉ
  pr2ᵉ pointed-map-pointed-equivᵉ = preserves-point-pointed-equivᵉ

  is-equiv-map-pointed-equivᵉ : is-equivᵉ map-pointed-equivᵉ
  is-equiv-map-pointed-equivᵉ = is-equiv-map-equivᵉ equiv-pointed-equivᵉ

  is-pointed-equiv-pointed-equivᵉ :
    is-pointed-equivᵉ pointed-map-pointed-equivᵉ
  is-pointed-equiv-pointed-equivᵉ = is-equiv-map-pointed-equivᵉ

  pointed-map-inv-pointed-equivᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-inv-pointed-equivᵉ =
    pointed-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  map-inv-pointed-equivᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-inv-pointed-equivᵉ =
    map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  preserves-point-map-inv-pointed-equivᵉ :
    map-inv-pointed-equivᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ
  preserves-point-map-inv-pointed-equivᵉ =
    preserves-point-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  is-pointed-section-pointed-map-inv-pointed-equivᵉ :
    is-pointed-sectionᵉ
      ( pointed-map-pointed-equivᵉ)
      ( pointed-map-inv-pointed-equivᵉ)
  is-pointed-section-pointed-map-inv-pointed-equivᵉ =
    is-pointed-section-pointed-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  is-section-map-inv-pointed-equivᵉ :
    is-sectionᵉ
      ( map-pointed-equivᵉ)
      ( map-inv-pointed-equivᵉ)
  is-section-map-inv-pointed-equivᵉ =
    is-section-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  coherence-point-is-section-map-inv-pointed-equivᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-pointed-equivᵉ ∘∗ᵉ pointed-map-inv-pointed-equivᵉ)
      ( id-pointed-mapᵉ)
      ( is-section-map-inv-pointed-equivᵉ)
  coherence-point-is-section-map-inv-pointed-equivᵉ =
    coherence-point-is-section-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  is-pointed-retraction-pointed-map-inv-pointed-equivᵉ :
    is-pointed-retractionᵉ
      ( pointed-map-pointed-equivᵉ)
      ( pointed-map-inv-pointed-equivᵉ)
  is-pointed-retraction-pointed-map-inv-pointed-equivᵉ =
    is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  is-retraction-map-inv-pointed-equivᵉ :
    is-retractionᵉ
      ( map-pointed-equivᵉ)
      ( map-inv-pointed-equivᵉ)
  is-retraction-map-inv-pointed-equivᵉ =
    is-retraction-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)

  coherence-point-is-retraction-map-inv-pointed-equivᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( pointed-map-inv-pointed-equivᵉ ∘∗ᵉ pointed-map-pointed-equivᵉ)
      ( id-pointed-mapᵉ)
      ( is-retraction-map-inv-pointed-equivᵉ)
  coherence-point-is-retraction-map-inv-pointed-equivᵉ =
    coherence-point-is-retraction-map-inv-is-pointed-equivᵉ
      ( pointed-map-pointed-equivᵉ)
      ( is-pointed-equiv-pointed-equivᵉ)
```

### The equivalence between pointed equivalences and the type of pointed maps that are pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ)
  where

  compute-pointed-equivᵉ : (Aᵉ ≃∗ᵉ Bᵉ) ≃ᵉ Σᵉ (Aᵉ →∗ᵉ Bᵉ) is-pointed-equivᵉ
  compute-pointed-equivᵉ = equiv-right-swap-Σᵉ

  inv-compute-pointed-equivᵉ : Σᵉ (Aᵉ →∗ᵉ Bᵉ) is-pointed-equivᵉ ≃ᵉ (Aᵉ ≃∗ᵉ Bᵉ)
  inv-compute-pointed-equivᵉ = equiv-right-swap-Σᵉ
```

### The identity pointed equivalence

```agda
module _
  {lᵉ : Level} {Aᵉ : Pointed-Typeᵉ lᵉ}
  where

  id-pointed-equivᵉ : Aᵉ ≃∗ᵉ Aᵉ
  pr1ᵉ id-pointed-equivᵉ = id-equivᵉ
  pr2ᵉ id-pointed-equivᵉ = reflᵉ
```

### Composition of pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  comp-pointed-equivᵉ : (Bᵉ ≃∗ᵉ Cᵉ) → (Aᵉ ≃∗ᵉ Bᵉ) → (Aᵉ ≃∗ᵉ Cᵉ)
  pr1ᵉ (comp-pointed-equivᵉ fᵉ eᵉ) =
    equiv-pointed-equivᵉ fᵉ ∘eᵉ equiv-pointed-equivᵉ eᵉ
  pr2ᵉ (comp-pointed-equivᵉ fᵉ eᵉ) =
    preserves-point-comp-pointed-mapᵉ
      ( pointed-map-pointed-equivᵉ fᵉ)
      ( pointed-map-pointed-equivᵉ eᵉ)
```

### Inverses of pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (eᵉ : Aᵉ ≃∗ᵉ Bᵉ)
  where

  abstract
    is-pointed-equiv-inv-pointed-equivᵉ :
      is-pointed-equivᵉ (pointed-map-inv-pointed-equivᵉ eᵉ)
    is-pointed-equiv-inv-pointed-equivᵉ =
      is-equiv-is-invertibleᵉ
        ( map-pointed-equivᵉ eᵉ)
        ( is-retraction-map-inv-pointed-equivᵉ eᵉ)
        ( is-section-map-inv-pointed-equivᵉ eᵉ)

  equiv-inv-pointed-equivᵉ : type-Pointed-Typeᵉ Bᵉ ≃ᵉ type-Pointed-Typeᵉ Aᵉ
  pr1ᵉ equiv-inv-pointed-equivᵉ = map-inv-pointed-equivᵉ eᵉ
  pr2ᵉ equiv-inv-pointed-equivᵉ = is-pointed-equiv-inv-pointed-equivᵉ

  inv-pointed-equivᵉ : Bᵉ ≃∗ᵉ Aᵉ
  pr1ᵉ inv-pointed-equivᵉ = equiv-inv-pointed-equivᵉ
  pr2ᵉ inv-pointed-equivᵉ = preserves-point-map-inv-pointed-equivᵉ eᵉ
```

## Properties

### Extensionality of the universe of pointed types

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  abstract
    is-torsorial-pointed-equivᵉ :
      is-torsorialᵉ (λ (Bᵉ : Pointed-Typeᵉ l1ᵉ) → Aᵉ ≃∗ᵉ Bᵉ)
    is-torsorial-pointed-equivᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (type-Pointed-Typeᵉ Aᵉ))
        ( type-Pointed-Typeᵉ Aᵉ ,ᵉ id-equivᵉ)
        ( is-torsorial-Idᵉ (point-Pointed-Typeᵉ Aᵉ))

  extensionality-Pointed-Typeᵉ : (Bᵉ : Pointed-Typeᵉ l1ᵉ) → (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ (Aᵉ ≃∗ᵉ Bᵉ)
  extensionality-Pointed-Typeᵉ =
    extensionality-Σᵉ
      ( λ bᵉ eᵉ → map-equivᵉ eᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ bᵉ)
      ( id-equivᵉ)
      ( reflᵉ)
      ( λ Bᵉ → equiv-univalenceᵉ)
      ( λ aᵉ → id-equivᵉ)

  eq-pointed-equivᵉ : (Bᵉ : Pointed-Typeᵉ l1ᵉ) → Aᵉ ≃∗ᵉ Bᵉ → Aᵉ ＝ᵉ Bᵉ
  eq-pointed-equivᵉ Bᵉ = map-inv-equivᵉ (extensionality-Pointed-Typeᵉ Bᵉ)
```

### Any pointed map satisfying the universal property of pointed equivalences is a pointed equivalence

Inᵉ otherᵉ words,ᵉ anyᵉ pointedᵉ mapᵉ `fᵉ : Aᵉ →∗ᵉ B`ᵉ suchᵉ thatᵉ precomposingᵉ byᵉ `f`ᵉ

```text
  -ᵉ ∘∗ᵉ fᵉ : (Bᵉ →∗ᵉ Cᵉ) → (Aᵉ →∗ᵉ Cᵉ)
```

isᵉ anᵉ equivalenceᵉ forᵉ anyᵉ pointedᵉ typeᵉ `C`,ᵉ isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (Hᵉ : universal-property-pointed-equivᵉ fᵉ)
  where

  pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    map-inv-is-equivᵉ (Hᵉ Aᵉ) id-pointed-mapᵉ

  map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    map-pointed-mapᵉ
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ

  preserves-point-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ
      ( point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    preserves-point-pointed-mapᵉ
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ

  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    is-pointed-retractionᵉ fᵉ
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ
  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    pointed-htpy-eqᵉ _ _ (is-section-map-inv-is-equivᵉ (Hᵉ Aᵉ) (id-pointed-mapᵉ))

  is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    is-retractionᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)
  is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    htpy-pointed-htpyᵉ
      ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)

  is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    is-pointed-sectionᵉ fᵉ
      pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ
  is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    pointed-htpy-eqᵉ _ _
      ( is-injective-is-equivᵉ (Hᵉ Bᵉ)
        ( eq-pointed-htpyᵉ ((fᵉ ∘∗ᵉ _) ∘∗ᵉ fᵉ) (id-pointed-mapᵉ ∘∗ᵉ fᵉ)
          ( concat-pointed-htpyᵉ
            ( associative-comp-pointed-mapᵉ fᵉ _ fᵉ)
            ( concat-pointed-htpyᵉ
              ( left-whisker-comp-pointed-htpyᵉ fᵉ _ _
                ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ))
              ( concat-pointed-htpyᵉ
                ( right-unit-law-comp-pointed-mapᵉ fᵉ)
                ( inv-left-unit-law-comp-pointed-mapᵉ fᵉ))))))

  is-section-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ :
    is-sectionᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)
  is-section-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ =
    htpy-pointed-htpyᵉ
      ( is-pointed-section-pointed-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)

  abstract
    is-pointed-equiv-universal-property-pointed-equivᵉ : is-pointed-equivᵉ fᵉ
    is-pointed-equiv-universal-property-pointed-equivᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)
        ( is-section-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)
        ( is-retraction-map-inv-is-pointed-equiv-universal-property-pointed-equivᵉ)
```

### Any pointed equivalence satisfies the universal property of pointed equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ :
    (Hᵉ : is-pointed-equivᵉ fᵉ) {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) →
    (Aᵉ →∗ᵉ Cᵉ) → (Bᵉ →∗ᵉ Cᵉ)
  map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ =
    precomp-pointed-mapᵉ
      ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
      ( Cᵉ)

  is-section-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ :
    (Hᵉ : is-pointed-equivᵉ fᵉ) →
    {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) →
    is-sectionᵉ
      ( precomp-pointed-mapᵉ fᵉ Cᵉ)
      ( map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ
        ( Hᵉ)
        ( Cᵉ))
  is-section-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ hᵉ =
    eq-pointed-htpyᵉ
      ( (hᵉ ∘∗ᵉ pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ) ∘∗ᵉ fᵉ)
      ( hᵉ)
      ( concat-pointed-htpyᵉ
        ( associative-comp-pointed-mapᵉ hᵉ
          ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
          ( fᵉ))
        ( left-whisker-comp-pointed-htpyᵉ hᵉ
          ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ ∘∗ᵉ fᵉ)
          ( id-pointed-mapᵉ)
          ( is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)))

  section-universal-property-pointed-equiv-is-pointed-equivᵉ :
    (Hᵉ : is-pointed-equivᵉ fᵉ) →
    {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) →
    sectionᵉ (precomp-pointed-mapᵉ fᵉ Cᵉ)
  pr1ᵉ (section-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
    map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ
  pr2ᵉ (section-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
    is-section-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ
      ( Hᵉ)
      ( Cᵉ)

  is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ :
    (Hᵉ : is-pointed-equivᵉ fᵉ) →
    {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) →
    is-retractionᵉ
      ( precomp-pointed-mapᵉ fᵉ Cᵉ)
      ( map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ
        ( Hᵉ)
        ( Cᵉ))
  is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ
    Hᵉ Cᵉ hᵉ =
    eq-pointed-htpyᵉ
      ( (hᵉ ∘∗ᵉ fᵉ) ∘∗ᵉ pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
      ( hᵉ)
      ( concat-pointed-htpyᵉ
        ( associative-comp-pointed-mapᵉ hᵉ fᵉ
          ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ))
        ( left-whisker-comp-pointed-htpyᵉ hᵉ
          ( fᵉ ∘∗ᵉ pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
          ( id-pointed-mapᵉ)
          ( is-pointed-section-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)))

  retraction-universal-property-pointed-equiv-is-pointed-equivᵉ :
    (Hᵉ : is-pointed-equivᵉ fᵉ) →
    {lᵉ : Level} (Cᵉ : Pointed-Typeᵉ lᵉ) →
    retractionᵉ (precomp-pointed-mapᵉ fᵉ Cᵉ)
  pr1ᵉ (retraction-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
    map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ
  pr2ᵉ (retraction-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
    is-retraction-map-inv-universal-property-pointed-equiv-is-pointed-equivᵉ
      ( Hᵉ)
      ( Cᵉ)

  abstract
    universal-property-pointed-equiv-is-pointed-equivᵉ :
      is-pointed-equivᵉ fᵉ →
      universal-property-pointed-equivᵉ fᵉ
    pr1ᵉ (universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
      section-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ
    pr2ᵉ (universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ) =
      retraction-universal-property-pointed-equiv-is-pointed-equivᵉ Hᵉ Cᵉ

equiv-precomp-pointed-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (Cᵉ : Pointed-Typeᵉ l3ᵉ) → (Aᵉ ≃∗ᵉ Bᵉ) → (Bᵉ →∗ᵉ Cᵉ) ≃ᵉ (Aᵉ →∗ᵉ Cᵉ)
pr1ᵉ (equiv-precomp-pointed-mapᵉ Cᵉ fᵉ) gᵉ =
  gᵉ ∘∗ᵉ (pointed-map-pointed-equivᵉ fᵉ)
pr2ᵉ (equiv-precomp-pointed-mapᵉ Cᵉ fᵉ) =
  universal-property-pointed-equiv-is-pointed-equivᵉ
    ( pointed-map-pointed-equivᵉ fᵉ)
    ( is-equiv-map-pointed-equivᵉ fᵉ)
    ( Cᵉ)
```

### Postcomposing by pointed equivalences is a pointed equivalence

#### The predicate of being an equivalence by postcomposition of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-equiv-postcomp-pointed-mapᵉ : UUωᵉ
  is-equiv-postcomp-pointed-mapᵉ =
    {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ) → is-equivᵉ (postcomp-pointed-mapᵉ fᵉ Xᵉ)
```

#### Any pointed map that is an equivalence by postcomposition is a pointed equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (Hᵉ : is-equiv-postcomp-pointed-mapᵉ fᵉ)
  where

  pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ : Bᵉ →∗ᵉ Aᵉ
  pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    map-inv-is-equivᵉ (Hᵉ Bᵉ) id-pointed-mapᵉ

  map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
  map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    map-pointed-mapᵉ
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)

  is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ :
    is-pointed-sectionᵉ fᵉ
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
  is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    pointed-htpy-eqᵉ
      ( fᵉ ∘∗ᵉ pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
      ( id-pointed-mapᵉ)
      ( is-section-map-inv-is-equivᵉ (Hᵉ Bᵉ) id-pointed-mapᵉ)

  is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ :
    is-sectionᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
  is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    htpy-pointed-htpyᵉ
      ( is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)

  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ :
    is-pointed-retractionᵉ fᵉ
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
  is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    pointed-htpy-eqᵉ
      ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ ∘∗ᵉ fᵉ)
      ( id-pointed-mapᵉ)
      ( is-injective-is-equivᵉ
        ( Hᵉ Aᵉ)
        ( eq-pointed-htpyᵉ
          ( ( fᵉ) ∘∗ᵉ
            ( ( pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ) ∘∗ᵉ
              ( fᵉ)))
          ( fᵉ ∘∗ᵉ id-pointed-mapᵉ)
          ( concat-pointed-htpyᵉ
            ( inv-associative-comp-pointed-mapᵉ fᵉ _ fᵉ)
            ( concat-pointed-htpyᵉ
              ( right-whisker-comp-pointed-htpyᵉ
                ( fᵉ ∘∗ᵉ _)
                ( id-pointed-mapᵉ)
                ( is-pointed-section-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
                ( fᵉ))
              ( concat-pointed-htpyᵉ
                ( left-unit-law-comp-pointed-mapᵉ fᵉ)
                ( inv-pointed-htpyᵉ (right-unit-law-comp-pointed-mapᵉ fᵉ)))))))

  is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ :
    is-retractionᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
  is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
    htpy-pointed-htpyᵉ
      ( is-pointed-retraction-pointed-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)

  abstract
    is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ : is-pointed-equivᵉ fᵉ
    is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
        ( is-section-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
        ( is-retraction-map-inv-is-pointed-equiv-is-equiv-postcomp-pointed-mapᵉ)
```

#### Any pointed equivalence is an equivalence by postcomposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  (Hᵉ : is-pointed-equivᵉ fᵉ)
  where

  map-inv-is-equiv-postcomp-is-pointed-equivᵉ :
    {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ) → (Xᵉ →∗ᵉ Bᵉ) → (Xᵉ →∗ᵉ Aᵉ)
  map-inv-is-equiv-postcomp-is-pointed-equivᵉ =
    postcomp-pointed-mapᵉ (pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)

  is-section-map-inv-is-equiv-postcomp-is-pointed-equivᵉ :
    {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ) →
    is-sectionᵉ
      ( postcomp-pointed-mapᵉ fᵉ Xᵉ)
      ( map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ)
  is-section-map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ hᵉ =
    eq-pointed-htpyᵉ
      ( fᵉ ∘∗ᵉ (pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ ∘∗ᵉ hᵉ))
      ( hᵉ)
      ( concat-pointed-htpyᵉ
        ( inv-associative-comp-pointed-mapᵉ fᵉ
          ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
          ( hᵉ))
        ( concat-pointed-htpyᵉ
          ( right-whisker-comp-pointed-htpyᵉ
            ( fᵉ ∘∗ᵉ pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
            ( id-pointed-mapᵉ)
            ( is-pointed-section-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
            ( hᵉ))
          ( left-unit-law-comp-pointed-mapᵉ hᵉ)))

  is-retraction-map-inv-is-equiv-postcomp-is-pointed-equivᵉ :
    {lᵉ : Level} (Xᵉ : Pointed-Typeᵉ lᵉ) →
    is-retractionᵉ
      ( postcomp-pointed-mapᵉ fᵉ Xᵉ)
      ( map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ)
  is-retraction-map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ hᵉ =
    eq-pointed-htpyᵉ
      ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ ∘∗ᵉ (fᵉ ∘∗ᵉ hᵉ))
      ( hᵉ)
      ( concat-pointed-htpyᵉ
        ( inv-associative-comp-pointed-mapᵉ
          ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
          ( fᵉ)
          ( hᵉ))
        ( concat-pointed-htpyᵉ
          ( right-whisker-comp-pointed-htpyᵉ
            ( pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ ∘∗ᵉ fᵉ)
            ( id-pointed-mapᵉ)
            ( is-pointed-retraction-pointed-map-inv-is-pointed-equivᵉ fᵉ Hᵉ)
            ( hᵉ))
          ( left-unit-law-comp-pointed-mapᵉ hᵉ)))

  abstract
    is-equiv-postcomp-is-pointed-equivᵉ : is-equiv-postcomp-pointed-mapᵉ fᵉ
    is-equiv-postcomp-is-pointed-equivᵉ Xᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ)
        ( is-section-map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ)
        ( is-retraction-map-inv-is-equiv-postcomp-is-pointed-equivᵉ Xᵉ)

equiv-postcomp-pointed-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (Cᵉ : Pointed-Typeᵉ l3ᵉ) → (Aᵉ ≃∗ᵉ Bᵉ) → (Cᵉ →∗ᵉ Aᵉ) ≃ᵉ (Cᵉ →∗ᵉ Bᵉ)
pr1ᵉ (equiv-postcomp-pointed-mapᵉ Cᵉ eᵉ) =
  postcomp-pointed-mapᵉ (pointed-map-pointed-equivᵉ eᵉ) Cᵉ
pr2ᵉ (equiv-postcomp-pointed-mapᵉ Cᵉ eᵉ) =
  is-equiv-postcomp-is-pointed-equivᵉ
    ( pointed-map-pointed-equivᵉ eᵉ)
    ( is-pointed-equiv-pointed-equivᵉ eᵉ)
    ( Cᵉ)
```

### The composition operation on pointed equivalences is a binary equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} {Cᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  abstract
    is-equiv-comp-pointed-equivᵉ :
      (fᵉ : Bᵉ ≃∗ᵉ Cᵉ) → is-equivᵉ (λ (eᵉ : Aᵉ ≃∗ᵉ Bᵉ) → comp-pointed-equivᵉ fᵉ eᵉ)
    is-equiv-comp-pointed-equivᵉ fᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-postcomp-equiv-equivᵉ (equiv-pointed-equivᵉ fᵉ))
        ( λ eᵉ →
          is-equiv-compᵉ _
            ( apᵉ (map-pointed-equivᵉ fᵉ))
            ( is-emb-is-equivᵉ (is-equiv-map-pointed-equivᵉ fᵉ) _ _)
            ( is-equiv-concat'ᵉ _ (preserves-point-pointed-equivᵉ fᵉ)))

  equiv-comp-pointed-equivᵉ : (fᵉ : Bᵉ ≃∗ᵉ Cᵉ) → (Aᵉ ≃∗ᵉ Bᵉ) ≃ᵉ (Aᵉ ≃∗ᵉ Cᵉ)
  pr1ᵉ (equiv-comp-pointed-equivᵉ fᵉ) = comp-pointed-equivᵉ fᵉ
  pr2ᵉ (equiv-comp-pointed-equivᵉ fᵉ) = is-equiv-comp-pointed-equivᵉ fᵉ

  abstract
    is-equiv-comp-pointed-equiv'ᵉ :
      (eᵉ : Aᵉ ≃∗ᵉ Bᵉ) → is-equivᵉ (λ (fᵉ : Bᵉ ≃∗ᵉ Cᵉ) → comp-pointed-equivᵉ fᵉ eᵉ)
    is-equiv-comp-pointed-equiv'ᵉ eᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-precomp-equiv-equivᵉ (equiv-pointed-equivᵉ eᵉ))
        ( λ fᵉ →
          is-equiv-concatᵉ
            ( apᵉ (map-equivᵉ fᵉ) (preserves-point-pointed-equivᵉ eᵉ))
            ( _))

  equiv-comp-pointed-equiv'ᵉ :
    (eᵉ : Aᵉ ≃∗ᵉ Bᵉ) → (Bᵉ ≃∗ᵉ Cᵉ) ≃ᵉ (Aᵉ ≃∗ᵉ Cᵉ)
  pr1ᵉ (equiv-comp-pointed-equiv'ᵉ eᵉ) fᵉ = comp-pointed-equivᵉ fᵉ eᵉ
  pr2ᵉ (equiv-comp-pointed-equiv'ᵉ eᵉ) = is-equiv-comp-pointed-equiv'ᵉ eᵉ

  abstract
    is-binary-equiv-comp-pointed-equivᵉ :
      is-binary-equivᵉ (λ (fᵉ : Bᵉ ≃∗ᵉ Cᵉ) (eᵉ : Aᵉ ≃∗ᵉ Bᵉ) → comp-pointed-equivᵉ fᵉ eᵉ)
    pr1ᵉ is-binary-equiv-comp-pointed-equivᵉ = is-equiv-comp-pointed-equiv'ᵉ
    pr2ᵉ is-binary-equiv-comp-pointed-equivᵉ = is-equiv-comp-pointed-equivᵉ
```