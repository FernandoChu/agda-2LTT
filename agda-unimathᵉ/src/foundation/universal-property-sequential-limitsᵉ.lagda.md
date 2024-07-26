# The universal property of sequential limits

```agda
module foundation.universal-property-sequential-limitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-inverse-sequential-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ anᵉ
[inverseᵉ sequentialᵉ diagramᵉ ofᵉ types](foundation.inverse-sequential-diagrams.mdᵉ)

```text
               fₙᵉ                     f₁ᵉ      f₀ᵉ
  ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀ᵉ
```

theᵉ **sequentialᵉ limit**ᵉ `limₙᵉ Aₙ`ᵉ isᵉ aᵉ universalᵉ typeᵉ completingᵉ theᵉ diagramᵉ

```text
                           fₙᵉ                     f₁ᵉ      f₀ᵉ
  limₙᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ Aₙ₊₁ᵉ --->ᵉ Aₙᵉ --->ᵉ ⋯ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀.ᵉ
```

Theᵉ **universalᵉ propertyᵉ ofᵉ theᵉ sequentialᵉ limit**ᵉ statesᵉ thatᵉ `limₙᵉ Aₙ`ᵉ isᵉ theᵉ
terminalᵉ suchᵉ type,ᵉ byᵉ whichᵉ weᵉ meanᵉ thatᵉ givenᵉ anyᵉ
[cone](foundation.cones-over-inverse-sequential-diagrams.mdᵉ) overᵉ `A`ᵉ with
domainᵉ `X`,ᵉ thereᵉ isᵉ aᵉ [unique](foundation-core.contractible-types.mdᵉ) mapᵉ
`gᵉ : Xᵉ → limₙᵉ Aₙ`ᵉ exhibitingᵉ thatᵉ coneᵉ asᵉ aᵉ compositeᵉ ofᵉ `g`ᵉ with theᵉ coneᵉ ofᵉ
`limₙᵉ Aₙ`ᵉ overᵉ `A`.ᵉ

## Definition

### The universal property of sequential limits

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  universal-property-sequential-limitᵉ : UUωᵉ
  universal-property-sequential-limitᵉ =
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    is-equivᵉ (cone-map-inverse-sequential-diagramᵉ Aᵉ {Yᵉ = Yᵉ} cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  map-universal-property-sequential-limitᵉ :
    universal-property-sequential-limitᵉ Aᵉ cᵉ →
    {Yᵉ : UUᵉ l3ᵉ} (c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ) → Yᵉ → Xᵉ
  map-universal-property-sequential-limitᵉ up-cᵉ {Yᵉ} c'ᵉ =
    map-inv-is-equivᵉ (up-cᵉ Yᵉ) c'ᵉ

  compute-map-universal-property-sequential-limitᵉ :
    (up-cᵉ : universal-property-sequential-limitᵉ Aᵉ cᵉ) →
    {Yᵉ : UUᵉ l3ᵉ} (c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ) →
    cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ
      ( map-universal-property-sequential-limitᵉ up-cᵉ c'ᵉ) ＝ᵉ
    c'ᵉ
  compute-map-universal-property-sequential-limitᵉ up-cᵉ {Yᵉ} c'ᵉ =
    is-section-map-inv-is-equivᵉ (up-cᵉ Yᵉ) c'ᵉ
```

## Properties

### 3-for-2 property of sequential limits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  (c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ)
  (hᵉ : Yᵉ → Xᵉ)
  (KLMᵉ :
    htpy-cone-inverse-sequential-diagramᵉ Aᵉ
      ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ hᵉ) c'ᵉ)
  where

  inv-triangle-cone-cone-inverse-sequential-diagramᵉ :
    {l6ᵉ : Level} (Dᵉ : UUᵉ l6ᵉ) →
    cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ ∘ᵉ postcompᵉ Dᵉ hᵉ ~ᵉ
    cone-map-inverse-sequential-diagramᵉ Aᵉ c'ᵉ
  inv-triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ kᵉ =
    apᵉ
      ( λ tᵉ → cone-map-inverse-sequential-diagramᵉ Aᵉ tᵉ kᵉ)
      ( eq-htpy-cone-inverse-sequential-diagramᵉ Aᵉ
        ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ hᵉ) c'ᵉ KLMᵉ)

  triangle-cone-cone-inverse-sequential-diagramᵉ :
    {l6ᵉ : Level} (Dᵉ : UUᵉ l6ᵉ) →
    cone-map-inverse-sequential-diagramᵉ Aᵉ c'ᵉ ~ᵉ
    cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ ∘ᵉ postcompᵉ Dᵉ hᵉ
  triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ kᵉ =
    invᵉ (inv-triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ kᵉ)

  abstract
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limitᵉ :
      universal-property-sequential-limitᵉ Aᵉ cᵉ →
      universal-property-sequential-limitᵉ Aᵉ c'ᵉ →
      is-equivᵉ hᵉ
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limitᵉ
      upᵉ up'ᵉ =
      is-equiv-is-equiv-postcompᵉ hᵉ
        ( λ Dᵉ →
          is-equiv-top-map-triangleᵉ
            ( cone-map-inverse-sequential-diagramᵉ Aᵉ c'ᵉ)
            ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ)
            ( postcompᵉ Dᵉ hᵉ)
            ( triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ)
            ( upᵉ Dᵉ)
            ( up'ᵉ Dᵉ))

  abstract
    universal-property-sequential-limit-universal-property-sequential-limit-is-equivᵉ :
      is-equivᵉ hᵉ →
      universal-property-sequential-limitᵉ Aᵉ cᵉ →
      universal-property-sequential-limitᵉ Aᵉ c'ᵉ
    universal-property-sequential-limit-universal-property-sequential-limit-is-equivᵉ
      is-equiv-hᵉ upᵉ Dᵉ =
      is-equiv-left-map-triangleᵉ
        ( cone-map-inverse-sequential-diagramᵉ Aᵉ c'ᵉ)
        ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ)
        ( postcompᵉ Dᵉ hᵉ)
        ( triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ)
        ( is-equiv-postcomp-is-equivᵉ hᵉ is-equiv-hᵉ Dᵉ)
        ( upᵉ Dᵉ)

  abstract
    universal-property-sequential-limit-is-equiv-universal-property-sequential-limitᵉ :
      universal-property-sequential-limitᵉ Aᵉ c'ᵉ →
      is-equivᵉ hᵉ →
      universal-property-sequential-limitᵉ Aᵉ cᵉ
    universal-property-sequential-limit-is-equiv-universal-property-sequential-limitᵉ
      up'ᵉ is-equiv-hᵉ Dᵉ =
      is-equiv-right-map-triangleᵉ
        ( cone-map-inverse-sequential-diagramᵉ Aᵉ c'ᵉ)
        ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ)
        ( postcompᵉ Dᵉ hᵉ)
        ( triangle-cone-cone-inverse-sequential-diagramᵉ Dᵉ)
        ( up'ᵉ Dᵉ)
        ( is-equiv-postcomp-is-equivᵉ hᵉ is-equiv-hᵉ Dᵉ)
```

### Uniqueness of maps obtained via the universal property of sequential limits

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  abstract
    uniqueness-universal-property-sequential-limitᵉ :
      universal-property-sequential-limitᵉ Aᵉ cᵉ →
      {l3ᵉ : Level} (Yᵉ : UUᵉ l3ᵉ) (c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ) →
      is-contrᵉ
        ( Σᵉ ( Yᵉ → Xᵉ)
            ( λ hᵉ →
              htpy-cone-inverse-sequential-diagramᵉ Aᵉ
                ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ hᵉ)
                (c'ᵉ)))
    uniqueness-universal-property-sequential-limitᵉ upᵉ Yᵉ c'ᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (Yᵉ → Xᵉ) (λ hᵉ → cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ hᵉ ＝ᵉ c'ᵉ))
        ( equiv-totᵉ
          ( λ hᵉ →
            extensionality-cone-inverse-sequential-diagramᵉ Aᵉ
              ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ hᵉ)
              ( c'ᵉ)))
        ( is-contr-map-is-equivᵉ (upᵉ Yᵉ) c'ᵉ)
```

### The homotopy of cones obtained from the universal property of sequential limits

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  where

  htpy-cone-map-universal-property-sequential-limitᵉ :
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ)
    (upᵉ : universal-property-sequential-limitᵉ Aᵉ cᵉ) →
    {l3ᵉ : Level} {Yᵉ : UUᵉ l3ᵉ} (c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ) →
    htpy-cone-inverse-sequential-diagramᵉ Aᵉ
      ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ
        ( map-universal-property-sequential-limitᵉ Aᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
  htpy-cone-map-universal-property-sequential-limitᵉ cᵉ upᵉ c'ᵉ =
    htpy-eq-cone-inverse-sequential-diagramᵉ Aᵉ
      ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ
        ( map-universal-property-sequential-limitᵉ Aᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( compute-map-universal-property-sequential-limitᵉ Aᵉ cᵉ upᵉ c'ᵉ)
```

### Unique uniqueness of sequential limits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  where

  abstract
    uniquely-unique-sequential-limitᵉ :
      ( c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ)
      ( cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
      ( up-c'ᵉ : universal-property-sequential-limitᵉ Aᵉ c'ᵉ) →
      ( up-cᵉ : universal-property-sequential-limitᵉ Aᵉ cᵉ) →
      is-contrᵉ
        ( Σᵉ (Yᵉ ≃ᵉ Xᵉ)
            ( λ eᵉ →
              htpy-cone-inverse-sequential-diagramᵉ Aᵉ
                ( cone-map-inverse-sequential-diagramᵉ Aᵉ cᵉ (map-equivᵉ eᵉ)) c'ᵉ))
    uniquely-unique-sequential-limitᵉ c'ᵉ cᵉ up-c'ᵉ up-cᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( uniqueness-universal-property-sequential-limitᵉ Aᵉ cᵉ up-cᵉ Yᵉ c'ᵉ)
        ( is-property-is-equivᵉ)
        ( map-universal-property-sequential-limitᵉ Aᵉ cᵉ up-cᵉ c'ᵉ)
        ( htpy-cone-map-universal-property-sequential-limitᵉ Aᵉ cᵉ up-cᵉ c'ᵉ)
        ( is-equiv-universal-property-sequential-limit-universal-property-sequential-limitᵉ
          ( cᵉ)
          ( c'ᵉ)
          ( map-universal-property-sequential-limitᵉ Aᵉ cᵉ up-cᵉ c'ᵉ)
          ( htpy-cone-map-universal-property-sequential-limitᵉ Aᵉ cᵉ up-cᵉ c'ᵉ)
          ( up-cᵉ)
          ( up-c'ᵉ))
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}

## See also

-ᵉ Forᵉ sequentialᵉ colimits,ᵉ seeᵉ
  [`synthetic-homotopy-theory.universal-property-sequential-colimits`](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)