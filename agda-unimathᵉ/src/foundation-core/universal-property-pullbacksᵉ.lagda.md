# The universal property of pullbacks

```agda
module foundation-core.universal-property-pullbacksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Definition

### The universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  universal-property-pullbackᵉ : UUωᵉ
  universal-property-pullbackᵉ =
    {lᵉ : Level} (C'ᵉ : UUᵉ lᵉ) → is-equivᵉ (cone-mapᵉ fᵉ gᵉ cᵉ {C'ᵉ})

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  map-universal-property-pullbackᵉ :
    universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
    {C'ᵉ : UUᵉ l5ᵉ} (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ) → C'ᵉ → Cᵉ
  map-universal-property-pullbackᵉ up-cᵉ {C'ᵉ} =
    map-inv-is-equivᵉ (up-cᵉ C'ᵉ)

  compute-map-universal-property-pullbackᵉ :
    (up-cᵉ : universal-property-pullbackᵉ fᵉ gᵉ cᵉ) →
    {C'ᵉ : UUᵉ l5ᵉ} (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ) →
    cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ up-cᵉ c'ᵉ) ＝ᵉ c'ᵉ
  compute-map-universal-property-pullbackᵉ up-cᵉ {C'ᵉ} =
    is-section-map-inv-is-equivᵉ (up-cᵉ C'ᵉ)
```

## Properties

### The homotopy of cones obtained from the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ}
  (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (upᵉ : universal-property-pullbackᵉ fᵉ gᵉ cᵉ)
  {l5ᵉ : Level} {C'ᵉ : UUᵉ l5ᵉ} (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ)
  where

  htpy-cone-map-universal-property-pullbackᵉ :
    htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
  htpy-cone-map-universal-property-pullbackᵉ =
    htpy-eq-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( compute-map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)

  htpy-vertical-map-map-universal-property-pullbackᵉ :
    vertical-map-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)) ~ᵉ
      vertical-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-vertical-map-map-universal-property-pullbackᵉ =
    htpy-vertical-map-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-map-universal-property-pullbackᵉ)

  htpy-horizontal-map-map-universal-property-pullbackᵉ :
    horizontal-map-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ)) ~ᵉ
      horizontal-map-coneᵉ fᵉ gᵉ c'ᵉ
  htpy-horizontal-map-map-universal-property-pullbackᵉ =
    htpy-horizontal-map-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-map-universal-property-pullbackᵉ)

  coh-htpy-cone-map-universal-property-pullbackᵉ :
    coherence-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-vertical-map-map-universal-property-pullbackᵉ)
      ( htpy-horizontal-map-map-universal-property-pullbackᵉ)
  coh-htpy-cone-map-universal-property-pullbackᵉ =
    coh-htpy-coneᵉ fᵉ gᵉ
      ( cone-mapᵉ fᵉ gᵉ cᵉ (map-universal-property-pullbackᵉ fᵉ gᵉ cᵉ upᵉ c'ᵉ))
      ( c'ᵉ)
      ( htpy-cone-map-universal-property-pullbackᵉ)
```

### 3-for-2 property of pullbacks

Givenᵉ twoᵉ conesᵉ `c`ᵉ andᵉ `c'`ᵉ overᵉ aᵉ commonᵉ cospanᵉ `fᵉ : Aᵉ → Xᵉ ←ᵉ Bᵉ : g`,ᵉ andᵉ aᵉ mapᵉ
betweenᵉ themᵉ `h`ᵉ suchᵉ thatᵉ theᵉ diagramᵉ

```text
              hᵉ
          Cᵉ ---->ᵉ C'ᵉ
        /ᵉ   \ᵉ   /ᵉ   \ᵉ
      /ᵉ      /ᵉ \ᵉ      \ᵉ
    /ᵉ   /ᵉ          \ᵉ    \ᵉ
   ∨ᵉ ∨ᵉ                 ∨ᵉ ∨ᵉ
  Aᵉ -------->ᵉ Xᵉ <--------ᵉ Bᵉ
        fᵉ           gᵉ
```

isᵉ coherent,ᵉ thenᵉ ifᵉ twoᵉ outᵉ ofᵉ theᵉ threeᵉ conditionsᵉ

-ᵉ `c`ᵉ isᵉ aᵉ pullbackᵉ coneᵉ
-ᵉ `c'`ᵉ isᵉ aᵉ pullbackᵉ coneᵉ
-ᵉ `h`ᵉ isᵉ anᵉ equivalenceᵉ

hold,ᵉ thenᵉ soᵉ doesᵉ theᵉ third.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ} {C'ᵉ : UUᵉ l5ᵉ}
  {fᵉ : Aᵉ → Xᵉ} {gᵉ : Bᵉ → Xᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ)
  (hᵉ : C'ᵉ → Cᵉ) (KLMᵉ : htpy-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ cᵉ hᵉ) c'ᵉ)
  where

  inv-triangle-cone-coneᵉ :
    {l6ᵉ : Level} (Dᵉ : UUᵉ l6ᵉ) →
    cone-mapᵉ fᵉ gᵉ cᵉ ∘ᵉ postcompᵉ Dᵉ hᵉ ~ᵉ cone-mapᵉ fᵉ gᵉ c'ᵉ
  inv-triangle-cone-coneᵉ Dᵉ kᵉ =
    apᵉ
      ( λ tᵉ → cone-mapᵉ fᵉ gᵉ tᵉ kᵉ)
      ( eq-htpy-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ cᵉ hᵉ) c'ᵉ KLMᵉ)

  triangle-cone-coneᵉ :
    {l6ᵉ : Level} (Dᵉ : UUᵉ l6ᵉ) → cone-mapᵉ fᵉ gᵉ c'ᵉ ~ᵉ cone-mapᵉ fᵉ gᵉ cᵉ ∘ᵉ postcompᵉ Dᵉ hᵉ
  triangle-cone-coneᵉ Dᵉ kᵉ = invᵉ (inv-triangle-cone-coneᵉ Dᵉ kᵉ)

  abstract
    is-equiv-up-pullback-up-pullbackᵉ :
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ fᵉ gᵉ c'ᵉ →
      is-equivᵉ hᵉ
    is-equiv-up-pullback-up-pullbackᵉ upᵉ up'ᵉ =
      is-equiv-is-equiv-postcompᵉ hᵉ
        ( λ Dᵉ →
          is-equiv-top-map-triangleᵉ
            ( cone-mapᵉ fᵉ gᵉ c'ᵉ)
            ( cone-mapᵉ fᵉ gᵉ cᵉ)
            ( postcompᵉ Dᵉ hᵉ)
            ( triangle-cone-coneᵉ Dᵉ)
            ( upᵉ Dᵉ)
            ( up'ᵉ Dᵉ))

  abstract
    up-pullback-up-pullback-is-equivᵉ :
      is-equivᵉ hᵉ →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      universal-property-pullbackᵉ fᵉ gᵉ c'ᵉ
    up-pullback-up-pullback-is-equivᵉ is-equiv-hᵉ upᵉ Dᵉ =
      is-equiv-left-map-triangleᵉ
        ( cone-mapᵉ fᵉ gᵉ c'ᵉ)
        ( cone-mapᵉ fᵉ gᵉ cᵉ)
        ( postcompᵉ Dᵉ hᵉ)
        ( triangle-cone-coneᵉ Dᵉ)
        ( is-equiv-postcomp-is-equivᵉ hᵉ is-equiv-hᵉ Dᵉ)
        ( upᵉ Dᵉ)

  abstract
    up-pullback-is-equiv-up-pullbackᵉ :
      universal-property-pullbackᵉ fᵉ gᵉ c'ᵉ →
      is-equivᵉ hᵉ →
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ
    up-pullback-is-equiv-up-pullbackᵉ up'ᵉ is-equiv-hᵉ Dᵉ =
      is-equiv-right-map-triangleᵉ
        ( cone-mapᵉ fᵉ gᵉ c'ᵉ)
        ( cone-mapᵉ fᵉ gᵉ cᵉ)
        ( postcompᵉ Dᵉ hᵉ)
        ( triangle-cone-coneᵉ Dᵉ)
        ( up'ᵉ Dᵉ)
        ( is-equiv-postcomp-is-equivᵉ hᵉ is-equiv-hᵉ Dᵉ)
```

### Uniqueness of maps obtained via the universal property of pullbacks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) {Cᵉ : UUᵉ l4ᵉ} (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  abstract
    uniqueness-universal-property-pullbackᵉ :
      universal-property-pullbackᵉ fᵉ gᵉ cᵉ →
      {l5ᵉ : Level} (C'ᵉ : UUᵉ l5ᵉ) (c'ᵉ : coneᵉ fᵉ gᵉ C'ᵉ) →
      is-contrᵉ (Σᵉ (C'ᵉ → Cᵉ) (λ hᵉ → htpy-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ cᵉ hᵉ) c'ᵉ))
    uniqueness-universal-property-pullbackᵉ upᵉ C'ᵉ c'ᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (C'ᵉ → Cᵉ) (λ hᵉ → cone-mapᵉ fᵉ gᵉ cᵉ hᵉ ＝ᵉ c'ᵉ))
        ( equiv-totᵉ (λ hᵉ → extensionality-coneᵉ fᵉ gᵉ (cone-mapᵉ fᵉ gᵉ cᵉ hᵉ) c'ᵉ))
        ( is-contr-map-is-equivᵉ (upᵉ C'ᵉ) c'ᵉ)
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}