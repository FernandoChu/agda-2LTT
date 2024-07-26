# `0`-Maps

```agda
module foundation.0-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

Mapsᵉ `fᵉ : Aᵉ → B`ᵉ ofᵉ whichᵉ theᵉ fibersᵉ areᵉ sets,ᵉ i.e.,ᵉ 0-truncatedᵉ types,ᵉ areᵉ
calledᵉ 0-maps.ᵉ Itᵉ isᵉ shownᵉ in
[`foundation.faithful-maps`](foundation.faithful-maps.mdᵉ) thatᵉ aᵉ mapᵉ `f`ᵉ isᵉ aᵉ
0-mapᵉ ifᵉ andᵉ onlyᵉ ifᵉ `f`ᵉ isᵉ faithful,ᵉ i.e.,ᵉ `f`ᵉ inducesᵉ embeddingsᵉ onᵉ identityᵉ
types.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  is-0-mapᵉ : {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-0-mapᵉ {Aᵉ} {Bᵉ} fᵉ = (yᵉ : Bᵉ) → is-setᵉ (fiberᵉ fᵉ yᵉ)

  0-mapᵉ : (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  0-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-0-mapᵉ

  map-0-mapᵉ : {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → 0-mapᵉ Aᵉ Bᵉ → Aᵉ → Bᵉ
  map-0-mapᵉ = pr1ᵉ

  is-0-map-map-0-mapᵉ :
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : 0-mapᵉ Aᵉ Bᵉ) → is-0-mapᵉ (map-0-mapᵉ fᵉ)
  is-0-map-map-0-mapᵉ = pr2ᵉ
```

## Properties

### Projections of families of sets are `0`-maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  abstract
    is-0-map-pr1ᵉ :
      {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → ((xᵉ : Aᵉ) → is-setᵉ (Bᵉ xᵉ)) → is-0-mapᵉ (pr1ᵉ {Bᵉ = Bᵉ})
    is-0-map-pr1ᵉ {Bᵉ} Hᵉ xᵉ =
      is-set-equivᵉ (Bᵉ xᵉ) (equiv-fiber-pr1ᵉ Bᵉ xᵉ) (Hᵉ xᵉ)

  pr1-0-mapᵉ :
    (Bᵉ : Aᵉ → Setᵉ l2ᵉ) → 0-mapᵉ (Σᵉ Aᵉ (λ xᵉ → type-Setᵉ (Bᵉ xᵉ))) Aᵉ
  pr1ᵉ (pr1-0-mapᵉ Bᵉ) = pr1ᵉ
  pr2ᵉ (pr1-0-mapᵉ Bᵉ) = is-0-map-pr1ᵉ (λ xᵉ → is-set-type-Setᵉ (Bᵉ xᵉ))
```

### `0`-maps are closed under homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  is-0-map-htpyᵉ : is-0-mapᵉ gᵉ → is-0-mapᵉ fᵉ
  is-0-map-htpyᵉ = is-trunc-map-htpyᵉ zero-𝕋ᵉ Hᵉ
```

### `0`-maps are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-0-map-compᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-0-mapᵉ gᵉ → is-0-mapᵉ hᵉ → is-0-mapᵉ (gᵉ ∘ᵉ hᵉ)
  is-0-map-compᵉ = is-trunc-map-compᵉ zero-𝕋ᵉ

  is-0-map-left-map-triangleᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-0-mapᵉ gᵉ → is-0-mapᵉ hᵉ → is-0-mapᵉ fᵉ
  is-0-map-left-map-triangleᵉ = is-trunc-map-left-map-triangleᵉ zero-𝕋ᵉ
```

### If a composite is a `0`-map, then so is its right factor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  where

  is-0-map-right-factorᵉ :
    (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) →
    is-0-mapᵉ gᵉ → is-0-mapᵉ (gᵉ ∘ᵉ hᵉ) → is-0-mapᵉ hᵉ
  is-0-map-right-factorᵉ = is-trunc-map-right-factorᵉ zero-𝕋ᵉ

  is-0-map-top-map-triangleᵉ :
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : fᵉ ~ᵉ (gᵉ ∘ᵉ hᵉ)) →
    is-0-mapᵉ gᵉ → is-0-mapᵉ fᵉ → is-0-mapᵉ hᵉ
  is-0-map-top-map-triangleᵉ = is-trunc-map-top-map-triangleᵉ zero-𝕋ᵉ
```

### Families of `0`-maps induce `0`-maps on total spaces

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ}
  where

  abstract
    is-0-map-totᵉ : ((xᵉ : Aᵉ) → is-0-mapᵉ (fᵉ xᵉ)) → is-0-mapᵉ (totᵉ fᵉ)
    is-0-map-totᵉ = is-trunc-map-totᵉ zero-𝕋ᵉ
```

### For any type family over the codomain, a `0`-map induces a `0`-map on total spaces

Inᵉ otherᵉ words,ᵉ `0`-mapsᵉ areᵉ stableᵉ underᵉ pullbacks.ᵉ Weᵉ willᵉ comeᵉ to thisᵉ pointᵉ
whenᵉ weᵉ introduceᵉ homotopyᵉ pullbacks.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} (Cᵉ : Bᵉ → UUᵉ l3ᵉ)
  where

  abstract
    is-0-map-map-Σ-map-baseᵉ : is-0-mapᵉ fᵉ → is-0-mapᵉ (map-Σ-map-baseᵉ fᵉ Cᵉ)
    is-0-map-map-Σ-map-baseᵉ = is-trunc-map-map-Σ-map-baseᵉ zero-𝕋ᵉ Cᵉ
```

### The functorial action of `Σ` preserves `0`-maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Dᵉ : Bᵉ → UUᵉ l4ᵉ) {fᵉ : Aᵉ → Bᵉ} {gᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ → Dᵉ (fᵉ xᵉ)}
  where

  is-0-map-map-Σᵉ :
    is-0-mapᵉ fᵉ → ((xᵉ : Aᵉ) → is-0-mapᵉ (gᵉ xᵉ)) → is-0-mapᵉ (map-Σᵉ Dᵉ fᵉ gᵉ)
  is-0-map-map-Σᵉ = is-trunc-map-map-Σᵉ zero-𝕋ᵉ Dᵉ
```