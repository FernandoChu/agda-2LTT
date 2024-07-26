# Fibers of maps

```agda
module foundation.fibers-of-mapsᵉ where

open import foundation-core.fibers-of-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.universal-property-pullbacksᵉ
```

</details>

## Properties

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  square-fiberᵉ :
    fᵉ ∘ᵉ pr1ᵉ ~ᵉ pointᵉ bᵉ ∘ᵉ terminal-mapᵉ (fiberᵉ fᵉ bᵉ)
  square-fiberᵉ = pr2ᵉ

  cone-fiberᵉ : coneᵉ fᵉ (pointᵉ bᵉ) (fiberᵉ fᵉ bᵉ)
  pr1ᵉ cone-fiberᵉ = pr1ᵉ
  pr1ᵉ (pr2ᵉ cone-fiberᵉ) = terminal-mapᵉ (fiberᵉ fᵉ bᵉ)
  pr2ᵉ (pr2ᵉ cone-fiberᵉ) = square-fiberᵉ

  abstract
    is-pullback-cone-fiberᵉ : is-pullbackᵉ fᵉ (pointᵉ bᵉ) cone-fiberᵉ
    is-pullback-cone-fiberᵉ =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ aᵉ → is-equiv-map-inv-left-unit-law-productᵉ)

  abstract
    universal-property-pullback-cone-fiberᵉ :
      universal-property-pullbackᵉ fᵉ (pointᵉ bᵉ) cone-fiberᵉ
    universal-property-pullback-cone-fiberᵉ =
      universal-property-pullback-is-pullbackᵉ fᵉ
        ( pointᵉ bᵉ)
        ( cone-fiberᵉ)
        ( is-pullback-cone-fiberᵉ)
```

### The fiber of the terminal map at any point is equivalent to its domain

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  equiv-fiber-terminal-mapᵉ :
    (uᵉ : unitᵉ) → fiberᵉ (terminal-mapᵉ Aᵉ) uᵉ ≃ᵉ Aᵉ
  equiv-fiber-terminal-mapᵉ uᵉ =
    right-unit-law-Σ-is-contrᵉ
      ( λ aᵉ → is-prop-unitᵉ (terminal-mapᵉ Aᵉ aᵉ) uᵉ)

  inv-equiv-fiber-terminal-mapᵉ :
    (uᵉ : unitᵉ) → Aᵉ ≃ᵉ fiberᵉ (terminal-mapᵉ Aᵉ) uᵉ
  inv-equiv-fiber-terminal-mapᵉ uᵉ =
    inv-equivᵉ (equiv-fiber-terminal-mapᵉ uᵉ)

  equiv-fiber-terminal-map-starᵉ :
    fiberᵉ (terminal-mapᵉ Aᵉ) starᵉ ≃ᵉ Aᵉ
  equiv-fiber-terminal-map-starᵉ = equiv-fiber-terminal-mapᵉ starᵉ

  inv-equiv-fiber-terminal-map-starᵉ :
    Aᵉ ≃ᵉ fiberᵉ (terminal-mapᵉ Aᵉ) starᵉ
  inv-equiv-fiber-terminal-map-starᵉ =
    inv-equivᵉ equiv-fiber-terminal-map-starᵉ
```

### The total space of the fibers of the terminal map is equivalent to its domain

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  equiv-total-fiber-terminal-mapᵉ :
    Σᵉ unitᵉ (fiberᵉ (terminal-mapᵉ Aᵉ)) ≃ᵉ Aᵉ
  equiv-total-fiber-terminal-mapᵉ =
    ( left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ) ∘eᵉ
    ( equiv-totᵉ equiv-fiber-terminal-mapᵉ)

  inv-equiv-total-fiber-terminal-mapᵉ :
    Aᵉ ≃ᵉ Σᵉ unitᵉ (fiberᵉ (terminal-mapᵉ Aᵉ))
  inv-equiv-total-fiber-terminal-mapᵉ =
    inv-equivᵉ equiv-total-fiber-terminal-mapᵉ
```

### Transport in fibers

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  compute-tr-fiberᵉ :
    {yᵉ y'ᵉ : Bᵉ} (pᵉ : yᵉ ＝ᵉ y'ᵉ) (uᵉ : fiberᵉ fᵉ yᵉ) →
    totᵉ (λ xᵉ → concat'ᵉ _ pᵉ) uᵉ ＝ᵉ trᵉ (fiberᵉ fᵉ) pᵉ uᵉ
  compute-tr-fiberᵉ reflᵉ uᵉ = apᵉ (pairᵉ _) right-unitᵉ
```

## Table of files about fibers of maps

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ fibersᵉ ofᵉ mapsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/fibers-of-maps.mdᵉ}}