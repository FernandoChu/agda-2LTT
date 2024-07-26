# Fiber inclusions

```agda
module foundation.fiber-inclusionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.1-typesᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ `B`ᵉ ofᵉ typesᵉ overᵉ `A`ᵉ andᵉ anᵉ elementᵉ `aᵉ : A`,ᵉ thenᵉ **theᵉ fiberᵉ
inclusion**ᵉ ofᵉ `B`ᵉ atᵉ `a`ᵉ isᵉ aᵉ mapᵉ `Bᵉ aᵉ → Σᵉ Aᵉ B`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  fiber-inclusionᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Σᵉ Aᵉ Bᵉ
  pr1ᵉ (fiber-inclusionᵉ xᵉ yᵉ) = xᵉ
  pr2ᵉ (fiber-inclusionᵉ xᵉ yᵉ) = yᵉ

  fiber-fiber-inclusionᵉ :
    (aᵉ : Aᵉ) (tᵉ : Σᵉ Aᵉ Bᵉ) → fiberᵉ (fiber-inclusionᵉ aᵉ) tᵉ ≃ᵉ (aᵉ ＝ᵉ pr1ᵉ tᵉ)
  fiber-fiber-inclusionᵉ aᵉ tᵉ =
    ( ( right-unit-law-Σ-is-contrᵉ
        ( λ pᵉ → is-contr-map-is-equivᵉ (is-equiv-trᵉ Bᵉ pᵉ) (pr2ᵉ tᵉ))) ∘eᵉ
      ( equiv-left-swap-Σᵉ)) ∘eᵉ
    ( equiv-totᵉ (λ bᵉ → equiv-pair-eq-Σᵉ (pairᵉ aᵉ bᵉ) tᵉ))
```

## Properties

### The fiber inclusions are truncated maps for any type family `B` if and only if `A` is truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ}
  where

  is-trunc-is-trunc-map-fiber-inclusionᵉ :
    ((Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ) → is-trunc-mapᵉ kᵉ (fiber-inclusionᵉ Bᵉ aᵉ)) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
  is-trunc-is-trunc-map-fiber-inclusionᵉ Hᵉ xᵉ yᵉ =
    is-trunc-equiv'ᵉ kᵉ
      ( fiberᵉ (fiber-inclusionᵉ Bᵉ xᵉ) (pairᵉ yᵉ raise-starᵉ))
      ( fiber-fiber-inclusionᵉ Bᵉ xᵉ (pairᵉ yᵉ raise-starᵉ))
      ( Hᵉ Bᵉ xᵉ (pairᵉ yᵉ raise-starᵉ))
    where
    Bᵉ : Aᵉ → UUᵉ l2ᵉ
    Bᵉ aᵉ = raise-unitᵉ l2ᵉ

  is-trunc-map-fiber-inclusion-is-truncᵉ :
    (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ) →
    is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-trunc-mapᵉ kᵉ (fiber-inclusionᵉ Bᵉ aᵉ)
  is-trunc-map-fiber-inclusion-is-truncᵉ Bᵉ aᵉ Hᵉ tᵉ =
    is-trunc-equivᵉ kᵉ
      ( aᵉ ＝ᵉ pr1ᵉ tᵉ)
      ( fiber-fiber-inclusionᵉ Bᵉ aᵉ tᵉ)
      ( Hᵉ aᵉ (pr1ᵉ tᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-contr-map-fiber-inclusionᵉ :
    (xᵉ : Aᵉ) → is-propᵉ Aᵉ → is-contr-mapᵉ (fiber-inclusionᵉ Bᵉ xᵉ)
  is-contr-map-fiber-inclusionᵉ =
    is-trunc-map-fiber-inclusion-is-truncᵉ neg-two-𝕋ᵉ Bᵉ

  is-prop-map-fiber-inclusionᵉ :
    (xᵉ : Aᵉ) → is-setᵉ Aᵉ → is-prop-mapᵉ (fiber-inclusionᵉ Bᵉ xᵉ)
  is-prop-map-fiber-inclusionᵉ =
    is-trunc-map-fiber-inclusion-is-truncᵉ neg-one-𝕋ᵉ Bᵉ

  is-0-map-fiber-inclusionᵉ :
    (xᵉ : Aᵉ) → is-1-typeᵉ Aᵉ → is-0-mapᵉ (fiber-inclusionᵉ Bᵉ xᵉ)
  is-0-map-fiber-inclusionᵉ =
    is-trunc-map-fiber-inclusion-is-truncᵉ zero-𝕋ᵉ Bᵉ

  is-emb-fiber-inclusionᵉ : is-setᵉ Aᵉ → (xᵉ : Aᵉ) → is-embᵉ (fiber-inclusionᵉ Bᵉ xᵉ)
  is-emb-fiber-inclusionᵉ Hᵉ xᵉ =
    is-emb-is-prop-mapᵉ (is-prop-map-fiber-inclusionᵉ xᵉ Hᵉ)

  emb-fiber-inclusionᵉ : is-setᵉ Aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ ↪ᵉ Σᵉ Aᵉ Bᵉ
  pr1ᵉ (emb-fiber-inclusionᵉ Hᵉ xᵉ) = fiber-inclusionᵉ Bᵉ xᵉ
  pr2ᵉ (emb-fiber-inclusionᵉ Hᵉ xᵉ) = is-emb-fiber-inclusionᵉ Hᵉ xᵉ

  is-faithful-fiber-inclusionᵉ :
    is-1-typeᵉ Aᵉ → (xᵉ : Aᵉ) → is-faithfulᵉ (fiber-inclusionᵉ Bᵉ xᵉ)
  is-faithful-fiber-inclusionᵉ Hᵉ xᵉ =
    is-faithful-is-0-mapᵉ (is-0-map-fiber-inclusionᵉ xᵉ Hᵉ)

fiber-inclusion-embᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Setᵉ l1ᵉ) (Bᵉ : type-Setᵉ Aᵉ → UUᵉ l2ᵉ) →
  (xᵉ : type-Setᵉ Aᵉ) → Bᵉ xᵉ ↪ᵉ Σᵉ (type-Setᵉ Aᵉ) Bᵉ
pr1ᵉ (fiber-inclusion-embᵉ Aᵉ Bᵉ xᵉ) = fiber-inclusionᵉ Bᵉ xᵉ
pr2ᵉ (fiber-inclusion-embᵉ Aᵉ Bᵉ xᵉ) = is-emb-fiber-inclusionᵉ Bᵉ (is-set-type-Setᵉ Aᵉ) xᵉ

fiber-inclusion-faithful-mapᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : 1-Typeᵉ l1ᵉ) (Bᵉ : type-1-Typeᵉ Aᵉ → UUᵉ l2ᵉ) →
  (xᵉ : type-1-Typeᵉ Aᵉ) → faithful-mapᵉ (Bᵉ xᵉ) (Σᵉ (type-1-Typeᵉ Aᵉ) Bᵉ)
pr1ᵉ (fiber-inclusion-faithful-mapᵉ Aᵉ Bᵉ xᵉ) = fiber-inclusionᵉ Bᵉ xᵉ
pr2ᵉ (fiber-inclusion-faithful-mapᵉ Aᵉ Bᵉ xᵉ) =
  is-faithful-fiber-inclusionᵉ Bᵉ (is-1-type-type-1-Typeᵉ Aᵉ) xᵉ
```

### Any fiber inclusion is a pullback of a point inclusion

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  where

  cone-fiber-famᵉ : coneᵉ (pr1ᵉ {Bᵉ = Bᵉ}) (pointᵉ aᵉ) (Bᵉ aᵉ)
  pr1ᵉ cone-fiber-famᵉ = fiber-inclusionᵉ Bᵉ aᵉ
  pr1ᵉ (pr2ᵉ cone-fiber-famᵉ) = terminal-mapᵉ (Bᵉ aᵉ)
  pr2ᵉ (pr2ᵉ cone-fiber-famᵉ) = refl-htpyᵉ

  abstract
    is-pullback-cone-fiber-famᵉ :
      is-pullbackᵉ (pr1ᵉ {Bᵉ = Bᵉ}) (pointᵉ aᵉ) cone-fiber-famᵉ
    is-pullback-cone-fiber-famᵉ =
      is-equiv-compᵉ
        ( gapᵉ (pr1ᵉ {Bᵉ = Bᵉ}) (pointᵉ aᵉ) (cone-fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ))
        ( map-inv-fiber-pr1ᵉ Bᵉ aᵉ)
        ( is-equiv-map-inv-fiber-pr1ᵉ Bᵉ aᵉ)
        ( is-pullback-cone-fiberᵉ pr1ᵉ aᵉ)
```