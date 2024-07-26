# Fibers of maps

```agda
module foundation-core.fibers-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Givenᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ anᵉ elementᵉ `bᵉ : B`,ᵉ theᵉ **fiber**ᵉ ofᵉ `f`ᵉ atᵉ `b`ᵉ isᵉ
theᵉ preimageᵉ ofᵉ `f`ᵉ atᵉ `b`.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ consistsᵉ ofᵉ theᵉ elementsᵉ `aᵉ : A`ᵉ
equippedᵉ with anᵉ [identification](foundation-core.identity-types.mdᵉ) `fᵉ aᵉ ＝ᵉ b`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  fiberᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  fiberᵉ = Σᵉ Aᵉ (λ xᵉ → fᵉ xᵉ ＝ᵉ bᵉ)

  fiber'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  fiber'ᵉ = Σᵉ Aᵉ (λ xᵉ → bᵉ ＝ᵉ fᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {bᵉ : Bᵉ}
  where

  inclusion-fiberᵉ : fiberᵉ fᵉ bᵉ → Aᵉ
  inclusion-fiberᵉ = pr1ᵉ

  compute-value-inclusion-fiberᵉ : (yᵉ : fiberᵉ fᵉ bᵉ) → fᵉ (inclusion-fiberᵉ yᵉ) ＝ᵉ bᵉ
  compute-value-inclusion-fiberᵉ = pr2ᵉ
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fiber`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  Eq-fiberᵉ : fiberᵉ fᵉ bᵉ → fiberᵉ fᵉ bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-fiberᵉ sᵉ tᵉ = Σᵉ (pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) (λ αᵉ → apᵉ fᵉ αᵉ ∙ᵉ pr2ᵉ tᵉ ＝ᵉ pr2ᵉ sᵉ)

  refl-Eq-fiberᵉ : (sᵉ : fiberᵉ fᵉ bᵉ) → Eq-fiberᵉ sᵉ sᵉ
  pr1ᵉ (refl-Eq-fiberᵉ sᵉ) = reflᵉ
  pr2ᵉ (refl-Eq-fiberᵉ sᵉ) = reflᵉ

  Eq-eq-fiberᵉ : {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → sᵉ ＝ᵉ tᵉ → Eq-fiberᵉ sᵉ tᵉ
  Eq-eq-fiberᵉ {sᵉ} reflᵉ = refl-Eq-fiberᵉ sᵉ

  eq-Eq-fiber-uncurryᵉ : {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → Eq-fiberᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-fiber-uncurryᵉ (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  eq-Eq-fiberᵉ :
    {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} (αᵉ : pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) → apᵉ fᵉ αᵉ ∙ᵉ pr2ᵉ tᵉ ＝ᵉ pr2ᵉ sᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-fiberᵉ αᵉ βᵉ = eq-Eq-fiber-uncurryᵉ (αᵉ ,ᵉ βᵉ)

  is-section-eq-Eq-fiberᵉ :
    {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} →
    is-sectionᵉ (Eq-eq-fiberᵉ {sᵉ} {tᵉ}) (eq-Eq-fiber-uncurryᵉ {sᵉ} {tᵉ})
  is-section-eq-Eq-fiberᵉ (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retraction-eq-Eq-fiberᵉ :
    {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} →
    is-retractionᵉ (Eq-eq-fiberᵉ {sᵉ} {tᵉ}) (eq-Eq-fiber-uncurryᵉ {sᵉ} {tᵉ})
  is-retraction-eq-Eq-fiberᵉ reflᵉ = reflᵉ

  abstract
    is-equiv-Eq-eq-fiberᵉ : {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → is-equivᵉ (Eq-eq-fiberᵉ {sᵉ} {tᵉ})
    is-equiv-Eq-eq-fiberᵉ =
      is-equiv-is-invertibleᵉ
        eq-Eq-fiber-uncurryᵉ
        is-section-eq-Eq-fiberᵉ
        is-retraction-eq-Eq-fiberᵉ

  equiv-Eq-eq-fiberᵉ : {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-fiberᵉ sᵉ tᵉ
  pr1ᵉ equiv-Eq-eq-fiberᵉ = Eq-eq-fiberᵉ
  pr2ᵉ equiv-Eq-eq-fiberᵉ = is-equiv-Eq-eq-fiberᵉ

  abstract
    is-equiv-eq-Eq-fiberᵉ :
      {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → is-equivᵉ (eq-Eq-fiber-uncurryᵉ {sᵉ} {tᵉ})
    is-equiv-eq-Eq-fiberᵉ =
      is-equiv-is-invertibleᵉ
        Eq-eq-fiberᵉ
        is-retraction-eq-Eq-fiberᵉ
        is-section-eq-Eq-fiberᵉ

  equiv-eq-Eq-fiberᵉ : {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} → Eq-fiberᵉ sᵉ tᵉ ≃ᵉ (sᵉ ＝ᵉ tᵉ)
  pr1ᵉ equiv-eq-Eq-fiberᵉ = eq-Eq-fiber-uncurryᵉ
  pr2ᵉ equiv-eq-Eq-fiberᵉ = is-equiv-eq-Eq-fiberᵉ

  compute-ap-inclusion-fiber-eq-Eq-fiberᵉ :
    {sᵉ tᵉ : fiberᵉ fᵉ bᵉ} (αᵉ : pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) (βᵉ : apᵉ fᵉ αᵉ ∙ᵉ pr2ᵉ tᵉ ＝ᵉ pr2ᵉ sᵉ) →
    apᵉ (inclusion-fiberᵉ fᵉ) (eq-Eq-fiberᵉ αᵉ βᵉ) ＝ᵉ αᵉ
  compute-ap-inclusion-fiber-eq-Eq-fiberᵉ reflᵉ reflᵉ = reflᵉ
```

#### The case of `fiber'`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  Eq-fiber'ᵉ : fiber'ᵉ fᵉ bᵉ → fiber'ᵉ fᵉ bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-fiber'ᵉ sᵉ tᵉ = Σᵉ (pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) (λ αᵉ → pr2ᵉ tᵉ ＝ᵉ pr2ᵉ sᵉ ∙ᵉ apᵉ fᵉ αᵉ)

  refl-Eq-fiber'ᵉ : (sᵉ : fiber'ᵉ fᵉ bᵉ) → Eq-fiber'ᵉ sᵉ sᵉ
  pr1ᵉ (refl-Eq-fiber'ᵉ sᵉ) = reflᵉ
  pr2ᵉ (refl-Eq-fiber'ᵉ sᵉ) = invᵉ right-unitᵉ

  Eq-eq-fiber'ᵉ : {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → sᵉ ＝ᵉ tᵉ → Eq-fiber'ᵉ sᵉ tᵉ
  Eq-eq-fiber'ᵉ {sᵉ} reflᵉ = refl-Eq-fiber'ᵉ sᵉ

  eq-Eq-fiber-uncurry'ᵉ : {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → Eq-fiber'ᵉ sᵉ tᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-fiber-uncurry'ᵉ {xᵉ ,ᵉ pᵉ} (reflᵉ ,ᵉ reflᵉ) =
    apᵉ (pairᵉ _) (invᵉ right-unitᵉ)

  eq-Eq-fiber'ᵉ :
    {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} (αᵉ : pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) → pr2ᵉ tᵉ ＝ᵉ pr2ᵉ sᵉ ∙ᵉ apᵉ fᵉ αᵉ → sᵉ ＝ᵉ tᵉ
  eq-Eq-fiber'ᵉ αᵉ βᵉ = eq-Eq-fiber-uncurry'ᵉ (αᵉ ,ᵉ βᵉ)

  is-section-eq-Eq-fiber'ᵉ :
    {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} →
    is-sectionᵉ (Eq-eq-fiber'ᵉ {sᵉ} {tᵉ}) (eq-Eq-fiber-uncurry'ᵉ {sᵉ} {tᵉ})
  is-section-eq-Eq-fiber'ᵉ {xᵉ ,ᵉ reflᵉ} (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retraction-eq-Eq-fiber'ᵉ :
    {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} →
    is-retractionᵉ (Eq-eq-fiber'ᵉ {sᵉ} {tᵉ}) (eq-Eq-fiber-uncurry'ᵉ {sᵉ} {tᵉ})
  is-retraction-eq-Eq-fiber'ᵉ {xᵉ ,ᵉ reflᵉ} reflᵉ = reflᵉ

  abstract
    is-equiv-Eq-eq-fiber'ᵉ :
      {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → is-equivᵉ (Eq-eq-fiber'ᵉ {sᵉ} {tᵉ})
    is-equiv-Eq-eq-fiber'ᵉ =
      is-equiv-is-invertibleᵉ
        eq-Eq-fiber-uncurry'ᵉ
        is-section-eq-Eq-fiber'ᵉ
        is-retraction-eq-Eq-fiber'ᵉ

  equiv-Eq-eq-fiber'ᵉ : {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → (sᵉ ＝ᵉ tᵉ) ≃ᵉ Eq-fiber'ᵉ sᵉ tᵉ
  pr1ᵉ equiv-Eq-eq-fiber'ᵉ = Eq-eq-fiber'ᵉ
  pr2ᵉ equiv-Eq-eq-fiber'ᵉ = is-equiv-Eq-eq-fiber'ᵉ

  abstract
    is-equiv-eq-Eq-fiber'ᵉ :
      {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → is-equivᵉ (eq-Eq-fiber-uncurry'ᵉ {sᵉ} {tᵉ})
    is-equiv-eq-Eq-fiber'ᵉ =
      is-equiv-is-invertibleᵉ
        Eq-eq-fiber'ᵉ
        is-retraction-eq-Eq-fiber'ᵉ
        is-section-eq-Eq-fiber'ᵉ

  equiv-eq-Eq-fiber'ᵉ : {sᵉ tᵉ : fiber'ᵉ fᵉ bᵉ} → Eq-fiber'ᵉ sᵉ tᵉ ≃ᵉ (sᵉ ＝ᵉ tᵉ)
  pr1ᵉ equiv-eq-Eq-fiber'ᵉ = eq-Eq-fiber-uncurry'ᵉ
  pr2ᵉ equiv-eq-Eq-fiber'ᵉ = is-equiv-eq-Eq-fiber'ᵉ
```

### `fiber f y` and `fiber' f y` are equivalent

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (yᵉ : Bᵉ)
  where

  map-equiv-fiberᵉ : fiberᵉ fᵉ yᵉ → fiber'ᵉ fᵉ yᵉ
  pr1ᵉ (map-equiv-fiberᵉ (xᵉ ,ᵉ _)) = xᵉ
  pr2ᵉ (map-equiv-fiberᵉ (xᵉ ,ᵉ pᵉ)) = invᵉ pᵉ

  map-inv-equiv-fiberᵉ : fiber'ᵉ fᵉ yᵉ → fiberᵉ fᵉ yᵉ
  pr1ᵉ (map-inv-equiv-fiberᵉ (xᵉ ,ᵉ _)) = xᵉ
  pr2ᵉ (map-inv-equiv-fiberᵉ (xᵉ ,ᵉ pᵉ)) = invᵉ pᵉ

  is-section-map-inv-equiv-fiberᵉ :
    is-sectionᵉ map-equiv-fiberᵉ map-inv-equiv-fiberᵉ
  is-section-map-inv-equiv-fiberᵉ (xᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retraction-map-inv-equiv-fiberᵉ :
    is-retractionᵉ map-equiv-fiberᵉ map-inv-equiv-fiberᵉ
  is-retraction-map-inv-equiv-fiberᵉ (xᵉ ,ᵉ reflᵉ) = reflᵉ

  is-equiv-map-equiv-fiberᵉ : is-equivᵉ map-equiv-fiberᵉ
  is-equiv-map-equiv-fiberᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-fiberᵉ
      is-section-map-inv-equiv-fiberᵉ
      is-retraction-map-inv-equiv-fiberᵉ

  equiv-fiberᵉ : fiberᵉ fᵉ yᵉ ≃ᵉ fiber'ᵉ fᵉ yᵉ
  pr1ᵉ equiv-fiberᵉ = map-equiv-fiberᵉ
  pr2ᵉ equiv-fiberᵉ = is-equiv-map-equiv-fiberᵉ
```

### Computing the fibers of a projection map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  where

  map-fiber-pr1ᵉ : fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ → Bᵉ aᵉ
  map-fiber-pr1ᵉ ((xᵉ ,ᵉ yᵉ) ,ᵉ pᵉ) = trᵉ Bᵉ pᵉ yᵉ

  map-inv-fiber-pr1ᵉ : Bᵉ aᵉ → fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ
  pr1ᵉ (pr1ᵉ (map-inv-fiber-pr1ᵉ bᵉ)) = aᵉ
  pr2ᵉ (pr1ᵉ (map-inv-fiber-pr1ᵉ bᵉ)) = bᵉ
  pr2ᵉ (map-inv-fiber-pr1ᵉ bᵉ) = reflᵉ

  is-section-map-inv-fiber-pr1ᵉ :
    is-sectionᵉ map-fiber-pr1ᵉ map-inv-fiber-pr1ᵉ
  is-section-map-inv-fiber-pr1ᵉ bᵉ = reflᵉ

  is-retraction-map-inv-fiber-pr1ᵉ :
    is-retractionᵉ map-fiber-pr1ᵉ map-inv-fiber-pr1ᵉ
  is-retraction-map-inv-fiber-pr1ᵉ ((.aᵉ ,ᵉ yᵉ) ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-map-fiber-pr1ᵉ : is-equivᵉ map-fiber-pr1ᵉ
    is-equiv-map-fiber-pr1ᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-fiber-pr1ᵉ
        is-section-map-inv-fiber-pr1ᵉ
        is-retraction-map-inv-fiber-pr1ᵉ

  equiv-fiber-pr1ᵉ : fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ ≃ᵉ Bᵉ aᵉ
  pr1ᵉ equiv-fiber-pr1ᵉ = map-fiber-pr1ᵉ
  pr2ᵉ equiv-fiber-pr1ᵉ = is-equiv-map-fiber-pr1ᵉ

  abstract
    is-equiv-map-inv-fiber-pr1ᵉ : is-equivᵉ map-inv-fiber-pr1ᵉ
    is-equiv-map-inv-fiber-pr1ᵉ =
      is-equiv-is-invertibleᵉ
        map-fiber-pr1ᵉ
        is-retraction-map-inv-fiber-pr1ᵉ
        is-section-map-inv-fiber-pr1ᵉ

  inv-equiv-fiber-pr1ᵉ : Bᵉ aᵉ ≃ᵉ fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ
  pr1ᵉ inv-equiv-fiber-pr1ᵉ = map-inv-fiber-pr1ᵉ
  pr2ᵉ inv-equiv-fiber-pr1ᵉ = is-equiv-map-inv-fiber-pr1ᵉ
```

### The total space of fibers

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  map-equiv-total-fiberᵉ : Σᵉ Bᵉ (fiberᵉ fᵉ) → Aᵉ
  map-equiv-total-fiberᵉ tᵉ = pr1ᵉ (pr2ᵉ tᵉ)

  triangle-map-equiv-total-fiberᵉ : pr1ᵉ ~ᵉ fᵉ ∘ᵉ map-equiv-total-fiberᵉ
  triangle-map-equiv-total-fiberᵉ tᵉ = invᵉ (pr2ᵉ (pr2ᵉ tᵉ))

  map-inv-equiv-total-fiberᵉ : Aᵉ → Σᵉ Bᵉ (fiberᵉ fᵉ)
  pr1ᵉ (map-inv-equiv-total-fiberᵉ xᵉ) = fᵉ xᵉ
  pr1ᵉ (pr2ᵉ (map-inv-equiv-total-fiberᵉ xᵉ)) = xᵉ
  pr2ᵉ (pr2ᵉ (map-inv-equiv-total-fiberᵉ xᵉ)) = reflᵉ

  is-retraction-map-inv-equiv-total-fiberᵉ :
    is-retractionᵉ map-equiv-total-fiberᵉ map-inv-equiv-total-fiberᵉ
  is-retraction-map-inv-equiv-total-fiberᵉ (.(fᵉ xᵉ) ,ᵉ xᵉ ,ᵉ reflᵉ) = reflᵉ

  is-section-map-inv-equiv-total-fiberᵉ :
    is-sectionᵉ map-equiv-total-fiberᵉ map-inv-equiv-total-fiberᵉ
  is-section-map-inv-equiv-total-fiberᵉ xᵉ = reflᵉ

  abstract
    is-equiv-map-equiv-total-fiberᵉ : is-equivᵉ map-equiv-total-fiberᵉ
    is-equiv-map-equiv-total-fiberᵉ =
      is-equiv-is-invertibleᵉ
        map-inv-equiv-total-fiberᵉ
        is-section-map-inv-equiv-total-fiberᵉ
        is-retraction-map-inv-equiv-total-fiberᵉ

    is-equiv-map-inv-equiv-total-fiberᵉ : is-equivᵉ map-inv-equiv-total-fiberᵉ
    is-equiv-map-inv-equiv-total-fiberᵉ =
      is-equiv-is-invertibleᵉ
        map-equiv-total-fiberᵉ
        is-retraction-map-inv-equiv-total-fiberᵉ
        is-section-map-inv-equiv-total-fiberᵉ

  equiv-total-fiberᵉ : Σᵉ Bᵉ (fiberᵉ fᵉ) ≃ᵉ Aᵉ
  pr1ᵉ equiv-total-fiberᵉ = map-equiv-total-fiberᵉ
  pr2ᵉ equiv-total-fiberᵉ = is-equiv-map-equiv-total-fiberᵉ

  inv-equiv-total-fiberᵉ : Aᵉ ≃ᵉ Σᵉ Bᵉ (fiberᵉ fᵉ)
  pr1ᵉ inv-equiv-total-fiberᵉ = map-inv-equiv-total-fiberᵉ
  pr2ᵉ inv-equiv-total-fiberᵉ = is-equiv-map-inv-equiv-total-fiberᵉ
```

### Fibers of compositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (xᵉ : Xᵉ)
  where

  map-compute-fiber-compᵉ :
    fiberᵉ (gᵉ ∘ᵉ hᵉ) xᵉ → Σᵉ (fiberᵉ gᵉ xᵉ) (λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
  pr1ᵉ (pr1ᵉ (map-compute-fiber-compᵉ (aᵉ ,ᵉ pᵉ))) = hᵉ aᵉ
  pr2ᵉ (pr1ᵉ (map-compute-fiber-compᵉ (aᵉ ,ᵉ pᵉ))) = pᵉ
  pr1ᵉ (pr2ᵉ (map-compute-fiber-compᵉ (aᵉ ,ᵉ pᵉ))) = aᵉ
  pr2ᵉ (pr2ᵉ (map-compute-fiber-compᵉ (aᵉ ,ᵉ pᵉ))) = reflᵉ

  map-inv-compute-fiber-compᵉ :
    Σᵉ (fiberᵉ gᵉ xᵉ) (λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ)) → fiberᵉ (gᵉ ∘ᵉ hᵉ) xᵉ
  pr1ᵉ (map-inv-compute-fiber-compᵉ tᵉ) = pr1ᵉ (pr2ᵉ tᵉ)
  pr2ᵉ (map-inv-compute-fiber-compᵉ tᵉ) = apᵉ gᵉ (pr2ᵉ (pr2ᵉ tᵉ)) ∙ᵉ pr2ᵉ (pr1ᵉ tᵉ)

  is-section-map-inv-compute-fiber-compᵉ :
    is-sectionᵉ map-compute-fiber-compᵉ map-inv-compute-fiber-compᵉ
  is-section-map-inv-compute-fiber-compᵉ ((.(hᵉ aᵉ) ,ᵉ reflᵉ) ,ᵉ (aᵉ ,ᵉ reflᵉ)) = reflᵉ

  is-retraction-map-inv-compute-fiber-compᵉ :
    is-retractionᵉ map-compute-fiber-compᵉ map-inv-compute-fiber-compᵉ
  is-retraction-map-inv-compute-fiber-compᵉ (aᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-map-compute-fiber-compᵉ :
      is-equivᵉ map-compute-fiber-compᵉ
    is-equiv-map-compute-fiber-compᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-compute-fiber-compᵉ)
        ( is-section-map-inv-compute-fiber-compᵉ)
        ( is-retraction-map-inv-compute-fiber-compᵉ)

  compute-fiber-compᵉ :
    fiberᵉ (gᵉ ∘ᵉ hᵉ) xᵉ ≃ᵉ Σᵉ (fiberᵉ gᵉ xᵉ) (λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
  pr1ᵉ compute-fiber-compᵉ = map-compute-fiber-compᵉ
  pr2ᵉ compute-fiber-compᵉ = is-equiv-map-compute-fiber-compᵉ

  abstract
    is-equiv-map-inv-compute-fiber-compᵉ :
      is-equivᵉ map-inv-compute-fiber-compᵉ
    is-equiv-map-inv-compute-fiber-compᵉ =
        is-equiv-is-invertibleᵉ
          ( map-compute-fiber-compᵉ)
          ( is-retraction-map-inv-compute-fiber-compᵉ)
          ( is-section-map-inv-compute-fiber-compᵉ)

  inv-compute-fiber-compᵉ :
    Σᵉ (fiberᵉ gᵉ xᵉ) (λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ)) ≃ᵉ fiberᵉ (gᵉ ∘ᵉ hᵉ) xᵉ
  pr1ᵉ inv-compute-fiber-compᵉ = map-inv-compute-fiber-compᵉ
  pr2ᵉ inv-compute-fiber-compᵉ = is-equiv-map-inv-compute-fiber-compᵉ
```

## Table of files about fibers of maps

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ fibersᵉ ofᵉ mapsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/fibers-of-maps.mdᵉ}}