# Fibers of exo maps

```agda
module foundation.fibers-of-exo-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.exo-universes
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types

open import foundation.exo-isomorphisms
open import foundation.exo-homotopies
open import foundation.exo-retractions
open import foundation.exo-sections
```

</details>

## Idea

Given a mapᵉ `f : A → B` and an element `b : B`, the **fiber** of `f` at `b` is
the preimage of `f` at `b`. In other words, it consists of the elements `a : A`
equipped with an [identification](foundation-core.identity-types.md) `f a ＝ᵉ b`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (b : B)
  where

  fiberᵉ : UUᵉ (l1 ⊔ l2)
  fiberᵉ = Σᵉ A (λ x → f x ＝ᵉ b)

  fiberᵉ' : UUᵉ (l1 ⊔ l2)
  fiberᵉ' = Σᵉ A (λ x → b ＝ᵉ f x)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) {b : B}
  where

  inclusion-fiberᵉ : fiberᵉ f b → A
  inclusion-fiberᵉ = pr1ᵉ

  compute-value-inclusion-fiberᵉ : (y : fiberᵉ f b) → f (inclusion-fiberᵉ y) ＝ᵉ b
  compute-value-inclusion-fiberᵉ = pr2ᵉ
```

## Properties

### Characterization of the identity types of the fibers of a map

#### The case of `fiber`

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (b : B)
  where

  Eq-fiberᵉ : fiberᵉ f b → fiberᵉ f b → UUᵉ (l1 ⊔ l2)
  Eq-fiberᵉ s t = Σᵉ (pr1ᵉ s ＝ᵉ pr1ᵉ t) (λ α → apᵉ f α ∙ᵉ pr2ᵉ t ＝ᵉ pr2ᵉ s)

  reflᵉ-Eq-fiberᵉ : (s : fiberᵉ f b) → Eq-fiberᵉ s s
  pr1ᵉ (reflᵉ-Eq-fiberᵉ s) = reflᵉ
  pr2ᵉ (reflᵉ-Eq-fiberᵉ s) = reflᵉ

  Eq-eq-fiberᵉ : {s t : fiberᵉ f b} → s ＝ᵉ t → Eq-fiberᵉ s t
  Eq-eq-fiberᵉ {s} reflᵉ = reflᵉ-Eq-fiberᵉ s

  eq-Eq-fiberᵉ-uncurry : {s t : fiberᵉ f b} → Eq-fiberᵉ s t → s ＝ᵉ t
  eq-Eq-fiberᵉ-uncurry (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  eq-Eq-fiberᵉ :
    {s t : fiberᵉ f b} (α : pr1ᵉ s ＝ᵉ pr1ᵉ t) → apᵉ f α ∙ᵉ pr2ᵉ t ＝ᵉ pr2ᵉ s → s ＝ᵉ t
  eq-Eq-fiberᵉ α β = eq-Eq-fiberᵉ-uncurry (α ,ᵉ β)

  is-sectionᵉ-eq-Eq-fiberᵉ :
    {s t : fiberᵉ f b} →
    is-sectionᵉ (Eq-eq-fiberᵉ {s} {t}) (eq-Eq-fiberᵉ-uncurry {s} {t})
  is-sectionᵉ-eq-Eq-fiberᵉ (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retractionᵉ-eq-Eq-fiberᵉ :
    {s t : fiberᵉ f b} →
    is-retractionᵉ (Eq-eq-fiberᵉ {s} {t}) (eq-Eq-fiberᵉ-uncurry {s} {t})
  is-retractionᵉ-eq-Eq-fiberᵉ reflᵉ = reflᵉ

  is-exo-iso-Eq-eq-fiberᵉ : {s t : fiberᵉ f b} → is-exo-iso (Eq-eq-fiberᵉ {s} {t})
  pr1ᵉ is-exo-iso-Eq-eq-fiberᵉ = eq-Eq-fiberᵉ-uncurry
  pr1ᵉ (pr2ᵉ is-exo-iso-Eq-eq-fiberᵉ) = is-sectionᵉ-eq-Eq-fiberᵉ
  pr2ᵉ (pr2ᵉ is-exo-iso-Eq-eq-fiberᵉ) = is-retractionᵉ-eq-Eq-fiberᵉ

  exo-iso-Eq-eq-fiberᵉ : {s t : fiberᵉ f b} → (s ＝ᵉ t) ≅ᵉ Eq-fiberᵉ s t
  pr1ᵉ exo-iso-Eq-eq-fiberᵉ = Eq-eq-fiberᵉ
  pr2ᵉ exo-iso-Eq-eq-fiberᵉ = is-exo-iso-Eq-eq-fiberᵉ

  is-exo-iso-eq-Eq-fiberᵉ :
    {s t : fiberᵉ f b} → is-exo-iso (eq-Eq-fiberᵉ-uncurry {s} {t})
  pr1ᵉ is-exo-iso-eq-Eq-fiberᵉ = Eq-eq-fiberᵉ
  pr1ᵉ (pr2ᵉ is-exo-iso-eq-Eq-fiberᵉ) = is-retractionᵉ-eq-Eq-fiberᵉ
  pr2ᵉ (pr2ᵉ is-exo-iso-eq-Eq-fiberᵉ) = is-sectionᵉ-eq-Eq-fiberᵉ

  exo-iso-eq-Eq-fiberᵉ : {s t : fiberᵉ f b} → Eq-fiberᵉ s t ≅ᵉ (s ＝ᵉ t)
  pr1ᵉ exo-iso-eq-Eq-fiberᵉ = eq-Eq-fiberᵉ-uncurry
  pr2ᵉ exo-iso-eq-Eq-fiberᵉ = is-exo-iso-eq-Eq-fiberᵉ

  compute-ap-inclusion-fiberᵉ-eq-Eq-fiberᵉ :
    {s t : fiberᵉ f b} (α : pr1ᵉ s ＝ᵉ pr1ᵉ t) (β : apᵉ f α ∙ᵉ pr2ᵉ t ＝ᵉ pr2ᵉ s) →
    apᵉ (inclusion-fiberᵉ f) (eq-Eq-fiberᵉ α β) ＝ᵉ α
  compute-ap-inclusion-fiberᵉ-eq-Eq-fiberᵉ reflᵉ reflᵉ = reflᵉ
```

#### The case of `fiberᵉ'`

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (b : B)
  where

  Eq-fiberᵉ' : fiberᵉ' f b → fiberᵉ' f b → UUᵉ (l1 ⊔ l2)
  Eq-fiberᵉ' s t = Σᵉ (pr1ᵉ s ＝ᵉ pr1ᵉ t) (λ α → pr2ᵉ t ＝ᵉ pr2ᵉ s ∙ᵉ apᵉ f α)

  reflᵉ-Eq-fiberᵉ' : (s : fiberᵉ' f b) → Eq-fiberᵉ' s s
  pr1ᵉ (reflᵉ-Eq-fiberᵉ' s) = reflᵉ
  pr2ᵉ (reflᵉ-Eq-fiberᵉ' s) = invᵉ right-unitᵉ

  Eq-eq-fiberᵉ' : {s t : fiberᵉ' f b} → s ＝ᵉ t → Eq-fiberᵉ' s t
  Eq-eq-fiberᵉ' {s} reflᵉ = reflᵉ-Eq-fiberᵉ' s

  eq-Eq-fiberᵉ-uncurry' : {s t : fiberᵉ' f b} → Eq-fiberᵉ' s t → s ＝ᵉ t
  eq-Eq-fiberᵉ-uncurry' {x ,ᵉ p} (reflᵉ ,ᵉ reflᵉ) =
    apᵉ (pairᵉ _) (invᵉ right-unitᵉ)

  eq-Eq-fiberᵉ' :
    {s t : fiberᵉ' f b} (α : pr1ᵉ s ＝ᵉ pr1ᵉ t) → pr2ᵉ t ＝ᵉ pr2ᵉ s ∙ᵉ apᵉ f α → s ＝ᵉ t
  eq-Eq-fiberᵉ' α β = eq-Eq-fiberᵉ-uncurry' (α ,ᵉ β)

  is-sectionᵉ-eq-Eq-fiberᵉ' :
    {s t : fiberᵉ' f b} →
    is-sectionᵉ (Eq-eq-fiberᵉ' {s} {t}) (eq-Eq-fiberᵉ-uncurry' {s} {t})
  is-sectionᵉ-eq-Eq-fiberᵉ' {x ,ᵉ reflᵉ} (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retractionᵉ-eq-Eq-fiberᵉ' :
    {s t : fiberᵉ' f b} →
    is-retractionᵉ (Eq-eq-fiberᵉ' {s} {t}) (eq-Eq-fiberᵉ-uncurry' {s} {t})
  is-retractionᵉ-eq-Eq-fiberᵉ' {x ,ᵉ reflᵉ} reflᵉ = reflᵉ

  is-exo-iso-Eq-eq-fiberᵉ' :
    {s t : fiberᵉ' f b} → is-exo-iso (Eq-eq-fiberᵉ' {s} {t})
  pr1ᵉ is-exo-iso-Eq-eq-fiberᵉ' = eq-Eq-fiberᵉ-uncurry'
  pr1ᵉ (pr2ᵉ is-exo-iso-Eq-eq-fiberᵉ') = is-sectionᵉ-eq-Eq-fiberᵉ'
  pr2ᵉ (pr2ᵉ is-exo-iso-Eq-eq-fiberᵉ') = is-retractionᵉ-eq-Eq-fiberᵉ'

  exo-iso-Eq-eq-fiberᵉ' : {s t : fiberᵉ' f b} → (s ＝ᵉ t) ≅ᵉ Eq-fiberᵉ' s t
  pr1ᵉ exo-iso-Eq-eq-fiberᵉ' = Eq-eq-fiberᵉ'
  pr2ᵉ exo-iso-Eq-eq-fiberᵉ' = is-exo-iso-Eq-eq-fiberᵉ'

  is-exo-iso-eq-Eq-fiberᵉ' :
    {s t : fiberᵉ' f b} → is-exo-iso (eq-Eq-fiberᵉ-uncurry' {s} {t})
  pr1ᵉ is-exo-iso-eq-Eq-fiberᵉ' = Eq-eq-fiberᵉ'
  pr1ᵉ (pr2ᵉ is-exo-iso-eq-Eq-fiberᵉ') = is-retractionᵉ-eq-Eq-fiberᵉ'
  pr2ᵉ (pr2ᵉ is-exo-iso-eq-Eq-fiberᵉ') = is-sectionᵉ-eq-Eq-fiberᵉ'

  exo-iso-eq-Eq-fiberᵉ' : {s t : fiberᵉ' f b} → Eq-fiberᵉ' s t ≅ᵉ (s ＝ᵉ t)
  pr1ᵉ exo-iso-eq-Eq-fiberᵉ' = eq-Eq-fiberᵉ-uncurry'
  pr2ᵉ exo-iso-eq-Eq-fiberᵉ' = is-exo-iso-eq-Eq-fiberᵉ'
```

### `fiberᵉ f y` and `fiberᵉ' f y` are isomorphic

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (y : B)
  where

  map-exo-iso-fiberᵉ : fiberᵉ f y → fiberᵉ' f y
  pr1ᵉ (map-exo-iso-fiberᵉ (x ,ᵉ _)) = x
  pr2ᵉ (map-exo-iso-fiberᵉ (x ,ᵉ p)) = invᵉ p

  map-inv-exo-iso-fiberᵉ : fiberᵉ' f y → fiberᵉ f y
  pr1ᵉ (map-inv-exo-iso-fiberᵉ (x ,ᵉ _)) = x
  pr2ᵉ (map-inv-exo-iso-fiberᵉ (x ,ᵉ p)) = invᵉ p

  is-sectionᵉ-map-inv-exo-iso-fiberᵉ :
    is-sectionᵉ map-exo-iso-fiberᵉ map-inv-exo-iso-fiberᵉ
  is-sectionᵉ-map-inv-exo-iso-fiberᵉ (x ,ᵉ reflᵉ) = reflᵉ

  is-retractionᵉ-map-inv-exo-iso-fiberᵉ :
    is-retractionᵉ map-exo-iso-fiberᵉ map-inv-exo-iso-fiberᵉ
  is-retractionᵉ-map-inv-exo-iso-fiberᵉ (x ,ᵉ reflᵉ) = reflᵉ

  is-exo-iso-map-exo-iso-fiberᵉ : is-exo-iso map-exo-iso-fiberᵉ
  pr1ᵉ is-exo-iso-map-exo-iso-fiberᵉ = map-inv-exo-iso-fiberᵉ
  pr1ᵉ (pr2ᵉ is-exo-iso-map-exo-iso-fiberᵉ) = is-sectionᵉ-map-inv-exo-iso-fiberᵉ
  pr2ᵉ (pr2ᵉ is-exo-iso-map-exo-iso-fiberᵉ) = is-retractionᵉ-map-inv-exo-iso-fiberᵉ

  exo-iso-fiberᵉ : fiberᵉ f y ≅ᵉ fiberᵉ' f y
  pr1ᵉ exo-iso-fiberᵉ = map-exo-iso-fiberᵉ
  pr2ᵉ exo-iso-fiberᵉ = is-exo-iso-map-exo-iso-fiberᵉ
```

-- ### Computing the fibers of a projection map

-- ```agda
-- module \_
-- {l1 l2 : Level} {A : UUᵉ l1} (B : A → UUᵉ l2) (a : A)
-- where

-- map-fiberᵉ-pr1ᵉ : fiberᵉ (pr1ᵉ {B = B}) a → B a
-- map-fiberᵉ-pr1ᵉ ((x ,ᵉ y) ,ᵉ p) = tr B p y

-- map-inv-fiberᵉ-pr1ᵉ : B a → fiberᵉ (pr1ᵉ {B = B}) a
-- pr1ᵉ (pr1ᵉ (map-inv-fiberᵉ-pr1ᵉ b)) = a
-- pr2ᵉ (pr1ᵉ (map-inv-fiberᵉ-pr1ᵉ b)) = b
-- pr2ᵉ (map-inv-fiberᵉ-pr1ᵉ b) = reflᵉ

-- is-sectionᵉ-map-inv-fiberᵉ-pr1ᵉ :
-- is-section map-fiberᵉ-pr1ᵉ map-inv-fiberᵉ-pr1ᵉ
-- is-sectionᵉ-map-inv-fiberᵉ-pr1ᵉ b = reflᵉ

-- is-retractionᵉ-map-inv-fiberᵉ-pr1ᵉ :
-- is-retraction map-fiberᵉ-pr1ᵉ map-inv-fiberᵉ-pr1ᵉ
-- is-retractionᵉ-map-inv-fiberᵉ-pr1ᵉ ((.a ,ᵉ y) ,ᵉ reflᵉ) = reflᵉ

-- abstract
-- is-equiv-map-fiberᵉ-pr1ᵉ : is-equiv map-fiberᵉ-pr1ᵉ
-- is-equiv-map-fiberᵉ-pr1ᵉ =
-- is-equiv-is-invertible
-- map-inv-fiberᵉ-pr1ᵉ
-- is-sectionᵉ-map-inv-fiberᵉ-pr1ᵉ
-- is-retractionᵉ-map-inv-fiberᵉ-pr1ᵉ

-- equiv-fiberᵉ-pr1ᵉ : fiberᵉ (pr1ᵉ {B = B}) a ≃ B a
-- pr1ᵉ equiv-fiberᵉ-pr1ᵉ = map-fiberᵉ-pr1ᵉ
-- pr2ᵉ equiv-fiberᵉ-pr1ᵉ = is-equiv-map-fiberᵉ-pr1ᵉ

-- abstract
-- is-equiv-map-inv-fiberᵉ-pr1ᵉ : is-equiv map-inv-fiberᵉ-pr1ᵉ
-- is-equiv-map-inv-fiberᵉ-pr1ᵉ =
-- is-equiv-is-invertible
-- map-fiberᵉ-pr1ᵉ
-- is-retractionᵉ-map-inv-fiberᵉ-pr1ᵉ
-- is-sectionᵉ-map-inv-fiberᵉ-pr1ᵉ

-- inv-equiv-fiberᵉ-pr1ᵉ : B a ≃ fiberᵉ (pr1ᵉ {B = B}) a
-- pr1ᵉ inv-equiv-fiberᵉ-pr1ᵉ = map-inv-fiberᵉ-pr1ᵉ
-- pr2ᵉ inv-equiv-fiberᵉ-pr1ᵉ = is-equiv-map-inv-fiberᵉ-pr1ᵉ
-- ```

-- ### The total space of fibers

-- ```agda
-- module \_
-- {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
-- where

-- map-equiv-total-fiberᵉ : Σᵉ B (fiberᵉ f) → A
-- map-equiv-total-fiberᵉ t = pr1ᵉ (pr2ᵉ t)

-- triangle-map-equiv-total-fiberᵉ : pr1ᵉ ~ f ∘ map-equiv-total-fiberᵉ
-- triangle-map-equiv-total-fiberᵉ t = invᵉ (pr2ᵉ (pr2ᵉ t))

-- map-inv-equiv-total-fiberᵉ : A → Σᵉ B (fiberᵉ f)
-- pr1ᵉ (map-inv-equiv-total-fiberᵉ x) = f x
-- pr1ᵉ (pr2ᵉ (map-inv-equiv-total-fiberᵉ x)) = x
-- pr2ᵉ (pr2ᵉ (map-inv-equiv-total-fiberᵉ x)) = reflᵉ

-- is-retractionᵉ-map-inv-equiv-total-fiberᵉ :
-- is-retraction map-equiv-total-fiberᵉ map-inv-equiv-total-fiberᵉ
-- is-retractionᵉ-map-inv-equiv-total-fiberᵉ (.(f x) ,ᵉ x ,ᵉ reflᵉ) = reflᵉ

-- is-sectionᵉ-map-inv-equiv-total-fiberᵉ :
-- is-section map-equiv-total-fiberᵉ map-inv-equiv-total-fiberᵉ
-- is-sectionᵉ-map-inv-equiv-total-fiberᵉ x = reflᵉ

-- abstract
-- is-equiv-map-equiv-total-fiberᵉ : is-equiv map-equiv-total-fiberᵉ
-- is-equiv-map-equiv-total-fiberᵉ =
-- is-equiv-is-invertible
-- map-inv-equiv-total-fiberᵉ
-- is-sectionᵉ-map-inv-equiv-total-fiberᵉ
-- is-retractionᵉ-map-inv-equiv-total-fiberᵉ

-- is-equiv-map-inv-equiv-total-fiberᵉ : is-equiv map-inv-equiv-total-fiberᵉ
-- is-equiv-map-inv-equiv-total-fiberᵉ =
-- is-equiv-is-invertible
-- map-equiv-total-fiberᵉ
-- is-retractionᵉ-map-inv-equiv-total-fiberᵉ
-- is-sectionᵉ-map-inv-equiv-total-fiberᵉ

-- equiv-total-fiberᵉ : Σᵉ B (fiberᵉ f) ≃ A
-- pr1ᵉ equiv-total-fiberᵉ = map-equiv-total-fiberᵉ
-- pr2ᵉ equiv-total-fiberᵉ = is-equiv-map-equiv-total-fiberᵉ

-- inv-equiv-total-fiberᵉ : A ≃ Σᵉ B (fiberᵉ f)
-- pr1ᵉ inv-equiv-total-fiberᵉ = map-inv-equiv-total-fiberᵉ
-- pr2ᵉ inv-equiv-total-fiberᵉ = is-equiv-map-inv-equiv-total-fiberᵉ
-- ```

-- ### Fibers of compositions

-- ```agda
-- module \_
-- {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
-- (g : B → X) (h : A → B) (x : X)
-- where

-- map-compute-fiberᵉ-comp :
-- fiberᵉ (g ∘ h) x → Σᵉ (fiberᵉ g x) (λ t → fiberᵉ h (pr1ᵉ t))
-- pr1ᵉ (pr1ᵉ (map-compute-fiberᵉ-comp (a ,ᵉ p))) = h a
-- pr2ᵉ (pr1ᵉ (map-compute-fiberᵉ-comp (a ,ᵉ p))) = p
-- pr1ᵉ (pr2ᵉ (map-compute-fiberᵉ-comp (a ,ᵉ p))) = a
-- pr2ᵉ (pr2ᵉ (map-compute-fiberᵉ-comp (a ,ᵉ p))) = reflᵉ

-- map-inv-compute-fiberᵉ-comp :
-- Σᵉ (fiberᵉ g x) (λ t → fiberᵉ h (pr1ᵉ t)) → fiberᵉ (g ∘ h) x
-- pr1ᵉ (map-inv-compute-fiberᵉ-comp t) = pr1ᵉ (pr2ᵉ t)
-- pr2ᵉ (map-inv-compute-fiberᵉ-comp t) = apᵉ g (pr2ᵉ (pr2ᵉ t)) ∙ᵉ pr2ᵉ (pr1ᵉ t)

-- is-sectionᵉ-map-inv-compute-fiberᵉ-comp :
-- is-section map-compute-fiberᵉ-comp map-inv-compute-fiberᵉ-comp
-- is-sectionᵉ-map-inv-compute-fiberᵉ-comp ((.(h a) ,ᵉ reflᵉ) ,ᵉ (a ,ᵉ reflᵉ)) = reflᵉ

-- is-retractionᵉ-map-inv-compute-fiberᵉ-comp :
-- is-retraction map-compute-fiberᵉ-comp map-inv-compute-fiberᵉ-comp
-- is-retractionᵉ-map-inv-compute-fiberᵉ-comp (a ,ᵉ reflᵉ) = reflᵉ

-- abstract
-- is-equiv-map-compute-fiberᵉ-comp :
-- is-equiv map-compute-fiberᵉ-comp
-- is-equiv-map-compute-fiberᵉ-comp =
-- is-equiv-is-invertible
-- ( map-inv-compute-fiberᵉ-comp)
-- ( is-sectionᵉ-map-inv-compute-fiberᵉ-comp)
-- ( is-retractionᵉ-map-inv-compute-fiberᵉ-comp)

-- compute-fiberᵉ-comp :
-- fiberᵉ (g ∘ h) x ≃ Σᵉ (fiberᵉ g x) (λ t → fiberᵉ h (pr1ᵉ t))
-- pr1ᵉ compute-fiberᵉ-comp = map-compute-fiberᵉ-comp
-- pr2ᵉ compute-fiberᵉ-comp = is-equiv-map-compute-fiberᵉ-comp

-- abstract
-- is-equiv-map-inv-compute-fiberᵉ-comp :
-- is-equiv map-inv-compute-fiberᵉ-comp
-- is-equiv-map-inv-compute-fiberᵉ-comp =
-- is-equiv-is-invertible
-- ( map-compute-fiberᵉ-comp)
-- ( is-retractionᵉ-map-inv-compute-fiberᵉ-comp)
-- ( is-sectionᵉ-map-inv-compute-fiberᵉ-comp)

-- inv-compute-fiberᵉ-comp :
-- Σᵉ (fiberᵉ g x) (λ t → fiberᵉ h (pr1ᵉ t)) ≃ fiberᵉ (g ∘ h) x
-- pr1ᵉ inv-compute-fiberᵉ-comp = map-inv-compute-fiberᵉ-comp
-- pr2ᵉ inv-compute-fiberᵉ-comp = is-equiv-map-inv-compute-fiberᵉ-comp
-- ```

-- ## Table of files about fibers of maps

-- The following table lists files that are about fibers of maps as a general
-- concept.

-- {{#include tables/fibers-of-maps.md}}
