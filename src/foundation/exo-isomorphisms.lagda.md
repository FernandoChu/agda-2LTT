# Exo-isomorphisms

```agda
module foundation.exo-isomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-retractions
open import foundation.exo-retracts-of-exo-types
open import foundation.exo-sections
-- open import foundation.exo-sections-of-exo-types
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types
open import foundation.exo-universes
```

</details>

## Idea

Exoisomorphisms.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  where

  is-inverse : (A → B) → (B → A) → UUᵉ (l1 ⊔ l2)
  is-inverse f g = is-sectionᵉ f g ×ᵉ is-retractionᵉ f g

  is-exo-iso : (f : A → B) → UUᵉ (l1 ⊔ l2)
  is-exo-iso f =
    Σᵉ (B → A) (λ g → is-inverse f g)

module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  where

  is-fiberwise-exo-iso : (f : (a : A) → B a → C a) → UUᵉ (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-exo-iso f = (a : A) → is-exo-iso (f a)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  {f : A → B} (H : is-exo-iso f)
  where

  map-inv-is-exo-iso : B → A
  map-inv-is-exo-iso = pr1ᵉ H

  is-retractionᵉ-is-exo-iso : (f ∘ᵉ map-inv-is-exo-iso) ~ᵉ idᵉ
  is-retractionᵉ-is-exo-iso = pr1ᵉ (pr2ᵉ H)

  is-sectionᵉ-is-exo-iso : (map-inv-is-exo-iso ∘ᵉ f) ~ᵉ idᵉ
  is-sectionᵉ-is-exo-iso = pr2ᵉ (pr2ᵉ H)

  retractionᵉ-is-exo-iso : retractionᵉ f
  pr1ᵉ retractionᵉ-is-exo-iso = map-inv-is-exo-iso 
  pr2ᵉ retractionᵉ-is-exo-iso = is-sectionᵉ-is-exo-iso 

  sectionᵉ-is-exo-iso : sectionᵉ f
  pr1ᵉ sectionᵉ-is-exo-iso = map-inv-is-exo-iso
  pr2ᵉ sectionᵉ-is-exo-iso = is-retractionᵉ-is-exo-iso

module _
  {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2)
  where

  exo-iso : UUᵉ (l1 ⊔ l2)
  exo-iso = Σᵉ (A → B) is-exo-iso

  infix 6 _≅ᵉ_

  _≅ᵉ_ : UUᵉ (l1 ⊔ l2)
  _≅ᵉ_ = exo-iso

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (e : A ≅ᵉ B)
  where

  map-exo-iso : A → B
  map-exo-iso = pr1ᵉ e

  is-exo-iso-map-exo-iso : is-exo-iso map-exo-iso
  is-exo-iso-map-exo-iso = pr2ᵉ e

  map-inv-exo-iso : B → A
  map-inv-exo-iso = map-inv-is-exo-iso is-exo-iso-map-exo-iso

  is-sectionᵉ-map-exo-iso : (map-inv-exo-iso ∘ᵉ map-exo-iso) ~ᵉ idᵉ
  is-sectionᵉ-map-exo-iso = is-sectionᵉ-is-exo-iso is-exo-iso-map-exo-iso

  is-retractionᵉ-map-exo-iso : (map-exo-iso ∘ᵉ map-inv-exo-iso) ~ᵉ idᵉ
  is-retractionᵉ-map-exo-iso = is-retractionᵉ-is-exo-iso is-exo-iso-map-exo-iso

module _
  {l : Level} {A : UUᵉ l}
  where

  is-exo-iso-idᵉ : is-exo-iso (idᵉ {l} {A})
  pr1ᵉ is-exo-iso-idᵉ = idᵉ
  pr1ᵉ (pr2ᵉ is-exo-iso-idᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ is-exo-iso-idᵉ) = refl-htpyᵉ

  id-exo-iso : A ≅ᵉ A
  pr1ᵉ id-exo-iso = idᵉ
  pr2ᵉ id-exo-iso = is-exo-iso-idᵉ
```

### Symmetry

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (e : A ≅ᵉ B)
  where

  is-exo-iso-map-inv-exo-iso : is-exo-iso (map-inv-exo-iso e)
  pr1ᵉ is-exo-iso-map-inv-exo-iso = map-exo-iso e
  pr1ᵉ (pr2ᵉ is-exo-iso-map-inv-exo-iso) = is-sectionᵉ-map-exo-iso e
  pr2ᵉ (pr2ᵉ is-exo-iso-map-inv-exo-iso) = is-retractionᵉ-map-exo-iso e

  inv-exo-iso : B ≅ᵉ A
  pr1ᵉ inv-exo-iso = map-inv-exo-iso e
  pr2ᵉ inv-exo-iso = is-exo-iso-map-inv-exo-iso
```

### Two out of three

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ᵉ g ∘ᵉ h)
  where

  abstract
    is-exo-iso-left-map-triangle : is-exo-iso h → is-exo-iso g → is-exo-iso f
    is-exo-iso-left-map-triangle H G =
      pairᵉ
        (  h⁻¹ ∘ᵉ g⁻¹)
        ( pairᵉ
          ( λ x →
            equational-reasoningᵉ
              (f ∘ᵉ h⁻¹ ∘ᵉ g⁻¹) x
                ＝ᵉ (g ∘ᵉ h ∘ᵉ h⁻¹ ∘ᵉ g⁻¹) x
                  byᵉ T (map-inv-is-exo-iso H (map-inv-is-exo-iso G x))
                ＝ᵉ (g ∘ᵉ g⁻¹) x
                  byᵉ apᵉ g (is-retractionᵉ-is-exo-iso H (map-inv-is-exo-iso G x))
                ＝ᵉ x
                  byᵉ is-retractionᵉ-is-exo-iso G x)
          ( λ a →
            equational-reasoningᵉ
              (h⁻¹ ∘ᵉ g⁻¹ ∘ᵉ f) a
                ＝ᵉ (h⁻¹ ∘ᵉ g⁻¹ ∘ᵉ g ∘ᵉ h) a
                  byᵉ apᵉ (h⁻¹ ∘ᵉ g⁻¹) (T a)
                ＝ᵉ (h⁻¹ ∘ᵉ h) a
                  byᵉ apᵉ h⁻¹ (is-sectionᵉ-is-exo-iso G (h a))
                ＝ᵉ a
                  byᵉ is-sectionᵉ-is-exo-iso H a))
      where
        g⁻¹ : X → B
        g⁻¹ = map-inv-is-exo-iso G
        h⁻¹ : B → A
        h⁻¹ = map-inv-is-exo-iso H

module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  where

  abstract
    is-exo-iso-comp :
      (g : B → X) (f : A → B) →
      is-exo-iso f → is-exo-iso g →
      is-exo-iso (g ∘ᵉ f)
    pr1ᵉ (is-exo-iso-comp g f is-exo-iso-f is-exo-iso-g) =
      map-inv-is-exo-iso is-exo-iso-f ∘ᵉ map-inv-is-exo-iso is-exo-iso-g
    pr1ᵉ (pr2ᵉ (is-exo-iso-comp g f is-exo-iso-f is-exo-iso-g)) =
      is-sectionᵉ-map-sectionᵉ-comp g f
        ( sectionᵉ-is-exo-iso is-exo-iso-f)
        ( sectionᵉ-is-exo-iso is-exo-iso-g)
    pr2ᵉ (pr2ᵉ (is-exo-iso-comp g f is-exo-iso-f is-exo-iso-g)) =
      is-retractionᵉ-map-retractionᵉ-comp g f
        ( retractionᵉ-is-exo-iso is-exo-iso-g)
        ( retractionᵉ-is-exo-iso is-exo-iso-f)

  comp-exo-iso : B ≅ᵉ X → A ≅ᵉ B → A ≅ᵉ X
  pr1ᵉ (comp-exo-iso g h) = map-exo-iso g ∘ᵉ map-exo-iso h
  pr2ᵉ (comp-exo-iso g h) = is-exo-iso-comp (pr1ᵉ g) (pr1ᵉ h) (pr2ᵉ h) (pr2ᵉ g)
```
