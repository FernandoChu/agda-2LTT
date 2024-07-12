# Contractible maps

```agda
module foundation.exo-contractible-exo-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-dependent-pair-types
open import foundation.exo-universes

open import foundation.exo-contractible-exo-types
open import foundation.exo-isomorphisms
open import foundation.exo-fibers-of-exo-maps
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-identity-types
```

</details>

## idᵉea

A map is often said to satisfy a property `P` if each of its fibers satisfy
property `P`. Thus, we define contractible maps to be maps of which each fiber
is contractible. In other words, contractible maps are maps `f : A → B` such
that for each element `b : B` there is a unique `a : A` equipped with an
identification `(f a) ＝ b`, i.e., contractible maps are the type theoretic
bijections.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  where

  is-contrᵉ-map : (A → B) → UUᵉ (l1 ⊔ l2)
  is-contrᵉ-map f = (y : B) → is-contrᵉ (fiberᵉ f y)
```

## Properties

### Any contractible map is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f : A → B}
  where

  map-inv-is-contrᵉ-map : is-contrᵉ-map f → B → A
  map-inv-is-contrᵉ-map H y = pr1ᵉ (center (H y))

  is-sectionᵉ-map-inv-is-contrᵉ-map :
    (H : is-contrᵉ-map f) → (f ∘ᵉ (map-inv-is-contrᵉ-map H)) ~ᵉ idᵉ
  is-sectionᵉ-map-inv-is-contrᵉ-map H y = pr2ᵉ (center (H y))

  is-retractionᵉ-map-inv-is-contrᵉ-map :
    (H : is-contrᵉ-map f) → ((map-inv-is-contrᵉ-map H) ∘ᵉ f) ~ᵉ idᵉ
  is-retractionᵉ-map-inv-is-contrᵉ-map H x =
    apᵉ
      ( pr1ᵉ {B = λ z → (f z) ＝ᵉ (f x)})
      ( ( invᵉ
          ( contraction
            ( H (f x))
            ( ( map-inv-is-contrᵉ-map H (f x)) ,ᵉ
              ( is-sectionᵉ-map-inv-is-contrᵉ-map H (f x))))) ∙ᵉ
        ( contraction (H (f x)) (x ,ᵉ reflᵉ)))

  abstract
    is-exo-iso-is-contrᵉ-map : is-contrᵉ-map f → is-exo-iso f
    pr1ᵉ (is-exo-iso-is-contrᵉ-map H) = map-inv-is-contrᵉ-map H
    pr1ᵉ (pr2ᵉ (is-exo-iso-is-contrᵉ-map H)) = is-sectionᵉ-map-inv-is-contrᵉ-map H
    pr2ᵉ (pr2ᵉ (is-exo-iso-is-contrᵉ-map H)) = is-retractionᵉ-map-inv-is-contrᵉ-map H
```

### Any coherently invertible map is a contractible map

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f : A → B}
--   where

--   abstract
--     center-fiber-is-coherently-invertible :
--       is-coherently-invertible f → (y : B) → fiber f y
--     pr1ᵉ (center-fiber-is-coherently-invertible H y) =
--       map-inv-is-coherently-invertible H y
--     pr2ᵉ (center-fiber-is-coherently-invertible H y) =
--       is-sectionᵉ-map-inv-is-coherently-invertible H y

--     contraction-fiber-is-coherently-invertible :
--       (H : is-coherently-invertible f) → (y : B) → (t : fiber f y) →
--       (center-fiber-is-coherently-invertible H y) ＝ t
--     contraction-fiber-is-coherently-invertible H y (x , refl) =
--       eq-Eq-fiber f y
--         ( is-retractionᵉ-map-inv-is-coherently-invertible H x)
--         ( ( right-unit) ∙
--           ( inv ( coh-is-coherently-invertible H x)))

--   is-contrᵉ-map-is-coherently-invertible :
--     is-coherently-invertible f → is-contrᵉ-map f
--   pr1ᵉ (is-contrᵉ-map-is-coherently-invertible H y) =
--     center-fiber-is-coherently-invertible H y
--   pr2ᵉ (is-contrᵉ-map-is-coherently-invertible H y) =
--     contraction-fiber-is-coherently-invertible H y
-- ```

-- ### Any equivalence is a contractible map

-- ```agda
-- module _
--   {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f : A → B}
--   where

--   abstract
--     is-contrᵉ-map-is-equiv : is-equiv f → is-contrᵉ-map f
--     is-contrᵉ-map-is-equiv =
--       is-contrᵉ-map-is-coherently-invertible ∘ᵉ is-coherently-invertible-is-equiv
-- ```

-- ### Any equivalence is a contractible map

-- ```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {f : A → B}
  where

  abstract
    is-contrᵉ-map-is-exo-iso : is-exo-iso f → is-contrᵉ-map f
    pr1ᵉ (pr1ᵉ (is-contrᵉ-map-is-exo-iso is-exo-iso-f b)) =
      map-inv-is-exo-iso is-exo-iso-f b
    pr2ᵉ (pr1ᵉ (is-contrᵉ-map-is-exo-iso is-exo-iso-f b)) =
      is-retractionᵉ-is-exo-iso is-exo-iso-f b
    pr2ᵉ (is-contrᵉ-map-is-exo-iso is-exo-iso-f b) (a ,ᵉ reflᵉ) =
      eq-Eq-fiberᵉ-uncurry f b
        ( pairᵉ (is-sectionᵉ-is-exo-iso is-exo-iso-f a )
        ( UIPᵉ _ _))
```

-- ## See also

-- - For the notion of biinvertible maps see
--   [`foundation.equivalences`](foundation.equivalences.md).
-- - For the notion of coherently invertible maps, also known as half-adjoint
--   equivalences, see
--   [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
-- - For the notion of path-split maps see
--   [`foundation.path-split-maps`](foundation.path-split-maps.md).
