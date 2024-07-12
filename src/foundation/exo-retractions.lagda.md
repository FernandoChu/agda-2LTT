# Retractions

```agda
module foundation.exo-retractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-dependent-pair-types
open import foundation.exo-universes

open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-identity-types
```

</details>

## Idea

A **retraction** of a map `f : A → B` consists of a map `r : B → A` equipped
with a [homotopy](foundation-core.homotopies.md) `r ∘ᵉ f ~ᵉ id`. In other words, a
retractionᵉ of a map `f` is a left inverse of `f`.

## Definitions

### The type of retractions

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2}
  where

  is-retractionᵉ : (f : A → B) (g : B → A) → UUᵉ l1
  is-retractionᵉ f g = g ∘ᵉ f ~ᵉ idᵉ

  retractionᵉ : (f : A → B) → UUᵉ (l1 ⊔ l2)
  retractionᵉ f = Σᵉ (B → A) (is-retractionᵉ f)

  map-retractionᵉ : (f : A → B) → retractionᵉ f → B → A
  map-retractionᵉ f = pr1ᵉ

  is-retractionᵉ-map-retractionᵉ :
    (f : A → B) (r : retractionᵉ f) → map-retractionᵉ f r ∘ᵉ f ~ᵉ idᵉ
  is-retractionᵉ-map-retractionᵉ f = pr2ᵉ
```

## Properties

### For any map `i : A → B`, a retractionᵉ of `i` induces a retractionᵉ of the action on identifications of `i`

**Proof:** Suppose that `H : r ∘ᵉ i ~ᵉ id` and `p : i x ＝ᵉ i y` is an
identification in `B`. Then we get the identification

```text
     (H x)⁻¹           apᵉ r p           H y
  x ========= r (i x) ======== r (i y) ===== y
```

This defines a map `s : (i x ＝ᵉ i y) → x ＝ᵉ y`. To see that `s ∘ᵉ apᵉ i ~ᵉ id`,
i.e., that the concatenation

```text
     (H x)⁻¹           apᵉ r (ap i p)           H y
  x ========= r (i x) =============== r (i y) ===== y
```

is identical to `p : x ＝ᵉ y` for all `p : x ＝ᵉ y`, we proceed by identification
elimination. Then it suffices to show that `(H x)⁻¹ ∙ᵉ (H x)` is identical to
`refl`, which is indeed the case by the left inverse law of concatenation of
identifications.

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (i : A → B)
  (r : B → A) (H : r ∘ᵉ i ~ᵉ idᵉ)
  where

  is-injective-has-retractionᵉ :
    {x y : A} → i x ＝ᵉ i y → x ＝ᵉ y
  is-injective-has-retractionᵉ {x} {y} p = invᵉ (H x) ∙ᵉ (apᵉ r p ∙ᵉ H y)

  is-retractionᵉ-is-injective-has-retractionᵉ :
    {x y : A} → is-injective-has-retractionᵉ ∘ᵉ apᵉ i {x} {y} ~ᵉ idᵉ
  is-retractionᵉ-is-injective-has-retractionᵉ {x} reflᵉ = left-invᵉ (H x)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (i : A → B) (R : retractionᵉ i)
  where

  is-injective-retractionᵉ :
    {x y : A} → i x ＝ᵉ i y → x ＝ᵉ y
  is-injective-retractionᵉ =
    is-injective-has-retractionᵉ i
      ( map-retractionᵉ i R)
      ( is-retractionᵉ-map-retractionᵉ i R)

  is-retractionᵉ-is-injective-retractionᵉ :
    {x y : A} → is-injective-retractionᵉ ∘ᵉ apᵉ i {x} {y} ~ᵉ idᵉ
  is-retractionᵉ-is-injective-retractionᵉ =
    is-retractionᵉ-is-injective-has-retractionᵉ i
      ( map-retractionᵉ i R)
      ( is-retractionᵉ-map-retractionᵉ i R)

  retractionᵉ-ap : {x y : A} → retractionᵉ (apᵉ i {x} {y})
  pr1ᵉ retractionᵉ-ap = is-injective-retractionᵉ
  pr2ᵉ retractionᵉ-ap = is-retractionᵉ-is-injective-retractionᵉ
```

### Composites of retractions are retractions

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  (g : B → X) (h : A → B) (r : retractionᵉ g) (s : retractionᵉ h)
  where

  map-retractionᵉ-comp : X → A
  map-retractionᵉ-comp = map-retractionᵉ h s ∘ᵉ map-retractionᵉ g r

  is-retractionᵉ-map-retractionᵉ-comp : is-retractionᵉ (g ∘ᵉ h) map-retractionᵉ-comp
  is-retractionᵉ-map-retractionᵉ-comp =
    ( map-retractionᵉ h s ·ᵉl (is-retractionᵉ-map-retractionᵉ g r ·ᵉr h)) ∙ᵉh
    ( is-retractionᵉ-map-retractionᵉ h s)

  retractionᵉ-comp : retractionᵉ (g ∘ᵉ h)
  pr1ᵉ retractionᵉ-comp = map-retractionᵉ-comp
  pr2ᵉ retractionᵉ-comp = is-retractionᵉ-map-retractionᵉ-comp
```

-- ### If `g ∘ᵉ f` has a retractionᵉ then `f` has a retraction

-- ```agda
-- module _
--   {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
--   (g : B → X) (h : A → B) (r : retractionᵉ (g ∘ᵉ h))
--   where

--   map-retractionᵉ-right-factor : B → A
--   map-retractionᵉ-right-factor = map-retractionᵉ (g ∘ᵉ h) r ∘ᵉ g

--   is-retractionᵉ-map-retractionᵉ-right-factor :
--     is-retractionᵉ h map-retractionᵉ-right-factor
--   is-retractionᵉ-map-retractionᵉ-right-factor =
--     is-retractionᵉ-map-retractionᵉ (g ∘ᵉ h) r

--   retractionᵉ-right-factor : retractionᵉ h
--   pr1ᵉ retractionᵉ-right-factor = map-retractionᵉ-right-factor
--   pr2ᵉ retractionᵉ-right-factor = is-retractionᵉ-map-retractionᵉ-right-factor
-- ```

-- ### In a commuting triangle `f ~ᵉ g ∘ᵉ h`, any retractionᵉ of the left map `f` induces a retractionᵉ of the top map `h`

-- In a commuting triangle of the form

-- ```text
--        h
--   A ------> B
--    \       /
--    f\     /g
--      \   /
--       ∨ ∨
--        X,
-- ```

-- if `r : X → A` is a retractionᵉ of the map `f` on the left, then `r ∘ᵉ g` is a
-- retractionᵉ of the top map `h`.

-- Note: In this file we are unable to use the definition of
-- [commuting triangles](foundation-core.commuting-triangles-of-maps.md), because
-- that would result in a cyclic module dependency.

-- ```agda
-- module _
--   {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
--   (f : A → X) (g : B → X) (h : A → B) (H : f ~ᵉ g ∘ᵉ h)
--   (r : retractionᵉ f)
--   where

--   map-retractionᵉ-top-map-triangle : B → A
--   map-retractionᵉ-top-map-triangle = map-retractionᵉ f r ∘ᵉ g

--   is-retractionᵉ-map-retractionᵉ-top-map-triangle :
--     is-retractionᵉ h map-retractionᵉ-top-map-triangle
--   is-retractionᵉ-map-retractionᵉ-top-map-triangle =
--     ( inv-htpy (map-retractionᵉ f r ·l H)) ∙ᵉh
--     ( is-retractionᵉ-map-retractionᵉ f r)

--   retractionᵉ-top-map-triangle : retractionᵉ h
--   pr1ᵉ retractionᵉ-top-map-triangle =
--     map-retractionᵉ-top-map-triangle
--   pr2ᵉ retractionᵉ-top-map-triangle =
--     is-retractionᵉ-map-retractionᵉ-top-map-triangle
-- ```

-- ### In a commuting triangle `f ~ᵉ g ∘ᵉ h`, retractions of `g` and `h` compose to a retractionᵉ of `f`

-- In a commuting triangle of the form

-- ```text
--        h
--   A ------> B
--    \       /
--    f\     /g
--      \   /
--       ∨ ∨
--        X,
-- ```

-- if `r : X → A` is a retractionᵉ of the map `g` on the right and `s : B → A` is a
-- retractionᵉ of the map `h` on top, then `s ∘ᵉ r` is a retractionᵉ of the map `f` on
-- the left.

-- ```agda
-- module _
--   {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
--   (f : A → X) (g : B → X) (h : A → B) (H : f ~ᵉ g ∘ᵉ h)
--   (r : retractionᵉ g) (s : retractionᵉ h)
--   where

--   map-retractionᵉ-left-map-triangle : X → A
--   map-retractionᵉ-left-map-triangle = map-retractionᵉ-comp g h r s

--   is-retractionᵉ-map-retractionᵉ-left-map-triangle :
--     is-retractionᵉ f map-retractionᵉ-left-map-triangle
--   is-retractionᵉ-map-retractionᵉ-left-map-triangle =
--     ( map-retractionᵉ-comp g h r s ·l H) ∙ᵉh
--     ( is-retractionᵉ-map-retractionᵉ-comp g h r s)

--   retractionᵉ-left-map-triangle : retractionᵉ f
--   pr1ᵉ retractionᵉ-left-map-triangle =
--     map-retractionᵉ-left-map-triangle
--   pr2ᵉ retractionᵉ-left-map-triangle =
--     is-retractionᵉ-map-retractionᵉ-left-map-triangle
-- ```

-- ## See also

-- - Retracts of types are defined in
--   [`foundation-core.retracts-of-types`](foundation-core.retracts-of-types.md).
-- - Retracts of maps are defined in
--   [`foundation.retracts-of-maps`](foundation.retracts-of-maps.md).
