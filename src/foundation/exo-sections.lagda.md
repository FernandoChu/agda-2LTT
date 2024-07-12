# Exo-Sections

```agda
module foundation.exo-sections where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-dependent-pair-types
open import foundation.exo-universes
open import foundation.exo-function-types
open import foundation.exo-homotopies
```

</details>

## idᵉea

A **section** of a map `f : A → B` consists of a map `s : B → A` equipped with a
homotopy `f ∘ᵉ s ~ᵉ idᵉ`. In other words, a sectionᵉ of a map `f` is a right inverse
of `f`. For example, every dependent function induces a sectionᵉ of the
projection map.

Note that unlike retractions, sections don't induce sections on identity types.
A map `f` equipped with a sectionᵉ such that all
[actions on identifications](foundation.action-on-identifications-functions.md)
`ap f : (x ＝ y) → (f x ＝ f y)` come equipped with sections is called a
[path split](foundation-core.path-split-maps.md) map. The condition of being
path split is equivalent to being an
[equivalence](foundation-core.equivalences.md).

## Definition

### The predicate of being a sectionᵉ of a map

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-sectionᵉ : (B → A) → UUᵉ l2
  is-sectionᵉ g = f ∘ᵉ g ~ᵉ idᵉ
```

### The type of sections of a map

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  sectionᵉ : UUᵉ (l1 ⊔ l2)
  sectionᵉ = Σᵉ (B → A) (is-sectionᵉ f)

  map-sectionᵉ : sectionᵉ → B → A
  map-sectionᵉ = pr1ᵉ

  is-sectionᵉ-map-sectionᵉ : (s : sectionᵉ) → is-sectionᵉ f (map-sectionᵉ s)
  is-sectionᵉ-map-sectionᵉ = pr2ᵉ
```

## Properties

### If `g ∘ᵉ h` has a sectionᵉ then `g` has a section

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  (g : B → X) (h : A → B) (s : sectionᵉ (g ∘ᵉ h))
  where

  map-sectionᵉ-left-factor : X → B
  map-sectionᵉ-left-factor = h ∘ᵉ map-sectionᵉ (g ∘ᵉ h) s

  is-sectionᵉ-map-sectionᵉ-left-factor : is-sectionᵉ g map-sectionᵉ-left-factor
  is-sectionᵉ-map-sectionᵉ-left-factor = pr2ᵉ s

  sectionᵉ-left-factor : sectionᵉ g
  pr1ᵉ sectionᵉ-left-factor = map-sectionᵉ-left-factor
  pr2ᵉ sectionᵉ-left-factor = is-sectionᵉ-map-sectionᵉ-left-factor
```

### Composites of sections are sections of composites

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  (g : B → X) (h : A → B) (t : sectionᵉ h) (s : sectionᵉ g)
  where

  map-sectionᵉ-comp : X → A
  map-sectionᵉ-comp = map-sectionᵉ h t ∘ᵉ map-sectionᵉ g s

  is-sectionᵉ-map-sectionᵉ-comp :
    is-sectionᵉ (g ∘ᵉ h) map-sectionᵉ-comp
  is-sectionᵉ-map-sectionᵉ-comp =
    ( g ·ᵉl (is-sectionᵉ-map-sectionᵉ h t ·ᵉr map-sectionᵉ g s)) ∙ᵉh
    ( is-sectionᵉ-map-sectionᵉ g s)

  sectionᵉ-comp : sectionᵉ (g ∘ᵉ h)
  pr1ᵉ sectionᵉ-comp = map-sectionᵉ-comp
  pr2ᵉ sectionᵉ-comp = is-sectionᵉ-map-sectionᵉ-comp
```

### In a commuting triangle `g ∘ᵉ h ~ᵉ f`, any sectionᵉ of `f` induces a sectionᵉ of `g`

In a commuting triangle of the form

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if `s : X → A` is a sectionᵉ of the map `f` on the left, then `h ∘ᵉ s` is a
sectionᵉ of the map `g` on the right.

Note: In this file we are unable to use the definition of
[commuting triangles](foundation-core.commuting-triangles-of-maps.md), because
that would result in a cyclic module dependency.

We state two versions: one with a homotopy `g ∘ᵉ h ~ᵉ f`, and the other with a
homotopy `f ~ᵉ g ∘ᵉ h`. Our convention for commuting triangles of maps is that the
homotopy is specified in the second way, i.e., as `f ~ᵉ g ∘ᵉ h`.

#### First version, with the commutativity of the triangle opposite to our convention

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
  (f : A → X) (g : B → X) (h : A → B) (H' : g ∘ᵉ h ~ᵉ f) (s : sectionᵉ f)
  where

  map-sectionᵉ-right-map-triangle' : X → B
  map-sectionᵉ-right-map-triangle' = h ∘ᵉ map-sectionᵉ f s

  is-sectionᵉ-map-sectionᵉ-right-map-triangle' :
    is-sectionᵉ g map-sectionᵉ-right-map-triangle'
  is-sectionᵉ-map-sectionᵉ-right-map-triangle' =
    (H' ·ᵉr map-sectionᵉ f s) ∙ᵉh is-sectionᵉ-map-sectionᵉ f s

  sectionᵉ-right-map-triangle' : sectionᵉ g
  pr1ᵉ sectionᵉ-right-map-triangle' =
    map-sectionᵉ-right-map-triangle'
  pr2ᵉ sectionᵉ-right-map-triangle' =
    is-sectionᵉ-map-sectionᵉ-right-map-triangle'
```

-- #### Second version, with the commutativity of the triangle accoring to our convention

-- We state the same result as the previous result, only with the homotopy
-- witnessing the commutativity of the triangle inverted.

-- ```agda
-- module _
--   {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
--   (f : A → X) (g : B → X) (h : A → B) (H : f ~ᵉ g ∘ᵉ h) (s : sectionᵉ f)
--   where

--   map-sectionᵉ-right-map-triangle : X → B
--   map-sectionᵉ-right-map-triangle =
--     map-sectionᵉ-right-map-triangle' f g h (inv-htpy H) s

--   is-sectionᵉ-map-sectionᵉ-right-map-triangle :
--     is-sectionᵉ g map-sectionᵉ-right-map-triangle
--   is-sectionᵉ-map-sectionᵉ-right-map-triangle =
--     is-sectionᵉ-map-sectionᵉ-right-map-triangle' f g h (inv-htpy H) s

--   sectionᵉ-right-map-triangle : sectionᵉ g
--   sectionᵉ-right-map-triangle =
--     sectionᵉ-right-map-triangle' f g h (inv-htpy H) s
-- ```

-- ### Composites of sections in commuting triangles are sections

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

-- if `s : X → B` is a sectionᵉ of the map `g` on the right and `t : B → A` is a
-- sectionᵉ of the map `h` on top, then `t ∘ᵉ s` is a sectionᵉ of the map `f` on the
-- left.

-- ```agda
-- module _
--   {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {X : UUᵉ l3}
--   (f : A → X) (g : B → X) (h : A → B) (H : f ~ᵉ g ∘ᵉ h) (t : sectionᵉ h)
--   where

--   map-sectionᵉ-left-map-triangle : sectionᵉ g → X → A
--   map-sectionᵉ-left-map-triangle s = map-sectionᵉ-comp g h t s

--   is-sectionᵉ-map-sectionᵉ-left-map-triangle :
--     (s : sectionᵉ g) → is-sectionᵉ f (map-sectionᵉ-left-map-triangle s)
--   is-sectionᵉ-map-sectionᵉ-left-map-triangle s =
--     ( H ·r map-sectionᵉ-comp g h t s) ∙h
--     ( is-sectionᵉ-map-sectionᵉ-comp g h t s)

--   sectionᵉ-left-map-triangle : sectionᵉ g → sectionᵉ f
--   pr1ᵉ (sectionᵉ-left-map-triangle s) = map-sectionᵉ-left-map-triangle s
--   pr2ᵉ (sectionᵉ-left-map-triangle s) = is-sectionᵉ-map-sectionᵉ-left-map-triangle s
-- ```
