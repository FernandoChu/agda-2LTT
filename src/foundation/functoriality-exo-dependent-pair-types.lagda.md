# Functoriality of exo dependent pairᵉ types

```agda
module foundation.functoriality-exo-dependent-pair-types where


open import foundation.identity-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.exo-function-types
open import foundation.function-types
open import foundation.exo-fibers-of-exo-maps
open import foundation.exo-contractible-exo-types
open import foundation.exo-contractible-exo-maps
open import foundation.exo-unit-type
open import foundation.unit-type
open import foundation.coercing-inner-types
open import foundation.exo-homotopies
open import foundation.homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types
open import foundation.exo-universes
open import foundation.exo-isomorphisms
open import foundation.exo-equality-exo-dependent-pair-types
```

## Idea

## Definition

### The induced map on total spaces

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  (f : (x : A) → B x → C x)
  where
```

Any family of maps induces a map on the total spaces.

```agda
  totᵉ : Σᵉ A B → Σᵉ A C
  pr1ᵉ (totᵉ t) = pr1ᵉ t
  pr2ᵉ (totᵉ t) = f (pr1ᵉ t) (pr2ᵉ t)
```

### Any map `f : A → B` induces a map `Σᵉ A (C ∘ᵉ f) → Σᵉ B C`

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : B → UUᵉ l3)
  where

  map-Σᵉ-map-base : Σᵉ A (λ x → C (f x)) → Σᵉ B C
  pr1ᵉ (map-Σᵉ-map-base s) = f (pr1ᵉ s)
  pr2ᵉ (map-Σᵉ-map-base s) = pr2ᵉ s
```

### The functorial action of dependent pairᵉ types, and its defining homotopy

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : A → UUᵉ l3}
  (D : B → UUᵉ l4)
  where

  map-Σᵉ :
    (f : A → B) (g : (x : A) → C x → D (f x)) → Σᵉ A C → Σᵉ B D
  pr1ᵉ (map-Σᵉ f g (a ,ᵉ c)) = f a
  pr2ᵉ (map-Σᵉ f g (a ,ᵉ c)) = g a c

  triangle-map-Σᵉ :
    (f : A → B) (g : (x : A) → C x → D (f x)) →
    (map-Σᵉ f g) ~ᵉ (map-Σᵉ-map-base f D ∘ᵉ totᵉ g)
  triangle-map-Σᵉ f g t = reflᵉ
```

## Properties

### The map `map-Σ` preserves homotopies

```agda

```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : A → UUᵉ l3}
  (D : B → UUᵉ l4)
  where

  htpy-map-Σᵉ :
    {f f' : A → B} (H : f ~ᵉ f')
    (g : (x : A) → C x → D (f x)) {g' : (x : A) → C x → D (f' x)}
    (K : (x : A) → ((trᵉ D (H x)) ∘ᵉ (g x)) ~ᵉ (g' x)) →
    (map-Σᵉ D f g) ~ᵉ (map-Σᵉ D f' g')
  htpy-map-Σᵉ H g K t = eq-pairᵉ-Σᵉ' (pairᵉ (H (pr1ᵉ t)) (K (pr1ᵉ t) (pr2ᵉ t)))
```

### The map `tot` preserves homotopies

```agda
tot-htpy :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ᵉ g x) → totᵉ f ~ᵉ totᵉ g
tot-htpy H (pairᵉ x y) = eq-pairᵉ-eq-fiber (H x y)
```

### The map `tot` preserves identity maps

```agda
tot-id :
  {l1 l2 : Level} {A : UUᵉ l1} (B : A → UUᵉ l2) →
  (totᵉ (λ x (y : B x) → y)) ~ᵉ idᵉ
tot-id B (pairᵉ x y) = reflᵉ
```

### The map `tot` preserves composition

```agda
preserves-comp-totᵉ :
  {l1 l2 l3 l4 : Level}
  {A : UUᵉ l1} {B : A → UUᵉ l2} {B' : A → UUᵉ l3} {B'' : A → UUᵉ l4}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  totᵉ (λ x → (g x) ∘ᵉ (f x)) ~ᵉ ((totᵉ g) ∘ᵉ (totᵉ f))
preserves-comp-totᵉ f g (pairᵉ x y) = reflᵉ
```

### The fibers of `tot`

We show that for any family of maps, the fiberᵉ of the induced map on total
spaces are equivalent to the fibers of the maps in the family.

````agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  (f : (x : A) → B x → C x)
  where

  map-compute-fiber-totᵉ :
    (t : Σᵉ A C) → fiberᵉ (totᵉ f) t → fiberᵉ (f (pr1ᵉ t)) (pr2ᵉ t)
  pr1ᵉ (map-compute-fiber-totᵉ .(totᵉ f (pairᵉ x y)) (pairᵉ (pairᵉ x y) reflᵉ)) = y
  pr2ᵉ (map-compute-fiber-totᵉ .(totᵉ f (pairᵉ x y)) (pairᵉ (pairᵉ x y) reflᵉ)) = reflᵉ

  map-inv-compute-fiber-totᵉ :
    (t : Σᵉ A C) → fiberᵉ (f (pr1ᵉ t)) (pr2ᵉ t) → fiberᵉ (totᵉ f) t
  pr1ᵉ (pr1ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ a .(f a y)) (pairᵉ y reflᵉ))) = a
  pr2ᵉ (pr1ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ a .(f a y)) (pairᵉ y reflᵉ))) = y
  pr2ᵉ (map-inv-compute-fiber-totᵉ (pairᵉ a .(f a y)) (pairᵉ y reflᵉ)) = reflᵉ

  is-sectionᵉ-map-inv-compute-fiber-totᵉ :
    (t : Σᵉ A C) → (map-compute-fiber-totᵉ t ∘ᵉ map-inv-compute-fiber-totᵉ t) ~ᵉ idᵉ
  is-sectionᵉ-map-inv-compute-fiber-totᵉ (pairᵉ x .(f x y)) (pairᵉ y reflᵉ) = reflᵉ

  is-retractionᵉ-map-inv-compute-fiber-totᵉ :
    (t : Σᵉ A C) → (map-inv-compute-fiber-totᵉ t ∘ᵉ map-compute-fiber-totᵉ t) ~ᵉ idᵉ
  is-retractionᵉ-map-inv-compute-fiber-totᵉ ._ (pairᵉ (pairᵉ x y) reflᵉ) =
    reflᵉ

  is-exo-iso-map-compute-fiber-totᵉ :
    (t : Σᵉ A C) → is-exo-iso (map-compute-fiber-totᵉ t)
  pr1ᵉ (is-exo-iso-map-compute-fiber-totᵉ t) = map-inv-compute-fiber-totᵉ t
  pr1ᵉ (pr2ᵉ (is-exo-iso-map-compute-fiber-totᵉ t)) = is-sectionᵉ-map-inv-compute-fiber-totᵉ t
  pr2ᵉ (pr2ᵉ (is-exo-iso-map-compute-fiber-totᵉ t)) = is-retractionᵉ-map-inv-compute-fiber-totᵉ t

  compute-fiber-totᵉ : (t : Σᵉ A C) → fiberᵉ (totᵉ f) t ≅ᵉ fiberᵉ (f (pr1ᵉ t)) (pr2ᵉ t)
  pr1ᵉ (compute-fiber-totᵉ t) = map-compute-fiber-totᵉ t
  pr2ᵉ (compute-fiber-totᵉ t) = is-exo-iso-map-compute-fiber-totᵉ t

  is-exo-iso-map-inv-compute-fiber-totᵉ :
    (t : Σᵉ A C) → is-exo-iso (map-inv-compute-fiber-totᵉ t)
  pr1ᵉ (is-exo-iso-map-inv-compute-fiber-totᵉ t) = map-compute-fiber-totᵉ t
  pr1ᵉ (pr2ᵉ (is-exo-iso-map-inv-compute-fiber-totᵉ t)) = is-retractionᵉ-map-inv-compute-fiber-totᵉ t
  pr2ᵉ (pr2ᵉ (is-exo-iso-map-inv-compute-fiber-totᵉ t)) = is-sectionᵉ-map-inv-compute-fiber-totᵉ t

  inv-compute-fiber-totᵉ :
    (t : Σᵉ A C) → fiberᵉ (f (pr1ᵉ t)) (pr2ᵉ t) ≅ᵉ fiberᵉ (totᵉ f) t
  pr1ᵉ (inv-compute-fiber-totᵉ t) = map-inv-compute-fiber-totᵉ t
  pr2ᵉ (inv-compute-fiber-totᵉ t) = is-exo-iso-map-inv-compute-fiber-totᵉ t
```

### A family of maps `f` is a family of equivalences if and only if `totᵉ f` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-exo-iso-tot-is-fiberwise-exo-iso : is-fiberwise-exo-iso f → is-exo-iso (totᵉ f)
    is-exo-iso-tot-is-fiberwise-exo-iso H =
      is-exo-iso-is-contrᵉ-map
        ( λ t →
          is-contrᵉ-is-exo-iso
            ( fiberᵉ (f (pr1ᵉ t)) (pr2ᵉ t))
            ( map-compute-fiber-totᵉ f t)
            ( is-exo-iso-map-compute-fiber-totᵉ f t)
            ( is-contrᵉ-map-is-exo-iso (H (pr1ᵉ t)) (pr2ᵉ t)))

  abstract
    is-fiberwise-exo-iso-is-exo-iso-totᵉ : is-exo-iso (totᵉ f) → is-fiberwise-exo-iso f
    is-fiberwise-exo-iso-is-exo-iso-totᵉ is-exo-iso-tot-f x =
      is-exo-iso-is-contrᵉ-map
        ( λ z →
          is-contrᵉ-is-exo-iso'
            ( fiberᵉ (totᵉ f) (pairᵉ x z))
            ( map-compute-fiber-totᵉ f (pairᵉ x z))
            ( is-exo-iso-map-compute-fiber-totᵉ f (pairᵉ x z))
            ( is-contrᵉ-map-is-exo-iso is-exo-iso-tot-f (pairᵉ x z)))
```

### The action of `tot` on equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2} {C : A → UUᵉ l3}
  where

  exo-iso-totᵉ : ((x : A) → B x ≅ᵉ C x) → (Σᵉ A B) ≅ᵉ (Σᵉ A C)
  pr1ᵉ (exo-iso-totᵉ e) = totᵉ (λ x → map-exo-iso (e x))
  pr2ᵉ (exo-iso-totᵉ e) =
    is-exo-iso-tot-is-fiberwise-exo-iso (λ x → is-exo-iso-map-exo-iso (e x))
```

### The fibers of `map-Σᵉ-map-base`

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : B → UUᵉ l3)
  where

  fiber-map-Σᵉ-map-base-fiberᵉ :
    (t : Σᵉ B C) → fiberᵉ f (pr1ᵉ t) → fiberᵉ (map-Σᵉ-map-base f C) t
  pr1ᵉ (pr1ᵉ (fiber-map-Σᵉ-map-base-fiberᵉ (pairᵉ .(f x) z) (pairᵉ x reflᵉ))) = x
  pr2ᵉ (pr1ᵉ (fiber-map-Σᵉ-map-base-fiberᵉ (pairᵉ .(f x) z) (pairᵉ x reflᵉ))) = z
  pr2ᵉ (fiber-map-Σᵉ-map-base-fiberᵉ (pairᵉ .(f x) z) (pairᵉ x reflᵉ)) = reflᵉ

  fiber-fiber-map-Σᵉ-map-base :
    (t : Σᵉ B C) → fiberᵉ (map-Σᵉ-map-base f C) t → fiberᵉ f (pr1ᵉ t)
  pr1ᵉ
    ( fiber-fiber-map-Σᵉ-map-base
      .(map-Σᵉ-map-base f C (pairᵉ x z)) (pairᵉ (pairᵉ x z) reflᵉ)) = x
  pr2ᵉ
    ( fiber-fiber-map-Σᵉ-map-base
      .(map-Σᵉ-map-base f C (pairᵉ x z)) (pairᵉ (pairᵉ x z) reflᵉ)) = reflᵉ

  is-sectionᵉ-fiber-fiber-map-Σᵉ-map-base :
    (t : Σᵉ B C) →
    (fiber-map-Σᵉ-map-base-fiberᵉ t ∘ᵉ fiber-fiber-map-Σᵉ-map-base t) ~ᵉ idᵉ
  is-sectionᵉ-fiber-fiber-map-Σᵉ-map-base .(pairᵉ (f x) z) (pairᵉ (pairᵉ x z) reflᵉ) =
    reflᵉ

  is-retractionᵉ-fiber-fiber-map-Σᵉ-map-base :
    (t : Σᵉ B C) →
    (fiber-fiber-map-Σᵉ-map-base t ∘ᵉ fiber-map-Σᵉ-map-base-fiberᵉ t) ~ᵉ idᵉ
  is-retractionᵉ-fiber-fiber-map-Σᵉ-map-base (pairᵉ .(f x) z) (pairᵉ x reflᵉ) = reflᵉ

  abstract
    is-exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ :
      (t : Σᵉ B C) → is-exo-iso (fiber-map-Σᵉ-map-base-fiberᵉ t)
    pr1ᵉ (is-exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t) = fiber-fiber-map-Σᵉ-map-base t
    pr1ᵉ (pr2ᵉ (is-exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t)) = is-sectionᵉ-fiber-fiber-map-Σᵉ-map-base t
    pr2ᵉ (pr2ᵉ (is-exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t)) = is-retractionᵉ-fiber-fiber-map-Σᵉ-map-base t

  exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ :
    (t : Σᵉ B C) → fiberᵉ f (pr1ᵉ t) ≅ᵉ fiberᵉ (map-Σᵉ-map-base f C) t
  pr1ᵉ (exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t) = fiber-map-Σᵉ-map-base-fiberᵉ t
  pr2ᵉ (exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t) =
    is-exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ t
```

### If `f : A → B` is a contractible map, then so is `map-Σᵉ-map-base f C`

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : B → UUᵉ l3)
  where

  abstract
    is-contrᵉ-map-map-Σᵉ-map-base :
      is-contrᵉ-map f → is-contrᵉ-map (map-Σᵉ-map-base f C)
    is-contrᵉ-map-map-Σᵉ-map-base is-contr-f (pairᵉ y z) =
      is-contrᵉ-exo-iso'
        ( fiberᵉ f y)
        ( exo-iso-fiber-map-Σᵉ-map-base-fiberᵉ f C (pairᵉ y z))
        ( is-contr-f y)
```

### If `f : A → B` is an equivalence, then so is `map-Σᵉ-map-base f C`

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B) (C : B → UUᵉ l3)
  where

  abstract
    is-exo-iso-map-Σᵉ-map-base : is-exo-iso f → is-exo-iso (map-Σᵉ-map-base f C)
    is-exo-iso-map-Σᵉ-map-base is-exo-iso-f =
      is-exo-iso-is-contrᵉ-map
        ( is-contrᵉ-map-map-Σᵉ-map-base f C (is-contrᵉ-map-is-exo-iso is-exo-iso-f))

exo-iso-Σ-exo-iso-base :
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (C : B → UUᵉ l3) (e : A ≅ᵉ B) →
  Σᵉ A (C ∘ᵉ map-exo-iso e) ≅ᵉ Σᵉ B C
pr1ᵉ (exo-iso-Σ-exo-iso-base C (pairᵉ f is-exo-iso-f)) = map-Σᵉ-map-base f C
pr2ᵉ (exo-iso-Σ-exo-iso-base C (pairᵉ f is-exo-iso-f)) =
  is-exo-iso-map-Σᵉ-map-base f C is-exo-iso-f
```

### The functorial action of dependent pairᵉ types preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : A → UUᵉ l3}
  (D : B → UUᵉ l4)
  where

  abstract
    is-exo-iso-map-Σᵉ :
      {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-exo-iso f → is-fiberwise-exo-iso g → is-exo-iso (map-Σᵉ D f g)
    is-exo-iso-map-Σᵉ {f} {g} is-exo-iso-f is-fiberwise-exo-iso-g =
      is-exo-iso-left-map-triangle
        ( map-Σᵉ D f g)
        ( map-Σᵉ-map-base f D)
        ( totᵉ g)
        ( triangle-map-Σᵉ D f g)
        ( is-exo-iso-tot-is-fiberwise-exo-iso is-fiberwise-exo-iso-g)
        ( is-exo-iso-map-Σᵉ-map-base f D is-exo-iso-f)

  exo-iso-Σᵉ :
    (e : A ≅ᵉ B) (g : (x : A) → C x ≅ᵉ D (map-exo-iso e x)) → Σᵉ A C ≅ᵉ Σᵉ B D
  pr1ᵉ (exo-iso-Σᵉ e g) = map-Σᵉ D (map-exo-iso e) (λ x → map-exo-iso (g x))
  pr2ᵉ (exo-iso-Σᵉ e g) =
    is-exo-iso-map-Σᵉ
      ( is-exo-iso-map-exo-iso e)
      ( λ x → is-exo-iso-map-exo-iso (g x))
```
