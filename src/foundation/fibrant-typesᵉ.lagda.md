# Fibrant exo-types

```agda
module foundation.fibrant-typesᵉ where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.pi-decompositionsᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.function-typesᵉ
open import foundation.function-types
open import foundation.unit-typeᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.equivalences
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.identity-types
open import foundation.function-extensionality
open import foundation.universe-levelsᵉ
open import foundation.equivalencesᵉ
open import foundation.coercing-inner-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.universe-levels
```

## Idea

## Definition

### Fibrant types

```agda
record is-fibrant {i : Level} (A : UUᵉ i) : UUᵉ (lsuc i) where
  field
    witness-is-fibrant : UU i
    equiv-witness-is-fibrant : coerce witness-is-fibrant ≃ᵉ A

  map-is-fibrant : coerce witness-is-fibrant → A
  map-is-fibrant = map-equivᵉ equiv-witness-is-fibrant

  is-equiv-map-is-fibrant : is-equivᵉ map-is-fibrant
  is-equiv-map-is-fibrant = is-equiv-map-equivᵉ equiv-witness-is-fibrant

  map-inv-is-fibrant : A → coerce witness-is-fibrant
  map-inv-is-fibrant = map-inv-equivᵉ equiv-witness-is-fibrant

  is-section-map-is-fibrant : (map-inv-is-fibrant ∘ᵉ map-is-fibrant) ~ᵉ idᵉ
  is-section-map-is-fibrant = is-retraction-map-inv-equivᵉ equiv-witness-is-fibrant

  is-retraction-map-is-fibrant : (map-is-fibrant ∘ᵉ map-inv-is-fibrant) ~ᵉ idᵉ
  is-retraction-map-is-fibrant = is-section-map-inv-equivᵉ equiv-witness-is-fibrant

open is-fibrant public

Fibrant-Type : (l : Level) → UUᵉ (lsuc l)
Fibrant-Type l = Σᵉ (UUᵉ l) (λ A → is-fibrant A)

module _
  {l : Level} (A : Fibrant-Type l)
  where

  type-Fibrant-Type : UUᵉ l
  type-Fibrant-Type = pr1ᵉ A

  is-fibrant-Fibrant-Type : is-fibrant type-Fibrant-Type
  is-fibrant-Fibrant-Type = pr2ᵉ A

  witness-Fibrant-Type : UU l
  witness-Fibrant-Type = witness-is-fibrant is-fibrant-Fibrant-Type

  equiv-witness-Fibrant-Type : coerce witness-Fibrant-Type ≃ᵉ type-Fibrant-Type
  equiv-witness-Fibrant-Type = equiv-witness-is-fibrant is-fibrant-Fibrant-Type

  map-Fibrant-Type : coerce witness-Fibrant-Type → type-Fibrant-Type
  map-Fibrant-Type = map-is-fibrant is-fibrant-Fibrant-Type

  map-inv-Fibrant-Type : type-Fibrant-Type → coerce witness-Fibrant-Type
  map-inv-Fibrant-Type = map-inv-is-fibrant is-fibrant-Fibrant-Type

  is-section-map-Fibrant-Type :
    (map-inv-Fibrant-Type ∘ᵉ map-Fibrant-Type) ~ᵉ idᵉ
  is-section-map-Fibrant-Type =
    is-section-map-is-fibrant is-fibrant-Fibrant-Type

  is-retraction-map-Fibrant-Type :
    (map-Fibrant-Type ∘ᵉ map-inv-Fibrant-Type) ~ᵉ idᵉ
  is-retraction-map-Fibrant-Type =
    is-retraction-map-is-fibrant is-fibrant-Fibrant-Type
```

### Trivially Fibrant types

```agda
record is-trivially-fibrant {i : Level} (A : UUᵉ i) : UUᵉ (lsuc i) where
  field
    is-fibrant-is-trivially-fibrant : is-fibrant A
    is-contr-witness-is-trivially-fibrant :
      is-contr (witness-is-fibrant is-fibrant-is-trivially-fibrant)

  witness-is-trivially-fibrant : UU i
  witness-is-trivially-fibrant =
    witness-is-fibrant is-fibrant-is-trivially-fibrant

  equiv-witness-is-trivially-fibrant : coerce witness-is-trivially-fibrant ≃ᵉ A
  equiv-witness-is-trivially-fibrant = equiv-witness-is-fibrant is-fibrant-is-trivially-fibrant

  map-is-trivially-fibrant : coerce witness-is-trivially-fibrant → A
  map-is-trivially-fibrant = map-is-fibrant is-fibrant-is-trivially-fibrant

  map-inv-is-trivially-fibrant : A → coerce witness-is-trivially-fibrant
  map-inv-is-trivially-fibrant =
    map-inv-is-fibrant is-fibrant-is-trivially-fibrant

  is-section-map-is-trivially-fibrant :
    (map-inv-is-trivially-fibrant ∘ᵉ map-is-trivially-fibrant) ~ᵉ idᵉ
  is-section-map-is-trivially-fibrant =
    is-section-map-is-fibrant is-fibrant-is-trivially-fibrant

  is-retraction-map-is-trivially-fibrant :
    (map-is-trivially-fibrant ∘ᵉ map-inv-is-trivially-fibrant) ~ᵉ idᵉ
  is-retraction-map-is-trivially-fibrant =
    is-retraction-map-is-fibrant is-fibrant-is-trivially-fibrant

  center-is-trivially-fibrant : A
  center-is-trivially-fibrant =
    map-is-trivially-fibrant
      ( map-coerce (center is-contr-witness-is-trivially-fibrant))

open is-trivially-fibrant public

Trivially-Fibrant-Type : (l : Level) → UUᵉ (lsuc l)
Trivially-Fibrant-Type l = Σᵉ (UUᵉ l) (λ A → is-trivially-fibrant A)

module _
  {l : Level} (A : Trivially-Fibrant-Type l)
  where

  type-Trivially-Fibrant-Type : UUᵉ l
  type-Trivially-Fibrant-Type = pr1ᵉ A

  is-trivially-fibrant-Trivially-Fibrant-Type :
    is-trivially-fibrant type-Trivially-Fibrant-Type
  is-trivially-fibrant-Trivially-Fibrant-Type = pr2ᵉ A

  is-fibrant-Trivially-Fibrant-Type :
    is-fibrant type-Trivially-Fibrant-Type
  is-fibrant-Trivially-Fibrant-Type =
    is-fibrant-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  witness-Trivially-Fibrant-Type : UU l
  witness-Trivially-Fibrant-Type =
    witness-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  equiv-witness-Trivially-Fibrant-Type :
    coerce witness-Trivially-Fibrant-Type ≃ᵉ type-Trivially-Fibrant-Type
  equiv-witness-Trivially-Fibrant-Type =
    equiv-witness-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  map-Trivially-Fibrant-Type :
    coerce witness-Trivially-Fibrant-Type → type-Trivially-Fibrant-Type
  map-Trivially-Fibrant-Type =
    map-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  map-inv-Trivially-Fibrant-Type :
    type-Trivially-Fibrant-Type → coerce witness-Trivially-Fibrant-Type
  map-inv-Trivially-Fibrant-Type =
    map-inv-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  is-section-map-Trivially-Fibrant-Type :
    (map-inv-Trivially-Fibrant-Type ∘ᵉ map-Trivially-Fibrant-Type) ~ᵉ idᵉ
  is-section-map-Trivially-Fibrant-Type =
    is-section-map-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type

  is-retraction-map-Trivially-Fibrant-Type :
    (map-Trivially-Fibrant-Type ∘ᵉ map-inv-Trivially-Fibrant-Type) ~ᵉ idᵉ
  is-retraction-map-Trivially-Fibrant-Type =
    is-retraction-map-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type

  is-contr-Trivially-Fibrant-Type :
    is-contr witness-Trivially-Fibrant-Type
  is-contr-Trivially-Fibrant-Type =
    is-contr-witness-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type
```

## Properties

### Closure under isos

```agda
module _
  {l : Level} {A : UUᵉ l} {B : UUᵉ l}
  (is-fibrant-A : is-fibrant A) (e : A ≃ᵉ B)
  where

  is-fibrant-equivᵉ : is-fibrant B
  witness-is-fibrant is-fibrant-equivᵉ = witness-is-fibrant is-fibrant-A
  equiv-witness-is-fibrant is-fibrant-equivᵉ =
    comp-equivᵉ e (equiv-witness-is-fibrant is-fibrant-A)
```

### Closure under Σ

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  (is-fibrant-A : is-fibrant A) (is-fibrant-B : (a : A) → is-fibrant (B a))
  where

  witness-is-fibrant-Σᵉ :
    UU (l1 ⊔ l2)
  witness-is-fibrant-Σᵉ =
    Σ ( witness-is-fibrant is-fibrant-A)
      ( λ a →
        witness-is-fibrant
          ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a))))

  is-fibrant-Σᵉ :
    is-fibrant (Σᵉ A B)
  witness-is-fibrant is-fibrant-Σᵉ = witness-is-fibrant-Σᵉ
  equiv-witness-is-fibrant is-fibrant-Σᵉ =
    equiv-Σᵉ B
      ( equiv-witness-is-fibrant is-fibrant-A)
      ( λ {(map-coerce a) →
        equiv-witness-is-fibrant
          ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))}) ∘eᵉ
    inv-equivᵉ
      ( equiv-coerce-Σᵉ ( witness-is-fibrant is-fibrant-A)
        ( λ a → witness-is-fibrant
          ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))))

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  (is-trivially-fibrant-A : is-trivially-fibrant A)
  (is-trivially-fibrant-B : (a : A) → is-trivially-fibrant (B a))
  where

  witness-is-trivially-fibrant-Σᵉ :
    UU (l1 ⊔ l2)
  witness-is-trivially-fibrant-Σᵉ =
    Σ ( witness-is-trivially-fibrant is-trivially-fibrant-A)
      ( λ a →
        witness-is-trivially-fibrant
          ( is-trivially-fibrant-B
            ( map-is-trivially-fibrant is-trivially-fibrant-A (map-coerce a))))

  is-trivially-fibrant-Σᵉ :
    is-trivially-fibrant (Σᵉ A B)
  is-fibrant-is-trivially-fibrant is-trivially-fibrant-Σᵉ =
    is-fibrant-Σᵉ
      ( is-fibrant-is-trivially-fibrant is-trivially-fibrant-A)
      ( λ a → is-fibrant-is-trivially-fibrant (is-trivially-fibrant-B a))
  is-contr-witness-is-trivially-fibrant is-trivially-fibrant-Σᵉ =
    is-contr-Σ'
      ( is-contr-witness-is-trivially-fibrant is-trivially-fibrant-A)
      ( λ a →
        is-contr-witness-is-trivially-fibrant
          ( is-trivially-fibrant-B
            ( map-is-trivially-fibrant
              ( is-trivially-fibrant-A)
              ( map-coerce a))))
```

### Closure under Π

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  (is-fibrant-A : is-fibrant A) (is-fibrant-B : (a : A) → is-fibrant (B a))
  where

  witness-is-fibrant-Πᵉ :
    UU (l1 ⊔ l2)
  witness-is-fibrant-Πᵉ =
    ( a : witness-is-fibrant is-fibrant-A) →
    witness-is-fibrant
      ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))

  test : coerce witness-is-fibrant-Πᵉ → Πᵉ A B
  test (map-coerce f) a = {! (map-coerce (f (map-inv-coerce (map-inv-is-fibrant is-fibrant-A a)))) !}

  is-fibrant-Πᵉ' :
    is-fibrant (Πᵉ A B)
  witness-is-fibrant is-fibrant-Πᵉ' = witness-is-fibrant-Πᵉ
  equiv-witness-is-fibrant is-fibrant-Πᵉ' =
    {! is-equiv-is-invertibleᵉ
      ?
      ?
      ? !}

  is-fibrant-Πᵉ :
    is-fibrant (Πᵉ A B)
  witness-is-fibrant is-fibrant-Πᵉ = witness-is-fibrant-Πᵉ
  equiv-witness-is-fibrant is-fibrant-Πᵉ =
    equiv-Πᵉ B
      ( equiv-witness-is-fibrant is-fibrant-A)
      ( λ {(map-coerce a) →
        equiv-witness-is-fibrant
          ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))}) ∘eᵉ
    inv-equivᵉ
      ( equiv-coerce-Πᵉ ( witness-is-fibrant is-fibrant-A)
        ( λ a → witness-is-fibrant
          ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))))

type-Π-Fibrant-Type :
  {l1 l2 : Level}
  (A : Fibrant-Type l1) →
  (type-Fibrant-Type A → Fibrant-Type l2) →
  UUᵉ (l1 ⊔ l2)
type-Π-Fibrant-Type A B =
  (a : type-Fibrant-Type A) → type-Fibrant-Type (B a)

Π-Fibrant-Type :
  {l1 l2 : Level}
  (A : Fibrant-Type l1)
  (B : type-Fibrant-Type A → Fibrant-Type l2) →
  Fibrant-Type (l1 ⊔ l2)
pr1ᵉ (Π-Fibrant-Type A B) = type-Π-Fibrant-Type A B
pr2ᵉ (Π-Fibrant-Type A B) =
  is-fibrant-Πᵉ
    (is-fibrant-Fibrant-Type A)
    (λ a → is-fibrant-Fibrant-Type (B a))

witness-Π-Fibrant-Type :
  {l1 l2 : Level}
  (A : Fibrant-Type l1) →
  (type-Fibrant-Type A → Fibrant-Type l2) →
  UU (l1 ⊔ l2)
witness-Π-Fibrant-Type A B =
  witness-Fibrant-Type (Π-Fibrant-Type A B)

type-hom-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Fibrant-Type l2 →
  UUᵉ (l1 ⊔ l2)
type-hom-Fibrant-Type A B = type-Π-Fibrant-Type A (λ a → B)

hom-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Fibrant-Type l2 →
  Fibrant-Type (l1 ⊔ l2)
hom-Fibrant-Type A B = Π-Fibrant-Type A (λ a → B)

witness-hom-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Fibrant-Type l2 →
  UU (l1 ⊔ l2)
witness-hom-Fibrant-Type A B =
  witness-Fibrant-Type (Π-Fibrant-Type A (λ a → B))

-- Warning: This is not judgementally equal to the obvious map.
-- In fact it's probably hard to show that these two maps are equal.
-- If the obvious map is ever needed then `hom-Fibrant-Type` should
-- probably be defined in a different way.

induced-map-hom-Fibrant-Type :
  {l1 l2 : Level} →
  ( A : Fibrant-Type l1) →
  ( B : Fibrant-Type l2) →
  type-Fibrant-Type (hom-Fibrant-Type A B) →
  witness-Fibrant-Type A → witness-Fibrant-Type B
induced-map-hom-Fibrant-Type A B f =
  map-inv-coerce (map-inv-Fibrant-Type (hom-Fibrant-Type A B) f)

-- test :
--   {l1 l2 : Level} →
--   ( A : UUᵉ l1) →
--   ( H H' : is-fibrant A) →
--   is-equiv (induced-map-hom-Fibrant-Type (A ,ᵉ H) (A ,ᵉ H') idᵉ)
-- test A H H' =
--   is-equiv-is-invertible ( induced-map-hom-Fibrant-Type (A ,ᵉ H') (A ,ᵉ H) idᵉ) (λ a → {! !}) {!!}

record equiv-Fibrant-Type {l1 l2  : Level} (A : Fibrant-Type l1) (B : Fibrant-Type l2) : UUᵉ (l1 ⊔ l2) where
  field
    map-equiv-Fibrant-Type : type-Fibrant-Type A → type-Fibrant-Type B
    is-equiv-map-equiv-Fibrant-Type : is-equiv (induced-map-hom-Fibrant-Type A B map-equiv-Fibrant-Type)

infix 6 _≃ᶠ_
_≃ᶠ_ : {l1 l2  : Level} (A : Fibrant-Type l1) (B : Fibrant-Type l2) → UUᵉ (l1 ⊔ l2)
A ≃ᶠ B = equiv-Fibrant-Type A B

type-equiv-witness-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Fibrant-Type l2 →
  UU (l1 ⊔ l2)
type-equiv-witness-Fibrant-Type A B =
  witness-Fibrant-Type A ≃ witness-Fibrant-Type B

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : A → UUᵉ l2}
  (is-fibrant-A : is-fibrant A)
  (is-trivially-fibrant-B : (a : A) → is-trivially-fibrant (B a))
  where

  witness-is-trivially-fibrant-Πᵉ :
    UU (l1 ⊔ l2)
  witness-is-trivially-fibrant-Πᵉ =
    ( a : witness-is-fibrant is-fibrant-A) →
    witness-is-trivially-fibrant
      ( is-trivially-fibrant-B
        ( map-is-fibrant is-fibrant-A (map-coerce a)))

  is-trivially-fibrant-Πᵉ :
    is-trivially-fibrant (Πᵉ A B)
  is-fibrant-is-trivially-fibrant is-trivially-fibrant-Πᵉ =
    is-fibrant-Πᵉ
      ( is-fibrant-A)
      ( λ a → is-fibrant-is-trivially-fibrant (is-trivially-fibrant-B a))
  is-contr-witness-is-trivially-fibrant is-trivially-fibrant-Πᵉ =
    is-contr-Π
      ( λ a →
        is-contr-witness-is-trivially-fibrant
          ( is-trivially-fibrant-B
            ( map-is-fibrant is-fibrant-A (map-coerce a))))

type-Π-Trivially-Fibrant-Type :
  {l1 l2 : Level}
  (A : Fibrant-Type l1) →
  (type-Fibrant-Type A → Trivially-Fibrant-Type l2) →
  UUᵉ (l1 ⊔ l2)
type-Π-Trivially-Fibrant-Type A B =
  (a : type-Fibrant-Type A) → type-Trivially-Fibrant-Type (B a)

Π-Trivially-Fibrant-Type :
  {l1 l2 : Level}
  (A : Fibrant-Type l1)
  (B : type-Fibrant-Type A → Trivially-Fibrant-Type l2) →
  Trivially-Fibrant-Type (l1 ⊔ l2)
pr1ᵉ (Π-Trivially-Fibrant-Type A B) = type-Π-Trivially-Fibrant-Type A B
pr2ᵉ (Π-Trivially-Fibrant-Type A B) =
  is-trivially-fibrant-Πᵉ
    (is-fibrant-Fibrant-Type A)
    (λ a → is-trivially-fibrant-Trivially-Fibrant-Type (B a))

type-hom-Trivially-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Trivially-Fibrant-Type l2 →
  UUᵉ (l1 ⊔ l2)
type-hom-Trivially-Fibrant-Type A B = type-Π-Trivially-Fibrant-Type A (λ a → B)

hom-Trivially-Fibrant-Type :
  {l1 l2 : Level} →
  Fibrant-Type l1 →
  Trivially-Fibrant-Type l2 →
  Trivially-Fibrant-Type (l1 ⊔ l2)
hom-Trivially-Fibrant-Type A B = Π-Trivially-Fibrant-Type A (λ a → B)
```

## Examples

### The exo-unit is trivially fibrant

```agda
map-is-fibrant-unitᵉ : coerce unit → unitᵉ
map-is-fibrant-unitᵉ (map-coerce star) = starᵉ

map-inv-is-fibrant-unitᵉ : unitᵉ → coerce unit
map-inv-is-fibrant-unitᵉ starᵉ = map-coerce star

is-equiv-map-is-fibrant-unitᵉ : is-equivᵉ map-is-fibrant-unitᵉ
is-equiv-map-is-fibrant-unitᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-is-fibrant-unitᵉ
    ( λ { starᵉ → reflᵉ})
    ( λ { (map-coerce star) → reflᵉ})

equiv-witness-is-fibrant-unitᵉ : coerce unit ≃ᵉ unitᵉ
pr1ᵉ equiv-witness-is-fibrant-unitᵉ = map-is-fibrant-unitᵉ
pr2ᵉ equiv-witness-is-fibrant-unitᵉ = is-equiv-map-is-fibrant-unitᵉ

is-fibrant-unitᵉ : is-fibrant unitᵉ
witness-is-fibrant is-fibrant-unitᵉ = unit
equiv-witness-is-fibrant is-fibrant-unitᵉ = equiv-witness-is-fibrant-unitᵉ

unit-Fibrant-Type : Fibrant-Type lzero
pr1ᵉ unit-Fibrant-Type = unitᵉ
pr2ᵉ unit-Fibrant-Type = is-fibrant-unitᵉ

is-trivially-fibrant-unitᵉ : is-trivially-fibrant unitᵉ
is-fibrant-is-trivially-fibrant is-trivially-fibrant-unitᵉ = is-fibrant-unitᵉ
is-contr-witness-is-trivially-fibrant is-trivially-fibrant-unitᵉ = is-contr-unit

unit-Trivially-Fibrant-Type : Trivially-Fibrant-Type lzero
pr1ᵉ unit-Trivially-Fibrant-Type = unitᵉ
pr2ᵉ unit-Trivially-Fibrant-Type = is-trivially-fibrant-unitᵉ
```
