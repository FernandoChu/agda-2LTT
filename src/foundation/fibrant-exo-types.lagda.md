# Fibrant exo-types

```agda
module foundation.fibrant-exo-types where

open import foundation.functoriality-exo-dependent-pair-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.exo-function-types
open import foundation.exo-unit-type
open import foundation.unit-type
open import foundation.coercing-inner-types
open import foundation.exo-homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types
open import foundation.exo-universes
open import foundation.exo-isomorphisms
```

## Idea

## Definition

### Fibrant types

```agda
record is-fibrant {i : Level} (A : UUᵉ i) : UUᵉ (lsuc i) where
  field
    witness-is-fibrant : UU i
    iso-is-fibrant : coerce witness-is-fibrant ≅ᵉ A

  map-is-fibrant : coerce witness-is-fibrant → A
  map-is-fibrant = map-exo-iso iso-is-fibrant

  is-iso-map-is-fibrant : is-exo-iso map-is-fibrant
  is-iso-map-is-fibrant = is-exo-iso-map-exo-iso iso-is-fibrant

  map-inv-is-fibrant : A → coerce witness-is-fibrant
  map-inv-is-fibrant = map-inv-exo-iso iso-is-fibrant

  is-sectionᵉ-map-is-fibrant : (map-inv-is-fibrant ∘ᵉ map-is-fibrant) ~ᵉ idᵉ
  is-sectionᵉ-map-is-fibrant = is-sectionᵉ-map-exo-iso iso-is-fibrant

  is-retractionᵉ-map-is-fibrant : (map-is-fibrant ∘ᵉ map-inv-is-fibrant) ~ᵉ idᵉ
  is-retractionᵉ-map-is-fibrant = is-retractionᵉ-map-exo-iso iso-is-fibrant

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

  iso-Fibrant-Type : coerce witness-Fibrant-Type ≅ᵉ type-Fibrant-Type
  iso-Fibrant-Type = iso-is-fibrant is-fibrant-Fibrant-Type

  map-Fibrant-Type : coerce witness-Fibrant-Type → type-Fibrant-Type
  map-Fibrant-Type = map-is-fibrant is-fibrant-Fibrant-Type

  map-inv-Fibrant-Type : type-Fibrant-Type → coerce witness-Fibrant-Type
  map-inv-Fibrant-Type = map-inv-is-fibrant is-fibrant-Fibrant-Type

  is-sectionᵉ-map-Fibrant-Type :
    (map-inv-Fibrant-Type ∘ᵉ map-Fibrant-Type) ~ᵉ idᵉ
  is-sectionᵉ-map-Fibrant-Type =
    is-sectionᵉ-map-is-fibrant is-fibrant-Fibrant-Type

  is-retractionᵉ-map-Fibrant-Type :
    (map-Fibrant-Type ∘ᵉ map-inv-Fibrant-Type) ~ᵉ idᵉ
  is-retractionᵉ-map-Fibrant-Type =
    is-retractionᵉ-map-is-fibrant is-fibrant-Fibrant-Type
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

  iso-is-trivially-fibrant : coerce witness-is-trivially-fibrant ≅ᵉ A
  iso-is-trivially-fibrant = iso-is-fibrant is-fibrant-is-trivially-fibrant

  map-is-trivially-fibrant : coerce witness-is-trivially-fibrant → A
  map-is-trivially-fibrant = map-is-fibrant is-fibrant-is-trivially-fibrant

  map-inv-is-trivially-fibrant : A → coerce witness-is-trivially-fibrant
  map-inv-is-trivially-fibrant =
    map-inv-is-fibrant is-fibrant-is-trivially-fibrant

  is-sectionᵉ-map-is-trivially-fibrant :
    (map-inv-is-trivially-fibrant ∘ᵉ map-is-trivially-fibrant) ~ᵉ idᵉ
  is-sectionᵉ-map-is-trivially-fibrant =
    is-sectionᵉ-map-is-fibrant is-fibrant-is-trivially-fibrant

  is-retractionᵉ-map-is-trivially-fibrant :
    (map-is-trivially-fibrant ∘ᵉ map-inv-is-trivially-fibrant) ~ᵉ idᵉ
  is-retractionᵉ-map-is-trivially-fibrant =
    is-retractionᵉ-map-is-fibrant is-fibrant-is-trivially-fibrant

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

  iso-Trivially-Fibrant-Type :
    coerce witness-Trivially-Fibrant-Type ≅ᵉ type-Trivially-Fibrant-Type
  iso-Trivially-Fibrant-Type =
    iso-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  map-Trivially-Fibrant-Type :
    coerce witness-Trivially-Fibrant-Type → type-Trivially-Fibrant-Type
  map-Trivially-Fibrant-Type =
    map-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  map-inv-Trivially-Fibrant-Type :
    type-Trivially-Fibrant-Type → coerce witness-Trivially-Fibrant-Type
  map-inv-Trivially-Fibrant-Type =
    map-inv-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

  is-sectionᵉ-map-Trivially-Fibrant-Type :
    (map-inv-Trivially-Fibrant-Type ∘ᵉ map-Trivially-Fibrant-Type) ~ᵉ idᵉ
  is-sectionᵉ-map-Trivially-Fibrant-Type =
    is-sectionᵉ-map-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type

  is-retractionᵉ-map-Trivially-Fibrant-Type :
    (map-Trivially-Fibrant-Type ∘ᵉ map-inv-Trivially-Fibrant-Type) ~ᵉ idᵉ
  is-retractionᵉ-map-Trivially-Fibrant-Type =
    is-retractionᵉ-map-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type

  is-contr-Trivially-Fibrant-Type :
    is-contr witness-Trivially-Fibrant-Type
  is-contr-Trivially-Fibrant-Type =
    is-contr-witness-is-trivially-fibrant
      is-trivially-fibrant-Trivially-Fibrant-Type
```

## Examples

### The exo-unit is trivially fibrant

```agda
iso-is-fibrant-unitᵉ : coerce unit ≅ᵉ unitᵉ
pr1ᵉ iso-is-fibrant-unitᵉ (map-coerce star) = starᵉ
pr1ᵉ (pr2ᵉ iso-is-fibrant-unitᵉ) starᵉ = map-coerce star
pr1ᵉ (pr2ᵉ (pr2ᵉ iso-is-fibrant-unitᵉ)) starᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ iso-is-fibrant-unitᵉ)) (map-coerce star) = reflᵉ

is-fibrant-unitᵉ : is-fibrant unitᵉ
witness-is-fibrant is-fibrant-unitᵉ = unit
iso-is-fibrant is-fibrant-unitᵉ = iso-is-fibrant-unitᵉ

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

## Properties

### Closure under isos

```agda
module _
  {l : Level} {A : UUᵉ l} {B : UUᵉ l}
  (is-fibrant-A : is-fibrant A) (e : A ≅ᵉ B)
  where

  is-fibrant-exo-iso : is-fibrant B
  witness-is-fibrant is-fibrant-exo-iso = witness-is-fibrant is-fibrant-A
  iso-is-fibrant is-fibrant-exo-iso = comp-exo-iso e (iso-is-fibrant is-fibrant-A)
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
  iso-is-fibrant is-fibrant-Σᵉ =
    comp-exo-iso lemma1 (inv-exo-iso lemma2)
    where
    Bf : (witness-is-fibrant is-fibrant-A) → UU l2
    Bf a =
      witness-is-fibrant
        ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))
    lemma2 :
      Σᵉ-coerce (witness-is-fibrant is-fibrant-A) Bf
        ≅ᵉ coerce witness-is-fibrant-Σᵉ
    lemma2 = exo-iso-coerce-Σᵉ ( witness-is-fibrant is-fibrant-A) Bf
    lemma1 :
      Σᵉ-coerce (witness-is-fibrant is-fibrant-A) Bf
        ≅ᵉ Σᵉ A B
    lemma1 =
      exo-iso-Σᵉ B
        ( iso-is-fibrant is-fibrant-A)
        ( λ {(map-coerce a) →
          iso-is-fibrant
            ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))})
```
