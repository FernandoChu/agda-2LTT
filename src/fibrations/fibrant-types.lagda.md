# Fibrant exo-types

```agda
module fibrations.fibrant-types where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.equivalencesᵉ

open import coercions.coercing-inner-types
```

## Idea

## Definition

### Fibrant types

```agda
record is-fibrant {i : Level} (A : UUᵉ i) : UUᵉ (lsuc i) where
  field
    witness-is-fibrant : UU i
    equivᵉ-is-fibrant : coerce witness-is-fibrant ≃ᵉ A

  map-is-fibrant : coerce witness-is-fibrant → A
  map-is-fibrant = map-equivᵉ equivᵉ-is-fibrant

  is-equivᵉ-map-is-fibrant : is-equivᵉ map-is-fibrant
  is-equivᵉ-map-is-fibrant = is-equiv-map-equivᵉ equivᵉ-is-fibrant

  map-inv-is-fibrant : A → coerce witness-is-fibrant
  map-inv-is-fibrant = map-inv-equivᵉ equivᵉ-is-fibrant

  is-sectionᵉ-map-is-fibrant : (map-inv-is-fibrant ∘ᵉ map-is-fibrant) ~ᵉ idᵉ
  is-sectionᵉ-map-is-fibrant = is-retraction-map-inv-equivᵉ equivᵉ-is-fibrant

  is-retractionᵉ-map-is-fibrant : (map-is-fibrant ∘ᵉ map-inv-is-fibrant) ~ᵉ idᵉ
  is-retractionᵉ-map-is-fibrant = is-section-map-inv-equivᵉ equivᵉ-is-fibrant

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

  equivᵉ-Fibrant-Type : coerce witness-Fibrant-Type ≃ᵉ type-Fibrant-Type
  equivᵉ-Fibrant-Type = equivᵉ-is-fibrant is-fibrant-Fibrant-Type

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

  equivᵉ-is-trivially-fibrant : coerce witness-is-trivially-fibrant ≃ᵉ A
  equivᵉ-is-trivially-fibrant = equivᵉ-is-fibrant is-fibrant-is-trivially-fibrant

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

  equivᵉ-Trivially-Fibrant-Type :
    coerce witness-Trivially-Fibrant-Type ≃ᵉ type-Trivially-Fibrant-Type
  equivᵉ-Trivially-Fibrant-Type =
    equivᵉ-is-trivially-fibrant is-trivially-fibrant-Trivially-Fibrant-Type

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
map-is-fibrant-unitᵉ : coerce unit → unitᵉ
map-is-fibrant-unitᵉ (map-coerce star) = starᵉ

map-inv-is-fibrant-unitᵉ : unitᵉ → coerce unit
map-inv-is-fibrant-unitᵉ starᵉ = map-coerce star

is-equivᵉ-map-is-fibrant-unitᵉ : is-equivᵉ map-is-fibrant-unitᵉ
is-equivᵉ-map-is-fibrant-unitᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-is-fibrant-unitᵉ
    ( λ { starᵉ → reflᵉ })
    ( λ { (map-coerce star) → reflᵉ })

equivᵉ-is-fibrant-unitᵉ : coerce unit ≃ᵉ unitᵉ
pr1ᵉ equivᵉ-is-fibrant-unitᵉ = map-is-fibrant-unitᵉ
pr2ᵉ equivᵉ-is-fibrant-unitᵉ = is-equivᵉ-map-is-fibrant-unitᵉ

is-fibrant-unitᵉ : is-fibrant unitᵉ
witness-is-fibrant is-fibrant-unitᵉ = unit
equivᵉ-is-fibrant is-fibrant-unitᵉ = equivᵉ-is-fibrant-unitᵉ

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
  (is-fibrant-A : is-fibrant A) (e : A ≃ᵉ B)
  where

  is-fibrant-equivᵉ : is-fibrant B
  witness-is-fibrant is-fibrant-equivᵉ = witness-is-fibrant is-fibrant-A
  equivᵉ-is-fibrant is-fibrant-equivᵉ = comp-equivᵉ  e (equivᵉ-is-fibrant is-fibrant-A)
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
  equivᵉ-is-fibrant is-fibrant-Σᵉ =
    comp-equivᵉ lemma1 (inv-equivᵉ lemma2)
    where
    Bf : (witness-is-fibrant is-fibrant-A) → UU l2
    Bf a =
      witness-is-fibrant
        ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))
    lemma2 :
      Σᵉ-coerce (witness-is-fibrant is-fibrant-A) Bf
        ≃ᵉ coerce witness-is-fibrant-Σᵉ
    lemma2 = equivᵉ-coerce-Σᵉ ( witness-is-fibrant is-fibrant-A) Bf
    lemma1 :
      Σᵉ-coerce (witness-is-fibrant is-fibrant-A) Bf
        ≃ᵉ Σᵉ A B
    lemma1 =
      equiv-Σᵉ B
        ( equivᵉ-is-fibrant is-fibrant-A)
        ( λ {(map-coerce a) →
          equivᵉ-is-fibrant
            ( is-fibrant-B (map-is-fibrant is-fibrant-A (map-coerce a)))})
```
