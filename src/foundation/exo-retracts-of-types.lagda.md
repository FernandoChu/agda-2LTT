# retractsᵉ of types

```agda
module foundation.exo-retracts-of-exo-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.precomposition-functions
open import foundation-core.retractionᵉs
open import foundation-core.sections
```

</details>

## Idea

We say that a type `A` is a
{{#concept "retract" Disambiguation="of types" Agda=retractsᵉ}} of a type `B` if
the types `A` and `B` come equipped with
{{#concept "retractᵉ data" Disambiguation="of types" Agda=retract}}, i.e., with
maps

```text
      i        r
  A -----> B -----> A
```

such that `r` is a [retractionᵉ](foundation-core.retractionᵉs.md) of `i`, i.e.,
there is a [homotopy](foundation-core.homotopies.md) `r ∘ i ~ id`. The map `i`
is called the **inclusion** of the retractᵉ data, and the map `r` is called the
**underlying map of the retractionᵉ**.

## Definitions

### The type of witnesses that `A` is a retractᵉ of `B`

The predicate `retractᵉ B` is used to assert that a type is a retractᵉ of `B`,
i.e., the type `retractᵉ B A` is the type of maps from `A` to `B` that come
equipped with a retractionᵉ.

We also introduce more intuitive infix notation `A retractᵉ-of B` to assert that
`A` is a retractᵉ of `B`.

```agda
retractᵉ : {l1 l2 : Level} → UUᵉ l1 → UUᵉ l2 → UUᵉ (l1 ⊔ l2)
retractᵉ B A = Σᵉ (A → B) (retractionᵉ)

infix 6 _retractᵉ-of_

_retractᵉ-of_ :
  {l1 l2 : Level} → UUᵉ l1 → UUᵉ l2 → UUᵉ (l1 ⊔ l2)
A retractᵉ-of B = retractᵉ B A

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (R : retractᵉ B A)
  where

  inclusion-retractᵉ : A → B
  inclusion-retractᵉ = pr1ᵉ R

  retractionᵉ-retractᵉ : retractionᵉ inclusion-retract
  retractionᵉ-retractᵉ = pr2ᵉ R

  map-retractionᵉ-retractᵉ : B → A
  map-retractionᵉ-retractᵉ = map-retractionᵉ inclusion-retractᵉ retractionᵉ-retract

  is-retractionᵉ-map-retractionᵉ-retractᵉ :
    is-section map-retractionᵉ-retractᵉ inclusion-retract
  is-retractionᵉ-map-retractionᵉ-retractᵉ =
    is-retractionᵉ-map-retractionᵉ inclusion-retractᵉ retractionᵉ-retract

  section-retractᵉ : section map-retractionᵉ-retract
  pr1ᵉ section-retractᵉ = inclusion-retract
  pr2ᵉ section-retractᵉ = is-retractionᵉ-map-retractionᵉ-retract
```

### The type of retractsᵉ of a type

```agda
retractsᵉ : {l1 : Level} (l2 : Level) (A : UUᵉ l1) → UUᵉ (l1 ⊔ lsuc l2)
retractsᵉ l2 A = Σᵉ (UUᵉ l2) (_retractᵉ-of A)

module _
  {l1 l2 : Level} {A : UUᵉ l1} (R : retractsᵉ l2 A)
  where

  type-retractsᵉ : UUᵉ l2
  type-retractsᵉ = pr1ᵉ R

  retractᵉ-retractsᵉ : type-retractsᵉ retractᵉ-of A
  retractᵉ-retractsᵉ = pr2ᵉ R

  inclusion-retractsᵉ : type-retractsᵉ → A
  inclusion-retractsᵉ = inclusion-retractᵉ retractᵉ-retractsᵉ

  retractionᵉ-retractsᵉ : retractionᵉ inclusion-retractsᵉ
  retractionᵉ-retractsᵉ = retractionᵉ-retractᵉ retractᵉ-retractsᵉ

  map-retractionᵉ-retractsᵉ : A → type-retractsᵉ
  map-retractionᵉ-retractsᵉ = map-retractionᵉ-retractᵉ retractᵉ-retractsᵉ

  is-retractionᵉ-map-retractionᵉ-retractsᵉ :
    is-section map-retractionᵉ-retractsᵉ inclusion-retractsᵉ
  is-retractionᵉ-map-retractionᵉ-retractsᵉ =
    is-retractionᵉ-map-retractionᵉ-retractᵉ retractᵉ-retractsᵉ

  section-retractsᵉ : section map-retractionᵉ-retractsᵉ
  section-retractsᵉ = section-retractᵉ retractᵉ-retractsᵉ
```

## Properties

### If `A` is a retractᵉ of `B` with inclusion `i : A → B`, then `x ＝ y` is a retractᵉ of `i x ＝ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (R : A retractᵉ-of B) (x y : A)
  where

  retractᵉ-eq :
    (x ＝ y) retractᵉ-of (inclusion-retractᵉ R x ＝ inclusion-retractᵉ R y)
  pr1ᵉ retractᵉ-eq = ap (inclusion-retractᵉ R)
  pr2ᵉ retractᵉ-eq = retractionᵉ-ap (inclusion-retractᵉ R) (retractionᵉ-retractᵉ R)
```

### If `A` is a retractᵉ of `B` then `A → S` is a retractᵉ of `B → S` via precomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (R : A retractᵉ-of B) (S : UUᵉ l3)
  where

  retractᵉ-precomp :
    (A → S) retractᵉ-of (B → S)
  pr1ᵉ retractᵉ-precomp =
    precomp (map-retractionᵉ-retractᵉ R) S
  pr1ᵉ (pr2ᵉ retractᵉ-precomp) =
    precomp (inclusion-retractᵉ R) S
  pr2ᵉ (pr2ᵉ retractᵉ-precomp) h =
    eq-htpy (h ·l is-retractionᵉ-map-retractionᵉ-retractᵉ R)
```

### If `A` is a retractᵉ of `B` then `S → A` is a retractᵉ of `S → B` via postcomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (S : UUᵉ l3) (R : A retractᵉ-of B)
  where

  retractᵉ-postcomp :
    (S → A) retractᵉ-of (S → B)
  pr1ᵉ retractᵉ-postcomp =
    postcomp S (inclusion-retractᵉ R)
  pr1ᵉ (pr2ᵉ retractᵉ-postcomp) =
    postcomp S (map-retractionᵉ-retractᵉ R)
  pr2ᵉ (pr2ᵉ retractᵉ-postcomp) h =
    eq-htpy (is-retractionᵉ-map-retractionᵉ-retractᵉ R ·r h)
```

### Composition of retractsᵉ

```agda
module _
  {l1 l2 l3 : Level} {A : UUᵉ l1} {B : UUᵉ l2} {C : UUᵉ l3}
  where

  comp-retractᵉ : B retractᵉ-of C → A retractᵉ-of B → A retractᵉ-of C
  pr1ᵉ (comp-retractᵉ r r') =
    inclusion-retractᵉ r ∘ inclusion-retractᵉ r'
  pr2ᵉ (comp-retractᵉ r r') =
    retractionᵉ-comp
      ( inclusion-retractᵉ r)
      ( inclusion-retractᵉ r')
      ( retractionᵉ-retractᵉ r)
      ( retractionᵉ-retractᵉ r')
```

## See also

- [retractsᵉ of maps](foundation.retractsᵉ-of-maps.md)
