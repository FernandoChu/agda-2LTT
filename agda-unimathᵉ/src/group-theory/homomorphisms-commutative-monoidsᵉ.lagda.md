# Homomorphisms of commutative monoids

```agda
module group-theory.homomorphisms-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
```

</details>

## Idea

Homomorphismsᵉ betweenᵉ twoᵉ commutativeᵉ monoidsᵉ areᵉ homomorphismsᵉ betweenᵉ theirᵉ
underlyingᵉ monoids.ᵉ

## Definition

### Homomorphisms of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (M1ᵉ : Commutative-Monoidᵉ l1ᵉ) (M2ᵉ : Commutative-Monoidᵉ l2ᵉ)
  where

  hom-set-Commutative-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Commutative-Monoidᵉ =
    hom-set-Monoidᵉ (monoid-Commutative-Monoidᵉ M1ᵉ) (monoid-Commutative-Monoidᵉ M2ᵉ)

  hom-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Commutative-Monoidᵉ =
    hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ M1ᵉ)
      ( monoid-Commutative-Monoidᵉ M2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Monoidᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ)
  where

  hom-semigroup-hom-Commutative-Monoidᵉ :
    hom-Semigroupᵉ
      ( semigroup-Commutative-Monoidᵉ Mᵉ)
      ( semigroup-Commutative-Monoidᵉ Nᵉ)
  hom-semigroup-hom-Commutative-Monoidᵉ =
    hom-semigroup-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  map-hom-Commutative-Monoidᵉ :
    type-Commutative-Monoidᵉ Mᵉ → type-Commutative-Monoidᵉ Nᵉ
  map-hom-Commutative-Monoidᵉ =
    map-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  preserves-mul-hom-Commutative-Monoidᵉ :
    preserves-mul-Semigroupᵉ
      ( semigroup-Commutative-Monoidᵉ Mᵉ)
      ( semigroup-Commutative-Monoidᵉ Nᵉ)
      ( map-hom-Commutative-Monoidᵉ)
  preserves-mul-hom-Commutative-Monoidᵉ =
    preserves-mul-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  preserves-unit-hom-Commutative-Monoidᵉ :
    preserves-unit-hom-Semigroupᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( hom-semigroup-hom-Commutative-Monoidᵉ)
  preserves-unit-hom-Commutative-Monoidᵉ =
    preserves-unit-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)
```

### The identity homomorphism of commutative monoids

```agda
id-hom-Commutative-Monoidᵉ :
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ) → hom-Commutative-Monoidᵉ Mᵉ Mᵉ
id-hom-Commutative-Monoidᵉ Mᵉ = id-hom-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### Composition of homomorphisms of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Kᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Lᵉ : Commutative-Monoidᵉ l2ᵉ)
  (Mᵉ : Commutative-Monoidᵉ l3ᵉ)
  where

  comp-hom-Commutative-Monoidᵉ :
    hom-Commutative-Monoidᵉ Lᵉ Mᵉ → hom-Commutative-Monoidᵉ Kᵉ Lᵉ →
    hom-Commutative-Monoidᵉ Kᵉ Mᵉ
  comp-hom-Commutative-Monoidᵉ =
    comp-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Kᵉ)
      ( monoid-Commutative-Monoidᵉ Lᵉ)
      ( monoid-Commutative-Monoidᵉ Mᵉ)
```

### Homotopies of homomorphisms of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Monoidᵉ l2ᵉ)
  where

  htpy-hom-Commutative-Monoidᵉ :
    (fᵉ gᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Commutative-Monoidᵉ =
    htpy-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)

  refl-htpy-hom-Commutative-Monoidᵉ :
    (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) → htpy-hom-Commutative-Monoidᵉ fᵉ fᵉ
  refl-htpy-hom-Commutative-Monoidᵉ =
    refl-htpy-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Monoidᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ)
  where

  is-torsorial-htpy-hom-Commutative-Monoidᵉ :
    is-torsorialᵉ (htpy-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ)
  is-torsorial-htpy-hom-Commutative-Monoidᵉ =
    is-torsorial-htpy-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  htpy-eq-hom-Commutative-Monoidᵉ :
    (gᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ
  htpy-eq-hom-Commutative-Monoidᵉ =
    htpy-eq-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Commutative-Monoidᵉ :
    (gᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    is-equivᵉ (htpy-eq-hom-Commutative-Monoidᵉ gᵉ)
  is-equiv-htpy-eq-hom-Commutative-Monoidᵉ =
    is-equiv-htpy-eq-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  extensionality-hom-Commutative-Monoidᵉ :
    (gᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ
  extensionality-hom-Commutative-Monoidᵉ =
    extensionality-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)

  eq-htpy-hom-Commutative-Monoidᵉ :
    (gᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    htpy-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Commutative-Monoidᵉ =
    eq-htpy-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)
```

### Composition of homomorphisms of commutative monoids is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Kᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Lᵉ : Commutative-Monoidᵉ l2ᵉ)
  (Mᵉ : Commutative-Monoidᵉ l3ᵉ)
  (Nᵉ : Commutative-Monoidᵉ l4ᵉ)
  where

  associative-comp-hom-Commutative-Monoidᵉ :
    (hᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ)
    (gᵉ : hom-Commutative-Monoidᵉ Lᵉ Mᵉ)
    (fᵉ : hom-Commutative-Monoidᵉ Kᵉ Lᵉ) →
    comp-hom-Commutative-Monoidᵉ Kᵉ Lᵉ Nᵉ
      ( comp-hom-Commutative-Monoidᵉ Lᵉ Mᵉ Nᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Commutative-Monoidᵉ Kᵉ Mᵉ Nᵉ
      ( hᵉ)
      ( comp-hom-Commutative-Monoidᵉ Kᵉ Lᵉ Mᵉ gᵉ fᵉ)
  associative-comp-hom-Commutative-Monoidᵉ =
    associative-comp-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Kᵉ)
      ( monoid-Commutative-Monoidᵉ Lᵉ)
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
```

### The unit laws for composition of homomorphisms of commutative monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Monoidᵉ l2ᵉ)
  where

  left-unit-law-comp-hom-Commutative-Monoidᵉ :
    (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    comp-hom-Commutative-Monoidᵉ Mᵉ Nᵉ Nᵉ (id-hom-Commutative-Monoidᵉ Nᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Commutative-Monoidᵉ =
    left-unit-law-comp-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)

  right-unit-law-comp-hom-Commutative-Monoidᵉ :
    (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ) →
    comp-hom-Commutative-Monoidᵉ Mᵉ Mᵉ Nᵉ fᵉ (id-hom-Commutative-Monoidᵉ Mᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Commutative-Monoidᵉ =
    right-unit-law-comp-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
```