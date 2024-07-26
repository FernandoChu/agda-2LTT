# Homomorphisms of monoids

```agda
module group-theory.homomorphisms-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.invertible-elements-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

**Homomorphisms**ᵉ betweenᵉ twoᵉ [monoids](group-theory.monoids.mdᵉ) areᵉ
[homomorphisms](group-theory.homomorphisms-semigroups.mdᵉ) betweenᵉ theirᵉ
underlyingᵉ [semigroups](group-theory.semigroups.mdᵉ) thatᵉ preserveᵉ theᵉ unitᵉ
element.ᵉ

## Definition

### Homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (M1ᵉ : Monoidᵉ l1ᵉ) (M2ᵉ : Monoidᵉ l2ᵉ)
  where

  preserves-unit-prop-hom-Semigroupᵉ :
    hom-Semigroupᵉ (semigroup-Monoidᵉ M1ᵉ) (semigroup-Monoidᵉ M2ᵉ) → Propᵉ l2ᵉ
  preserves-unit-prop-hom-Semigroupᵉ fᵉ =
    Id-Propᵉ
      ( set-Monoidᵉ M2ᵉ)
      ( map-hom-Semigroupᵉ
        ( semigroup-Monoidᵉ M1ᵉ)
        ( semigroup-Monoidᵉ M2ᵉ)
        ( fᵉ)
        ( unit-Monoidᵉ M1ᵉ))
      ( unit-Monoidᵉ M2ᵉ)

  preserves-unit-hom-Semigroupᵉ :
    hom-Semigroupᵉ (semigroup-Monoidᵉ M1ᵉ) (semigroup-Monoidᵉ M2ᵉ) → UUᵉ l2ᵉ
  preserves-unit-hom-Semigroupᵉ fᵉ =
    type-Propᵉ (preserves-unit-prop-hom-Semigroupᵉ fᵉ)

  is-prop-preserves-unit-hom-Semigroupᵉ :
    (fᵉ : hom-Semigroupᵉ (semigroup-Monoidᵉ M1ᵉ) (semigroup-Monoidᵉ M2ᵉ)) →
    is-propᵉ (preserves-unit-hom-Semigroupᵉ fᵉ)
  is-prop-preserves-unit-hom-Semigroupᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-unit-prop-hom-Semigroupᵉ fᵉ)

  preserves-unit-hom-prop-Semigroupᵉ :
    hom-Semigroupᵉ (semigroup-Monoidᵉ M1ᵉ) (semigroup-Monoidᵉ M2ᵉ) →
    Propᵉ l2ᵉ
  preserves-unit-hom-prop-Semigroupᵉ fᵉ =
    ( preserves-unit-hom-Semigroupᵉ fᵉ ,ᵉ
      is-prop-preserves-unit-hom-Semigroupᵉ fᵉ)

  hom-set-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Monoidᵉ =
    set-subsetᵉ
      ( hom-set-Semigroupᵉ (semigroup-Monoidᵉ M1ᵉ) (semigroup-Monoidᵉ M2ᵉ))
      ( preserves-unit-prop-hom-Semigroupᵉ)

  hom-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Monoidᵉ = type-Setᵉ hom-set-Monoidᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  hom-semigroup-hom-Monoidᵉ :
    hom-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ) (semigroup-Monoidᵉ Nᵉ)
  hom-semigroup-hom-Monoidᵉ = pr1ᵉ fᵉ

  map-hom-Monoidᵉ : type-Monoidᵉ Mᵉ → type-Monoidᵉ Nᵉ
  map-hom-Monoidᵉ =
    map-hom-Semigroupᵉ
      ( semigroup-Monoidᵉ Mᵉ)
      ( semigroup-Monoidᵉ Nᵉ)
      ( hom-semigroup-hom-Monoidᵉ)

  preserves-mul-hom-Monoidᵉ :
    preserves-mul-Semigroupᵉ
      ( semigroup-Monoidᵉ Mᵉ)
      ( semigroup-Monoidᵉ Nᵉ)
      ( map-hom-Monoidᵉ)
  preserves-mul-hom-Monoidᵉ =
    preserves-mul-hom-Semigroupᵉ
      ( semigroup-Monoidᵉ Mᵉ)
      ( semigroup-Monoidᵉ Nᵉ)
      ( hom-semigroup-hom-Monoidᵉ)

  preserves-unit-hom-Monoidᵉ :
    preserves-unit-hom-Semigroupᵉ Mᵉ Nᵉ hom-semigroup-hom-Monoidᵉ
  preserves-unit-hom-Monoidᵉ = pr2ᵉ fᵉ
```

### The identity homomorphism of monoids

```agda
preserves-unit-id-hom-Monoidᵉ :
  { lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) →
  preserves-unit-hom-Semigroupᵉ Mᵉ Mᵉ (id-hom-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ))
preserves-unit-id-hom-Monoidᵉ Mᵉ = reflᵉ

id-hom-Monoidᵉ :
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ) → hom-Monoidᵉ Mᵉ Mᵉ
pr1ᵉ (id-hom-Monoidᵉ Mᵉ) = id-hom-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
pr2ᵉ (id-hom-Monoidᵉ Mᵉ) = preserves-unit-id-hom-Monoidᵉ Mᵉ
```

### Composition of homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Kᵉ : Monoidᵉ l1ᵉ) (Lᵉ : Monoidᵉ l2ᵉ) (Mᵉ : Monoidᵉ l3ᵉ)
  where

  preserves-unit-comp-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Lᵉ Mᵉ) (fᵉ : hom-Monoidᵉ Kᵉ Lᵉ) →
    preserves-unit-hom-Semigroupᵉ Kᵉ Mᵉ
      ( comp-hom-Semigroupᵉ
        ( semigroup-Monoidᵉ Kᵉ)
        ( semigroup-Monoidᵉ Lᵉ)
        ( semigroup-Monoidᵉ Mᵉ)
        ( hom-semigroup-hom-Monoidᵉ Lᵉ Mᵉ gᵉ)
        ( hom-semigroup-hom-Monoidᵉ Kᵉ Lᵉ fᵉ))
  preserves-unit-comp-hom-Monoidᵉ gᵉ fᵉ =
    ( apᵉ (map-hom-Monoidᵉ Lᵉ Mᵉ gᵉ) (preserves-unit-hom-Monoidᵉ Kᵉ Lᵉ fᵉ)) ∙ᵉ
    ( preserves-unit-hom-Monoidᵉ Lᵉ Mᵉ gᵉ)

  comp-hom-Monoidᵉ :
    hom-Monoidᵉ Lᵉ Mᵉ → hom-Monoidᵉ Kᵉ Lᵉ → hom-Monoidᵉ Kᵉ Mᵉ
  pr1ᵉ (comp-hom-Monoidᵉ gᵉ fᵉ) =
    comp-hom-Semigroupᵉ
      ( semigroup-Monoidᵉ Kᵉ)
      ( semigroup-Monoidᵉ Lᵉ)
      ( semigroup-Monoidᵉ Mᵉ)
      ( hom-semigroup-hom-Monoidᵉ Lᵉ Mᵉ gᵉ)
      ( hom-semigroup-hom-Monoidᵉ Kᵉ Lᵉ fᵉ)
  pr2ᵉ (comp-hom-Monoidᵉ gᵉ fᵉ) =
    preserves-unit-comp-hom-Monoidᵉ gᵉ fᵉ
```

### Homotopies of homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  htpy-hom-Monoidᵉ : (fᵉ gᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Monoidᵉ fᵉ gᵉ =
    htpy-hom-Semigroupᵉ
      ( semigroup-Monoidᵉ Mᵉ)
      ( semigroup-Monoidᵉ Nᵉ)
      ( hom-semigroup-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
      ( hom-semigroup-hom-Monoidᵉ Mᵉ Nᵉ gᵉ)

  refl-htpy-hom-Monoidᵉ : (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → htpy-hom-Monoidᵉ fᵉ fᵉ
  refl-htpy-hom-Monoidᵉ fᵉ =
    refl-htpy-hom-Semigroupᵉ
      ( semigroup-Monoidᵉ Mᵉ)
      ( semigroup-Monoidᵉ Nᵉ)
      ( hom-semigroup-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  is-torsorial-htpy-hom-Monoidᵉ :
    is-torsorialᵉ (htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
  is-torsorial-htpy-hom-Monoidᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpy-hom-Semigroupᵉ
        ( semigroup-Monoidᵉ Mᵉ)
        ( semigroup-Monoidᵉ Nᵉ)
        ( hom-semigroup-hom-Monoidᵉ Mᵉ Nᵉ fᵉ))
      ( is-prop-preserves-unit-hom-Semigroupᵉ Mᵉ Nᵉ)
      ( hom-semigroup-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
      ( refl-htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
      ( preserves-unit-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)

  htpy-eq-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → fᵉ ＝ᵉ gᵉ → htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ
  htpy-eq-hom-Monoidᵉ .fᵉ reflᵉ = refl-htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ

  is-equiv-htpy-eq-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → is-equivᵉ (htpy-eq-hom-Monoidᵉ gᵉ)
  is-equiv-htpy-eq-hom-Monoidᵉ =
    fundamental-theorem-idᵉ is-torsorial-htpy-hom-Monoidᵉ htpy-eq-hom-Monoidᵉ

  extensionality-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Monoidᵉ gᵉ) = htpy-eq-hom-Monoidᵉ gᵉ
  pr2ᵉ (extensionality-hom-Monoidᵉ gᵉ) = is-equiv-htpy-eq-hom-Monoidᵉ gᵉ

  eq-htpy-hom-Monoidᵉ :
    (gᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → htpy-hom-Monoidᵉ Mᵉ Nᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Monoidᵉ gᵉ = map-inv-equivᵉ (extensionality-hom-Monoidᵉ gᵉ)
```

### Associativity of composition of homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Kᵉ : Monoidᵉ l1ᵉ) (Lᵉ : Monoidᵉ l2ᵉ) (Mᵉ : Monoidᵉ l3ᵉ) (Nᵉ : Monoidᵉ l4ᵉ)
  where

  associative-comp-hom-Monoidᵉ :
    (hᵉ : hom-Monoidᵉ Mᵉ Nᵉ) (gᵉ : hom-Monoidᵉ Lᵉ Mᵉ) (fᵉ : hom-Monoidᵉ Kᵉ Lᵉ) →
    comp-hom-Monoidᵉ Kᵉ Lᵉ Nᵉ (comp-hom-Monoidᵉ Lᵉ Mᵉ Nᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Monoidᵉ Kᵉ Mᵉ Nᵉ hᵉ (comp-hom-Monoidᵉ Kᵉ Lᵉ Mᵉ gᵉ fᵉ)
  associative-comp-hom-Monoidᵉ hᵉ gᵉ fᵉ =
    eq-htpy-hom-Monoidᵉ Kᵉ Nᵉ
      ( comp-hom-Monoidᵉ Kᵉ Lᵉ Nᵉ (comp-hom-Monoidᵉ Lᵉ Mᵉ Nᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Monoidᵉ Kᵉ Mᵉ Nᵉ hᵉ (comp-hom-Monoidᵉ Kᵉ Lᵉ Mᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)
```

### Unit laws for composition of homomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  left-unit-law-comp-hom-Monoidᵉ :
    (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) →
    comp-hom-Monoidᵉ Mᵉ Nᵉ Nᵉ (id-hom-Monoidᵉ Nᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Monoidᵉ fᵉ =
    eq-htpy-hom-Monoidᵉ Mᵉ Nᵉ
      ( comp-hom-Monoidᵉ Mᵉ Nᵉ Nᵉ (id-hom-Monoidᵉ Nᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-hom-Monoidᵉ :
    (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) →
    comp-hom-Monoidᵉ Mᵉ Mᵉ Nᵉ fᵉ (id-hom-Monoidᵉ Mᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Monoidᵉ fᵉ =
    eq-htpy-hom-Monoidᵉ Mᵉ Nᵉ
      ( comp-hom-Monoidᵉ Mᵉ Mᵉ Nᵉ fᵉ (id-hom-Monoidᵉ Mᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)
```

### Any homomorphism of monoids sends invertible elements to invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  preserves-invertible-elements-hom-Monoidᵉ :
    {xᵉ : type-Monoidᵉ Mᵉ} →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-invertible-element-Monoidᵉ Nᵉ (map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ xᵉ)
  pr1ᵉ (preserves-invertible-elements-hom-Monoidᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ)) =
    map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ yᵉ
  pr1ᵉ (pr2ᵉ (preserves-invertible-elements-hom-Monoidᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) =
    ( invᵉ (preserves-mul-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)) ∙ᵉ
    ( apᵉ (map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ) pᵉ) ∙ᵉ
    ( preserves-unit-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
  pr2ᵉ (pr2ᵉ (preserves-invertible-elements-hom-Monoidᵉ (yᵉ ,ᵉ pᵉ ,ᵉ qᵉ))) =
    ( invᵉ (preserves-mul-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)) ∙ᵉ
    ( apᵉ (map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ) qᵉ) ∙ᵉ
    ( preserves-unit-hom-Monoidᵉ Mᵉ Nᵉ fᵉ)
```