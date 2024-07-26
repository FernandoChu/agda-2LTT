# Homomorphisms of finite rings

```agda
module finite-algebra.homomorphisms-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-ringsᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ

open import ring-theory.homomorphisms-ringsᵉ
```

</details>

## Idea

Ringᵉ homomorphismsᵉ areᵉ mapsᵉ betweenᵉ ringsᵉ thatᵉ preserveᵉ theᵉ ringᵉ structureᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  where

  is-finite-ring-homomorphism-hom-Ab-Propᵉ :
    hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ) (ab-Ring-𝔽ᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-ring-homomorphism-hom-Ab-Propᵉ =
    is-ring-homomorphism-hom-Ab-Propᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)

  is-finite-ring-homomorphism-hom-Abᵉ :
    hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ) (ab-Ring-𝔽ᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-ring-homomorphism-hom-Abᵉ =
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)

  is-prop-is-finite-ring-homomorphism-hom-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ) (ab-Ring-𝔽ᵉ Bᵉ)) →
    is-propᵉ (is-finite-ring-homomorphism-hom-Abᵉ fᵉ)
  is-prop-is-finite-ring-homomorphism-hom-Abᵉ =
    is-prop-is-ring-homomorphism-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  where

  hom-set-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Ring-𝔽ᵉ =
    hom-set-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ) (ring-Ring-𝔽ᵉ Bᵉ)

  hom-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Ring-𝔽ᵉ =
    hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ) (ring-Ring-𝔽ᵉ Bᵉ)

  is-set-hom-Ring-𝔽ᵉ : is-setᵉ hom-Ring-𝔽ᵉ
  is-set-hom-Ring-𝔽ᵉ =
    is-set-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ) (ring-Ring-𝔽ᵉ Bᵉ)

  module _
    (fᵉ : hom-Ring-𝔽ᵉ)
    where

    hom-ab-hom-Ring-𝔽ᵉ :
      hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ) (ab-Ring-𝔽ᵉ Bᵉ)
    hom-ab-hom-Ring-𝔽ᵉ =
      hom-ab-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ) (ring-Ring-𝔽ᵉ Bᵉ) fᵉ

    hom-multiplicative-monoid-hom-Ring-𝔽ᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Ring-𝔽ᵉ Aᵉ)
        ( multiplicative-monoid-Ring-𝔽ᵉ Bᵉ)
    hom-multiplicative-monoid-hom-Ring-𝔽ᵉ =
      hom-multiplicative-monoid-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    map-hom-Ring-𝔽ᵉ : type-Ring-𝔽ᵉ Aᵉ → type-Ring-𝔽ᵉ Bᵉ
    map-hom-Ring-𝔽ᵉ =
      map-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-add-hom-Ring-𝔽ᵉ :
      preserves-add-Abᵉ
        ( ab-Ring-𝔽ᵉ Aᵉ)
        ( ab-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Ring-𝔽ᵉ)
    preserves-add-hom-Ring-𝔽ᵉ =
      preserves-add-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-zero-hom-Ring-𝔽ᵉ :
      preserves-zero-Abᵉ
        ( ab-Ring-𝔽ᵉ Aᵉ)
        ( ab-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Ring-𝔽ᵉ)
    preserves-zero-hom-Ring-𝔽ᵉ =
      preserves-zero-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-neg-hom-Ring-𝔽ᵉ :
      preserves-negatives-Abᵉ
        ( ab-Ring-𝔽ᵉ Aᵉ)
        ( ab-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Ring-𝔽ᵉ)
    preserves-neg-hom-Ring-𝔽ᵉ =
      preserves-neg-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-mul-hom-Ring-𝔽ᵉ :
      preserves-mul-hom-Abᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( hom-ab-hom-Ring-𝔽ᵉ)
    preserves-mul-hom-Ring-𝔽ᵉ =
      preserves-mul-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-one-hom-Ring-𝔽ᵉ :
      preserves-unit-hom-Abᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( hom-ab-hom-Ring-𝔽ᵉ)
    preserves-one-hom-Ring-𝔽ᵉ =
      preserves-one-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    is-finite-ring-homomorphism-hom-Ring-𝔽ᵉ :
      is-finite-ring-homomorphism-hom-Abᵉ Aᵉ Bᵉ hom-ab-hom-Ring-𝔽ᵉ
    is-finite-ring-homomorphism-hom-Ring-𝔽ᵉ =
      is-ring-homomorphism-hom-Ringᵉ
        ( ring-Ring-𝔽ᵉ Aᵉ)
        ( ring-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)
```

### The identity homomorphism of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Ring-𝔽ᵉ lᵉ)
  where

  preserves-mul-id-hom-Ring-𝔽ᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ))
  preserves-mul-id-hom-Ring-𝔽ᵉ =
    preserves-mul-id-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ)

  preserves-unit-id-hom-Ring-𝔽ᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ))
  preserves-unit-id-hom-Ring-𝔽ᵉ =
    preserves-unit-id-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ)

  is-ring-homomorphism-id-hom-Ring-𝔽ᵉ :
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ))
  is-ring-homomorphism-id-hom-Ring-𝔽ᵉ =
    is-ring-homomorphism-id-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ)

  id-hom-Ring-𝔽ᵉ : hom-Ring-𝔽ᵉ Aᵉ Aᵉ
  id-hom-Ring-𝔽ᵉ = id-hom-Ringᵉ (ring-Ring-𝔽ᵉ Aᵉ)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Ring-𝔽ᵉ l2ᵉ) (Cᵉ : Ring-𝔽ᵉ l3ᵉ)
  (gᵉ : hom-Ring-𝔽ᵉ Bᵉ Cᵉ) (fᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  hom-ab-comp-hom-Ring-𝔽ᵉ :
    hom-Abᵉ (ab-Ring-𝔽ᵉ Aᵉ) (ab-Ring-𝔽ᵉ Cᵉ)
  hom-ab-comp-hom-Ring-𝔽ᵉ =
    hom-ab-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  hom-multiplicative-monoid-comp-hom-Ring-𝔽ᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Ring-𝔽ᵉ Aᵉ)
      ( multiplicative-monoid-Ring-𝔽ᵉ Cᵉ)
  hom-multiplicative-monoid-comp-hom-Ring-𝔽ᵉ =
    hom-multiplicative-monoid-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-mul-comp-hom-Ring-𝔽ᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( hom-ab-comp-hom-Ring-𝔽ᵉ)
  preserves-mul-comp-hom-Ring-𝔽ᵉ =
    preserves-mul-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-unit-comp-hom-Ring-𝔽ᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( hom-ab-comp-hom-Ring-𝔽ᵉ)
  preserves-unit-comp-hom-Ring-𝔽ᵉ =
    preserves-unit-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  is-finite-ring-homomorphism-comp-hom-Ring-𝔽ᵉ :
    is-finite-ring-homomorphism-hom-Abᵉ Aᵉ Cᵉ
      ( hom-ab-comp-hom-Ring-𝔽ᵉ)
  is-finite-ring-homomorphism-comp-hom-Ring-𝔽ᵉ =
    is-ring-homomorphism-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Ring-𝔽ᵉ : hom-Ring-𝔽ᵉ Aᵉ Cᵉ
  comp-hom-Ring-𝔽ᵉ =
    comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  where

  htpy-hom-Ring-𝔽ᵉ :
    hom-Ring-𝔽ᵉ Aᵉ Bᵉ → hom-Ring-𝔽ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Ring-𝔽ᵉ =
    htpy-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)

  refl-htpy-hom-Ring-𝔽ᵉ :
    (fᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ) → htpy-hom-Ring-𝔽ᵉ fᵉ fᵉ
  refl-htpy-hom-Ring-𝔽ᵉ =
    refl-htpy-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  (fᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  htpy-eq-hom-Ring-𝔽ᵉ :
    (gᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ
  htpy-eq-hom-Ring-𝔽ᵉ =
    htpy-eq-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  is-torsorial-htpy-hom-Ring-𝔽ᵉ :
    is-torsorialᵉ (htpy-hom-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ)
  is-torsorial-htpy-hom-Ring-𝔽ᵉ =
    is-torsorial-htpy-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Ring-𝔽ᵉ :
    (gᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-hom-Ring-𝔽ᵉ gᵉ)
  is-equiv-htpy-eq-hom-Ring-𝔽ᵉ =
    is-equiv-htpy-eq-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  extensionality-hom-Ring-𝔽ᵉ :
    (gᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ
  extensionality-hom-Ring-𝔽ᵉ =
    extensionality-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  eq-htpy-hom-Ring-𝔽ᵉ :
    (gᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    htpy-hom-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Ring-𝔽ᵉ =
    eq-htpy-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Ring-𝔽ᵉ l1ᵉ)
  (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  (Cᵉ : Ring-𝔽ᵉ l3ᵉ)
  (Dᵉ : Ring-𝔽ᵉ l4ᵉ)
  (hᵉ : hom-Ring-𝔽ᵉ Cᵉ Dᵉ)
  (gᵉ : hom-Ring-𝔽ᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  associative-comp-hom-Ring-𝔽ᵉ :
    comp-hom-Ring-𝔽ᵉ Aᵉ Bᵉ Dᵉ (comp-hom-Ring-𝔽ᵉ Bᵉ Cᵉ Dᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Ring-𝔽ᵉ Aᵉ Cᵉ Dᵉ hᵉ (comp-hom-Ring-𝔽ᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
  associative-comp-hom-Ring-𝔽ᵉ =
    associative-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( ring-Ring-𝔽ᵉ Cᵉ)
      ( ring-Ring-𝔽ᵉ Dᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Ring-𝔽ᵉ l1ᵉ)
  (Bᵉ : Ring-𝔽ᵉ l2ᵉ)
  (fᵉ : hom-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-hom-Ring-𝔽ᵉ :
    comp-hom-Ring-𝔽ᵉ Aᵉ Bᵉ Bᵉ (id-hom-Ring-𝔽ᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Ring-𝔽ᵉ =
    left-unit-law-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Ring-𝔽ᵉ :
    comp-hom-Ring-𝔽ᵉ Aᵉ Aᵉ Bᵉ fᵉ (id-hom-Ring-𝔽ᵉ Aᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Ring-𝔽ᵉ =
    right-unit-law-comp-hom-Ringᵉ
      ( ring-Ring-𝔽ᵉ Aᵉ)
      ( ring-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)
```