# Homomorphisms of commutative finite rings

```agda
module finite-algebra.homomorphisms-commutative-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.homomorphisms-commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-semiringsᵉ

open import finite-algebra.commutative-finite-ringsᵉ

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

Aᵉ **homomorphismᵉ ofᵉ commutativeᵉ finiteᵉ rings**ᵉ isᵉ aᵉ homomorphismᵉ betweenᵉ theirᵉ
underlyingᵉ rings.ᵉ

## Definition

### The predicate of being a ring homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  where

  is-commutative-finite-ring-homomorphism-hom-Ab-Propᵉ :
    hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ) (ab-Commutative-Ring-𝔽ᵉ Bᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-commutative-finite-ring-homomorphism-hom-Ab-Propᵉ =
    is-ring-homomorphism-hom-Ab-Propᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  is-commutative-finite-ring-homomorphism-hom-Abᵉ :
    hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ) (ab-Commutative-Ring-𝔽ᵉ Bᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-commutative-finite-ring-homomorphism-hom-Abᵉ =
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  is-prop-is-commutative-finite-ring-homomorphism-hom-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ) (ab-Commutative-Ring-𝔽ᵉ Bᵉ)) →
    is-propᵉ
      ( is-commutative-ring-homomorphism-hom-Abᵉ
        ( commutative-ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( commutative-ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ))
  is-prop-is-commutative-finite-ring-homomorphism-hom-Abᵉ =
    is-prop-is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  where

  hom-set-Commutative-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Commutative-Ring-𝔽ᵉ =
    hom-set-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ) (ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  hom-Commutative-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Commutative-Ring-𝔽ᵉ =
    hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ) (ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  is-set-hom-Commutative-Ring-𝔽ᵉ : is-setᵉ hom-Commutative-Ring-𝔽ᵉ
  is-set-hom-Commutative-Ring-𝔽ᵉ =
    is-set-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ) (ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  module _
    (fᵉ : hom-Commutative-Ring-𝔽ᵉ)
    where

    hom-ab-hom-Commutative-Ring-𝔽ᵉ :
      hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ) (ab-Commutative-Ring-𝔽ᵉ Bᵉ)
    hom-ab-hom-Commutative-Ring-𝔽ᵉ =
      hom-ab-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ) (ring-Commutative-Ring-𝔽ᵉ Bᵉ) fᵉ

    hom-multiplicative-monoid-hom-Commutative-Ring-𝔽ᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( multiplicative-monoid-Commutative-Ring-𝔽ᵉ Bᵉ)
    hom-multiplicative-monoid-hom-Commutative-Ring-𝔽ᵉ =
      hom-multiplicative-monoid-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    map-hom-Commutative-Ring-𝔽ᵉ :
      type-Commutative-Ring-𝔽ᵉ Aᵉ → type-Commutative-Ring-𝔽ᵉ Bᵉ
    map-hom-Commutative-Ring-𝔽ᵉ =
      map-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-add-hom-Commutative-Ring-𝔽ᵉ :
      preserves-add-Abᵉ
        ( ab-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ab-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Commutative-Ring-𝔽ᵉ)
    preserves-add-hom-Commutative-Ring-𝔽ᵉ =
      preserves-add-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-zero-hom-Commutative-Ring-𝔽ᵉ :
      preserves-zero-Abᵉ
        ( ab-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ab-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Commutative-Ring-𝔽ᵉ)
    preserves-zero-hom-Commutative-Ring-𝔽ᵉ =
      preserves-zero-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-neg-hom-Commutative-Ring-𝔽ᵉ :
      preserves-negatives-Abᵉ
        ( ab-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ab-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( map-hom-Commutative-Ring-𝔽ᵉ)
    preserves-neg-hom-Commutative-Ring-𝔽ᵉ =
      preserves-neg-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-mul-hom-Commutative-Ring-𝔽ᵉ :
      preserves-mul-hom-Abᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( hom-ab-hom-Commutative-Ring-𝔽ᵉ)
    preserves-mul-hom-Commutative-Ring-𝔽ᵉ =
      preserves-mul-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    preserves-one-hom-Commutative-Ring-𝔽ᵉ :
      preserves-unit-hom-Abᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( hom-ab-hom-Commutative-Ring-𝔽ᵉ)
    preserves-one-hom-Commutative-Ring-𝔽ᵉ =
      preserves-one-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    is-commutative-ring-homomorphism-hom-Commutative-Ring-𝔽ᵉ :
      is-commutative-ring-homomorphism-hom-Abᵉ
        ( commutative-ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( commutative-ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( hom-ab-hom-Commutative-Ring-𝔽ᵉ)
    is-commutative-ring-homomorphism-hom-Commutative-Ring-𝔽ᵉ =
      is-ring-homomorphism-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)

    hom-commutative-semiring-hom-Commutative-Ring-𝔽ᵉ :
      hom-Commutative-Semiringᵉ
        ( commutative-semiring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( commutative-semiring-Commutative-Ring-𝔽ᵉ Bᵉ)
    hom-commutative-semiring-hom-Commutative-Ring-𝔽ᵉ =
      hom-semiring-hom-Ringᵉ
        ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
        ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
        ( fᵉ)
```

### The identity homomorphism of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ring-𝔽ᵉ lᵉ)
  where

  preserves-mul-id-hom-Commutative-Ring-𝔽ᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ))
  preserves-mul-id-hom-Commutative-Ring-𝔽ᵉ =
    preserves-mul-id-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ)

  preserves-unit-id-hom-Commutative-Ring-𝔽ᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ))
  preserves-unit-id-hom-Commutative-Ring-𝔽ᵉ =
    preserves-unit-id-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ)

  is-ring-homomorphism-id-hom-Commutative-Ring-𝔽ᵉ :
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ))
  is-ring-homomorphism-id-hom-Commutative-Ring-𝔽ᵉ =
    is-ring-homomorphism-id-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ)

  id-hom-Commutative-Ring-𝔽ᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Aᵉ
  id-hom-Commutative-Ring-𝔽ᵉ = id-hom-Ringᵉ (ring-Commutative-Ring-𝔽ᵉ Aᵉ)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ)
  (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  (Cᵉ : Commutative-Ring-𝔽ᵉ l3ᵉ)
  (gᵉ : hom-Commutative-Ring-𝔽ᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  hom-ab-comp-hom-Commutative-Ring-𝔽ᵉ :
    hom-Abᵉ (ab-Commutative-Ring-𝔽ᵉ Aᵉ) (ab-Commutative-Ring-𝔽ᵉ Cᵉ)
  hom-ab-comp-hom-Commutative-Ring-𝔽ᵉ =
    hom-ab-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  hom-multiplicative-monoid-comp-hom-Commutative-Ring-𝔽ᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( multiplicative-monoid-Commutative-Ring-𝔽ᵉ Cᵉ)
  hom-multiplicative-monoid-comp-hom-Commutative-Ring-𝔽ᵉ =
    hom-multiplicative-monoid-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-mul-comp-hom-Commutative-Ring-𝔽ᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽ᵉ)
  preserves-mul-comp-hom-Commutative-Ring-𝔽ᵉ =
    preserves-mul-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-unit-comp-hom-Commutative-Ring-𝔽ᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽ᵉ)
  preserves-unit-comp-hom-Commutative-Ring-𝔽ᵉ =
    preserves-unit-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring-𝔽ᵉ :
    is-commutative-ring-homomorphism-hom-Abᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( hom-ab-comp-hom-Commutative-Ring-𝔽ᵉ)
  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring-𝔽ᵉ =
    is-ring-homomorphism-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Commutative-Ring-𝔽ᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Cᵉ
  comp-hom-Commutative-Ring-𝔽ᵉ =
    comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  where

  htpy-hom-Commutative-Ring-𝔽ᵉ :
    hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ → hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Commutative-Ring-𝔽ᵉ =
    htpy-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)

  refl-htpy-hom-Commutative-Ring-𝔽ᵉ :
    (fᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ) → htpy-hom-Commutative-Ring-𝔽ᵉ fᵉ fᵉ
  refl-htpy-hom-Commutative-Ring-𝔽ᵉ =
    refl-htpy-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  htpy-eq-hom-Commutative-Ring-𝔽ᵉ :
    (gᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ
  htpy-eq-hom-Commutative-Ring-𝔽ᵉ =
    htpy-eq-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  is-torsorial-htpy-hom-Commutative-Ring-𝔽ᵉ :
    is-torsorialᵉ (htpy-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ)
  is-torsorial-htpy-hom-Commutative-Ring-𝔽ᵉ =
    is-torsorial-htpy-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Commutative-Ring-𝔽ᵉ :
    (gᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-hom-Commutative-Ring-𝔽ᵉ gᵉ)
  is-equiv-htpy-eq-hom-Commutative-Ring-𝔽ᵉ =
    is-equiv-htpy-eq-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  extensionality-hom-Commutative-Ring-𝔽ᵉ :
    (gᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ
  extensionality-hom-Commutative-Ring-𝔽ᵉ =
    extensionality-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  eq-htpy-hom-Commutative-Ring-𝔽ᵉ :
    (gᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ) →
    htpy-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Commutative-Ring-𝔽ᵉ =
    eq-htpy-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ)
  (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  (Cᵉ : Commutative-Ring-𝔽ᵉ l3ᵉ)
  (Dᵉ : Commutative-Ring-𝔽ᵉ l4ᵉ)
  (hᵉ : hom-Commutative-Ring-𝔽ᵉ Cᵉ Dᵉ)
  (gᵉ : hom-Commutative-Ring-𝔽ᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  associative-comp-hom-Commutative-Ring-𝔽ᵉ :
    comp-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ Dᵉ
      ( comp-hom-Commutative-Ring-𝔽ᵉ Bᵉ Cᵉ Dᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Commutative-Ring-𝔽ᵉ Aᵉ Cᵉ Dᵉ
      ( hᵉ)
      ( comp-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
  associative-comp-hom-Commutative-Ring-𝔽ᵉ =
    associative-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Cᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Dᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ)
  (Bᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-hom-Commutative-Ring-𝔽ᵉ :
    comp-hom-Commutative-Ring-𝔽ᵉ Aᵉ Bᵉ Bᵉ (id-hom-Commutative-Ring-𝔽ᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Commutative-Ring-𝔽ᵉ =
    left-unit-law-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Commutative-Ring-𝔽ᵉ :
    comp-hom-Commutative-Ring-𝔽ᵉ Aᵉ Aᵉ Bᵉ fᵉ (id-hom-Commutative-Ring-𝔽ᵉ Aᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Commutative-Ring-𝔽ᵉ =
    right-unit-law-comp-hom-Ringᵉ
      ( ring-Commutative-Ring-𝔽ᵉ Aᵉ)
      ( ring-Commutative-Ring-𝔽ᵉ Bᵉ)
      ( fᵉ)
```