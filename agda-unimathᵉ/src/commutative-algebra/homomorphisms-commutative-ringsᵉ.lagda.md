# Homomorphisms of commutative rings

```agda
module commutative-algebra.homomorphisms-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-semiringsᵉ
open import commutative-algebra.invertible-elements-commutative-ringsᵉ

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

Aᵉ **homomorphismᵉ ofᵉ commutativeᵉ rings**ᵉ isᵉ aᵉ homomorphismᵉ betweenᵉ theirᵉ
underlyingᵉ rings.ᵉ

## Definition

### The predicate of being a ring homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  is-commutative-ring-homomorphism-hom-Ab-Propᵉ :
    hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-commutative-ring-homomorphism-hom-Ab-Propᵉ =
    is-ring-homomorphism-hom-Ab-Propᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-commutative-ring-homomorphism-hom-Abᵉ :
    hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-commutative-ring-homomorphism-hom-Abᵉ =
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-prop-is-commutative-ring-homomorphism-hom-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ)) →
    is-propᵉ (is-commutative-ring-homomorphism-hom-Abᵉ fᵉ)
  is-prop-is-commutative-ring-homomorphism-hom-Abᵉ =
    is-prop-is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  hom-set-Commutative-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Commutative-Ringᵉ =
    hom-set-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) (ring-Commutative-Ringᵉ Bᵉ)

  hom-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Commutative-Ringᵉ =
    hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) (ring-Commutative-Ringᵉ Bᵉ)

  is-set-hom-Commutative-Ringᵉ : is-setᵉ hom-Commutative-Ringᵉ
  is-set-hom-Commutative-Ringᵉ =
    is-set-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) (ring-Commutative-Ringᵉ Bᵉ)

  module _
    (fᵉ : hom-Commutative-Ringᵉ)
    where

    hom-ab-hom-Commutative-Ringᵉ :
      hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ)
    hom-ab-hom-Commutative-Ringᵉ =
      hom-ab-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) (ring-Commutative-Ringᵉ Bᵉ) fᵉ

    hom-multiplicative-monoid-hom-Commutative-Ringᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Commutative-Ringᵉ Aᵉ)
        ( multiplicative-monoid-Commutative-Ringᵉ Bᵉ)
    hom-multiplicative-monoid-hom-Commutative-Ringᵉ =
      hom-multiplicative-monoid-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    map-hom-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Bᵉ
    map-hom-Commutative-Ringᵉ =
      map-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    preserves-add-hom-Commutative-Ringᵉ :
      preserves-add-Abᵉ
        ( ab-Commutative-Ringᵉ Aᵉ)
        ( ab-Commutative-Ringᵉ Bᵉ)
        ( map-hom-Commutative-Ringᵉ)
    preserves-add-hom-Commutative-Ringᵉ =
      preserves-add-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    preserves-zero-hom-Commutative-Ringᵉ :
      preserves-zero-Abᵉ
        ( ab-Commutative-Ringᵉ Aᵉ)
        ( ab-Commutative-Ringᵉ Bᵉ)
        ( map-hom-Commutative-Ringᵉ)
    preserves-zero-hom-Commutative-Ringᵉ =
      preserves-zero-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    preserves-neg-hom-Commutative-Ringᵉ :
      preserves-negatives-Abᵉ
        ( ab-Commutative-Ringᵉ Aᵉ)
        ( ab-Commutative-Ringᵉ Bᵉ)
        ( map-hom-Commutative-Ringᵉ)
    preserves-neg-hom-Commutative-Ringᵉ =
      preserves-neg-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    preserves-mul-hom-Commutative-Ringᵉ :
      preserves-mul-hom-Abᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( hom-ab-hom-Commutative-Ringᵉ)
    preserves-mul-hom-Commutative-Ringᵉ =
      preserves-mul-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    preserves-one-hom-Commutative-Ringᵉ :
      preserves-unit-hom-Abᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( hom-ab-hom-Commutative-Ringᵉ)
    preserves-one-hom-Commutative-Ringᵉ =
      preserves-one-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    is-commutative-ring-homomorphism-hom-Commutative-Ringᵉ :
      is-commutative-ring-homomorphism-hom-Abᵉ Aᵉ Bᵉ hom-ab-hom-Commutative-Ringᵉ
    is-commutative-ring-homomorphism-hom-Commutative-Ringᵉ =
      is-ring-homomorphism-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)

    hom-commutative-semiring-hom-Commutative-Ringᵉ :
      hom-Commutative-Semiringᵉ
        ( commutative-semiring-Commutative-Ringᵉ Aᵉ)
        ( commutative-semiring-Commutative-Ringᵉ Bᵉ)
    hom-commutative-semiring-hom-Commutative-Ringᵉ =
      hom-semiring-hom-Ringᵉ
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( ring-Commutative-Ringᵉ Bᵉ)
        ( fᵉ)
```

### The identity homomorphism of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  preserves-mul-id-hom-Commutative-Ringᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ))
  preserves-mul-id-hom-Commutative-Ringᵉ =
    preserves-mul-id-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  preserves-unit-id-hom-Commutative-Ringᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ))
  preserves-unit-id-hom-Commutative-Ringᵉ =
    preserves-unit-id-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-ring-homomorphism-id-hom-Commutative-Ringᵉ :
    is-ring-homomorphism-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( id-hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ))
  is-ring-homomorphism-id-hom-Commutative-Ringᵉ =
    is-ring-homomorphism-id-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  id-hom-Commutative-Ringᵉ : hom-Commutative-Ringᵉ Aᵉ Aᵉ
  id-hom-Commutative-Ringᵉ = id-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ) (Cᵉ : Commutative-Ringᵉ l3ᵉ)
  (gᵉ : hom-Commutative-Ringᵉ Bᵉ Cᵉ) (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  hom-ab-comp-hom-Commutative-Ringᵉ :
    hom-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Cᵉ)
  hom-ab-comp-hom-Commutative-Ringᵉ =
    hom-ab-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  hom-multiplicative-monoid-comp-hom-Commutative-Ringᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Commutative-Ringᵉ Aᵉ)
      ( multiplicative-monoid-Commutative-Ringᵉ Cᵉ)
  hom-multiplicative-monoid-comp-hom-Commutative-Ringᵉ =
    hom-multiplicative-monoid-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-mul-comp-hom-Commutative-Ringᵉ :
    preserves-mul-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( hom-ab-comp-hom-Commutative-Ringᵉ)
  preserves-mul-comp-hom-Commutative-Ringᵉ =
    preserves-mul-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-unit-comp-hom-Commutative-Ringᵉ :
    preserves-unit-hom-Abᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( hom-ab-comp-hom-Commutative-Ringᵉ)
  preserves-unit-comp-hom-Commutative-Ringᵉ =
    preserves-unit-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  is-commutative-ring-homomorphism-comp-hom-Commutative-Ringᵉ :
    is-commutative-ring-homomorphism-hom-Abᵉ Aᵉ Cᵉ
      ( hom-ab-comp-hom-Commutative-Ringᵉ)
  is-commutative-ring-homomorphism-comp-hom-Commutative-Ringᵉ =
    is-ring-homomorphism-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Commutative-Ringᵉ : hom-Commutative-Ringᵉ Aᵉ Cᵉ
  comp-hom-Commutative-Ringᵉ =
    comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  htpy-hom-Commutative-Ringᵉ :
    hom-Commutative-Ringᵉ Aᵉ Bᵉ → hom-Commutative-Ringᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Commutative-Ringᵉ =
    htpy-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  refl-htpy-hom-Commutative-Ringᵉ :
    (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) → htpy-hom-Commutative-Ringᵉ fᵉ fᵉ
  refl-htpy-hom-Commutative-Ringᵉ =
    refl-htpy-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  htpy-eq-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ gᵉ
  htpy-eq-hom-Commutative-Ringᵉ =
    htpy-eq-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-torsorial-htpy-hom-Commutative-Ringᵉ :
    is-torsorialᵉ (htpy-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ)
  is-torsorial-htpy-hom-Commutative-Ringᵉ =
    is-torsorial-htpy-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-hom-Commutative-Ringᵉ gᵉ)
  is-equiv-htpy-eq-hom-Commutative-Ringᵉ =
    is-equiv-htpy-eq-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  extensionality-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ gᵉ
  extensionality-hom-Commutative-Ringᵉ =
    extensionality-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  eq-htpy-hom-Commutative-Ringᵉ :
    (gᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    htpy-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Commutative-Ringᵉ =
    eq-htpy-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (Cᵉ : Commutative-Ringᵉ l3ᵉ)
  (Dᵉ : Commutative-Ringᵉ l4ᵉ)
  (hᵉ : hom-Commutative-Ringᵉ Cᵉ Dᵉ)
  (gᵉ : hom-Commutative-Ringᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  associative-comp-hom-Commutative-Ringᵉ :
    comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Dᵉ (comp-hom-Commutative-Ringᵉ Bᵉ Cᵉ Dᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Commutative-Ringᵉ Aᵉ Cᵉ Dᵉ hᵉ (comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
  associative-comp-hom-Commutative-Ringᵉ =
    associative-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( ring-Commutative-Ringᵉ Cᵉ)
      ( ring-Commutative-Ringᵉ Dᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-hom-Commutative-Ringᵉ :
    comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Bᵉ (id-hom-Commutative-Ringᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Commutative-Ringᵉ =
    left-unit-law-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Commutative-Ringᵉ :
    comp-hom-Commutative-Ringᵉ Aᵉ Aᵉ Bᵉ fᵉ (id-hom-Commutative-Ringᵉ Aᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Commutative-Ringᵉ =
    right-unit-law-comp-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)
```

### Any homomorphism of commutative rings sends invertible elements to invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Sᵉ)
  where

  preserves-invertible-elements-hom-Commutative-Ringᵉ :
    {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-invertible-element-Commutative-Ringᵉ Sᵉ (map-hom-Commutative-Ringᵉ Aᵉ Sᵉ fᵉ xᵉ)
  preserves-invertible-elements-hom-Commutative-Ringᵉ =
    preserves-invertible-elements-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Sᵉ)
      ( fᵉ)
```