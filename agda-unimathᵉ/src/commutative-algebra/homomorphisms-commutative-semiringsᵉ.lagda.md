# Homomorphisms of commutative semirings

```agda
module commutative-algebra.homomorphisms-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.homomorphisms-monoidsᵉ

open import ring-theory.homomorphisms-semiringsᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ commutativeᵉ semirings**ᵉ isᵉ aᵉ mapᵉ whichᵉ preservesᵉ `0`,ᵉ `+`,ᵉ
`1`,ᵉ andᵉ `·`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) (Bᵉ : Commutative-Semiringᵉ l2ᵉ)
  where

  hom-set-Commutative-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Commutative-Semiringᵉ =
    hom-set-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)

  hom-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Commutative-Semiringᵉ =
    hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)

  is-set-hom-Commutative-Semiringᵉ : is-setᵉ hom-Commutative-Semiringᵉ
  is-set-hom-Commutative-Semiringᵉ =
    is-set-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)

  module _
    (fᵉ : hom-Commutative-Semiringᵉ)
    where

    hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ :
      hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Commutative-Semiringᵉ Aᵉ)
        ( additive-commutative-monoid-Commutative-Semiringᵉ Bᵉ)
    hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ =
      hom-additive-commutative-monoid-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    map-hom-Commutative-Semiringᵉ :
      type-Commutative-Semiringᵉ Aᵉ → type-Commutative-Semiringᵉ Bᵉ
    map-hom-Commutative-Semiringᵉ =
      map-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    preserves-addition-hom-Commutative-Semiringᵉ :
      {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} →
      map-hom-Commutative-Semiringᵉ (add-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
      add-Commutative-Semiringᵉ Bᵉ
        ( map-hom-Commutative-Semiringᵉ xᵉ)
        ( map-hom-Commutative-Semiringᵉ yᵉ)
    preserves-addition-hom-Commutative-Semiringᵉ =
      preserves-addition-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    preserves-zero-hom-Commutative-Semiringᵉ :
      map-hom-Commutative-Semiringᵉ (zero-Commutative-Semiringᵉ Aᵉ) ＝ᵉ
      zero-Commutative-Semiringᵉ Bᵉ
    preserves-zero-hom-Commutative-Semiringᵉ =
      preserves-zero-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    preserves-mul-hom-Commutative-Semiringᵉ :
      {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} →
      map-hom-Commutative-Semiringᵉ (mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
      mul-Commutative-Semiringᵉ Bᵉ
        ( map-hom-Commutative-Semiringᵉ xᵉ)
        ( map-hom-Commutative-Semiringᵉ yᵉ)
    preserves-mul-hom-Commutative-Semiringᵉ =
      preserves-mul-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    preserves-unit-hom-Commutative-Semiringᵉ :
      map-hom-Commutative-Semiringᵉ (one-Commutative-Semiringᵉ Aᵉ) ＝ᵉ
      one-Commutative-Semiringᵉ Bᵉ
    preserves-unit-hom-Commutative-Semiringᵉ =
      preserves-unit-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    is-homomorphism-semiring-hom-Commutative-Semiringᵉ :
      is-homomorphism-semiring-hom-Commutative-Monoidᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ)
    is-homomorphism-semiring-hom-Commutative-Semiringᵉ =
      is-homomorphism-semiring-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)

    hom-multiplicative-monoid-hom-Commutative-Semiringᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Commutative-Semiringᵉ Aᵉ)
        ( multiplicative-monoid-Commutative-Semiringᵉ Bᵉ)
    hom-multiplicative-monoid-hom-Commutative-Semiringᵉ =
      hom-multiplicative-monoid-hom-Semiringᵉ
        ( semiring-Commutative-Semiringᵉ Aᵉ)
        ( semiring-Commutative-Semiringᵉ Bᵉ)
        ( fᵉ)
```

### The identity homomorphism of commutative semirings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  hom-additive-commutative-monoid-id-hom-Commutative-Semiringᵉ :
    hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Commutative-Semiringᵉ Aᵉ)
      ( additive-commutative-monoid-Commutative-Semiringᵉ Aᵉ)
  hom-additive-commutative-monoid-id-hom-Commutative-Semiringᵉ =
    hom-additive-commutative-monoid-id-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)

  preserves-mul-id-hom-Commutative-Semiringᵉ :
    {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} →
    mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ
  preserves-mul-id-hom-Commutative-Semiringᵉ =
    preserves-mul-id-hom-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  preserves-unit-id-hom-Commutative-Semiringᵉ :
    one-Commutative-Semiringᵉ Aᵉ ＝ᵉ one-Commutative-Semiringᵉ Aᵉ
  preserves-unit-id-hom-Commutative-Semiringᵉ =
    preserves-unit-id-hom-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  id-hom-Commutative-Semiringᵉ : hom-Commutative-Semiringᵉ Aᵉ Aᵉ
  id-hom-Commutative-Semiringᵉ =
    id-hom-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Composition of homomorphisms of commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Bᵉ : Commutative-Semiringᵉ l2ᵉ)
  (Cᵉ : Commutative-Semiringᵉ l3ᵉ)
  (gᵉ : hom-Commutative-Semiringᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ)
  where

  hom-additive-commutative-monoid-comp-hom-Commutative-Semiringᵉ :
    hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Commutative-Semiringᵉ Aᵉ)
      ( additive-commutative-monoid-Commutative-Semiringᵉ Cᵉ)
  hom-additive-commutative-monoid-comp-hom-Commutative-Semiringᵉ =
    hom-additive-commutative-monoid-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  hom-multiplicative-monoid-comp-hom-Commutative-Semiringᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Commutative-Semiringᵉ Aᵉ)
      ( multiplicative-monoid-Commutative-Semiringᵉ Cᵉ)
  hom-multiplicative-monoid-comp-hom-Commutative-Semiringᵉ =
    hom-multiplicative-monoid-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  map-comp-hom-Commutative-Semiringᵉ :
    type-Commutative-Semiringᵉ Aᵉ → type-Commutative-Semiringᵉ Cᵉ
  map-comp-hom-Commutative-Semiringᵉ =
    map-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-mul-comp-hom-Commutative-Semiringᵉ :
    {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} →
    map-comp-hom-Commutative-Semiringᵉ (mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Semiringᵉ Cᵉ
      ( map-comp-hom-Commutative-Semiringᵉ xᵉ)
      ( map-comp-hom-Commutative-Semiringᵉ yᵉ)
  preserves-mul-comp-hom-Commutative-Semiringᵉ =
    preserves-mul-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-unit-comp-hom-Commutative-Semiringᵉ :
    map-comp-hom-Commutative-Semiringᵉ (one-Commutative-Semiringᵉ Aᵉ) ＝ᵉ
    one-Commutative-Semiringᵉ Cᵉ
  preserves-unit-comp-hom-Commutative-Semiringᵉ =
    preserves-unit-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Commutative-Semiringᵉ : hom-Commutative-Semiringᵉ Aᵉ Cᵉ
  comp-hom-Commutative-Semiringᵉ =
    comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of homomorphisms of commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Semiringᵉ l1ᵉ) (Sᵉ : Commutative-Semiringᵉ l2ᵉ)
  where

  htpy-hom-Commutative-Semiringᵉ :
    (fᵉ gᵉ : hom-Commutative-Semiringᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Commutative-Semiringᵉ fᵉ gᵉ =
    htpy-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Commutative-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Commutative-Semiringᵉ Sᵉ)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ Rᵉ Sᵉ fᵉ)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ Rᵉ Sᵉ gᵉ)

  refl-htpy-hom-Commutative-Semiringᵉ :
    (fᵉ : hom-Commutative-Semiringᵉ Rᵉ Sᵉ) → htpy-hom-Commutative-Semiringᵉ fᵉ fᵉ
  refl-htpy-hom-Commutative-Semiringᵉ fᵉ =
    refl-htpy-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Commutative-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Commutative-Semiringᵉ Sᵉ)
      ( hom-additive-commutative-monoid-hom-Commutative-Semiringᵉ Rᵉ Sᵉ fᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) (Bᵉ : Commutative-Semiringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ)
  where

  is-torsorial-htpy-hom-Commutative-Semiringᵉ :
    is-torsorialᵉ (htpy-hom-Commutative-Semiringᵉ Aᵉ Bᵉ fᵉ)
  is-torsorial-htpy-hom-Commutative-Semiringᵉ =
    is-torsorial-htpy-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)

  htpy-eq-hom-Commutative-Semiringᵉ :
    (gᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-hom-Commutative-Semiringᵉ Aᵉ Bᵉ fᵉ gᵉ
  htpy-eq-hom-Commutative-Semiringᵉ =
    htpy-eq-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)

  is-equiv-htpy-eq-hom-Commutative-Semiringᵉ :
    (gᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-hom-Commutative-Semiringᵉ gᵉ)
  is-equiv-htpy-eq-hom-Commutative-Semiringᵉ =
    is-equiv-htpy-eq-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)

  extensionality-hom-Commutative-Semiringᵉ :
    (gᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Commutative-Semiringᵉ Aᵉ Bᵉ fᵉ gᵉ
  extensionality-hom-Commutative-Semiringᵉ =
    extensionality-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)

  eq-htpy-hom-Commutative-Semiringᵉ :
    (gᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ) →
    htpy-hom-Commutative-Semiringᵉ Aᵉ Bᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Commutative-Semiringᵉ =
    eq-htpy-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)
```

### Associativity of composition of homomorphisms of commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Bᵉ : Commutative-Semiringᵉ l2ᵉ)
  (Cᵉ : Commutative-Semiringᵉ l3ᵉ)
  (Dᵉ : Commutative-Semiringᵉ l4ᵉ)
  (hᵉ : hom-Commutative-Semiringᵉ Cᵉ Dᵉ)
  (gᵉ : hom-Commutative-Semiringᵉ Bᵉ Cᵉ)
  (fᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ)
  where

  associative-comp-hom-Commutative-Semiringᵉ :
    comp-hom-Commutative-Semiringᵉ Aᵉ Bᵉ Dᵉ
      ( comp-hom-Commutative-Semiringᵉ Bᵉ Cᵉ Dᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Commutative-Semiringᵉ Aᵉ Cᵉ Dᵉ
      ( hᵉ)
      ( comp-hom-Commutative-Semiringᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
  associative-comp-hom-Commutative-Semiringᵉ =
    associative-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( semiring-Commutative-Semiringᵉ Cᵉ)
      ( semiring-Commutative-Semiringᵉ Dᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Unit laws for composition of homomorphisms of commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) (Bᵉ : Commutative-Semiringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Semiringᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-hom-Commutative-Semiringᵉ :
    comp-hom-Commutative-Semiringᵉ Aᵉ Bᵉ Bᵉ (id-hom-Commutative-Semiringᵉ Bᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Commutative-Semiringᵉ =
    left-unit-law-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Commutative-Semiringᵉ :
    comp-hom-Commutative-Semiringᵉ Aᵉ Aᵉ Bᵉ fᵉ (id-hom-Commutative-Semiringᵉ Aᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Commutative-Semiringᵉ =
    right-unit-law-comp-hom-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( semiring-Commutative-Semiringᵉ Bᵉ)
      ( fᵉ)
```