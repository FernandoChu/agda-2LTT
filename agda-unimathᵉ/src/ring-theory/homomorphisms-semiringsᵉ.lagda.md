# Homomorphisms of semirings

```agda
module ring-theory.homomorphisms-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
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

open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.homomorphisms-semigroupsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

**Homomorphismsᵉ ofᵉ semirings**ᵉ areᵉ homomorphismsᵉ ofᵉ theirᵉ underlyingᵉ additiveᵉ
commutativeᵉ monoidsᵉ thatᵉ preserveᵉ multiplicationᵉ andᵉ theᵉ multiplicativeᵉ unit.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ)
  where

  is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ :
    ( hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Sᵉ)) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ fᵉ =
    Σ-Propᵉ
      ( preserves-mul-prop-Semigroupᵉ
        ( multiplicative-semigroup-Semiringᵉ Rᵉ)
        ( multiplicative-semigroup-Semiringᵉ Sᵉ)
        ( map-hom-Commutative-Monoidᵉ
          ( additive-commutative-monoid-Semiringᵉ Rᵉ)
          ( additive-commutative-monoid-Semiringᵉ Sᵉ)
          ( fᵉ)))
      ( λ Hᵉ →
        preserves-unit-prop-hom-Semigroupᵉ
          ( multiplicative-monoid-Semiringᵉ Rᵉ)
          ( multiplicative-monoid-Semiringᵉ Sᵉ)
          ( ( map-hom-Commutative-Monoidᵉ
              ( additive-commutative-monoid-Semiringᵉ Rᵉ)
              ( additive-commutative-monoid-Semiringᵉ Sᵉ)
              ( fᵉ)) ,ᵉ
            ( Hᵉ)))

  is-homomorphism-semiring-hom-Commutative-Monoidᵉ :
    ( hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Sᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-homomorphism-semiring-hom-Commutative-Monoidᵉ fᵉ =
    type-Propᵉ (is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ fᵉ)

  is-prop-is-homomorphism-semiring-hom-Commutative-Monoidᵉ :
    ( fᵉ :
      hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)) →
    is-propᵉ (is-homomorphism-semiring-hom-Commutative-Monoidᵉ fᵉ)
  is-prop-is-homomorphism-semiring-hom-Commutative-Monoidᵉ fᵉ =
    is-prop-type-Propᵉ (is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ fᵉ)

  hom-set-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Semiringᵉ =
    set-subsetᵉ
      ( hom-set-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ))
      ( is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ)

  hom-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Semiringᵉ = type-Setᵉ hom-set-Semiringᵉ

  is-set-hom-Semiringᵉ : is-setᵉ hom-Semiringᵉ
  is-set-hom-Semiringᵉ = is-set-type-Setᵉ hom-set-Semiringᵉ

  module _
    (fᵉ : hom-Semiringᵉ)
    where

    hom-additive-commutative-monoid-hom-Semiringᵉ :
      hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)
    hom-additive-commutative-monoid-hom-Semiringᵉ = pr1ᵉ fᵉ

    map-hom-Semiringᵉ : type-Semiringᵉ Rᵉ → type-Semiringᵉ Sᵉ
    map-hom-Semiringᵉ =
      map-hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)
        ( hom-additive-commutative-monoid-hom-Semiringᵉ)

    preserves-addition-hom-Semiringᵉ :
      {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
      map-hom-Semiringᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
      add-Semiringᵉ Sᵉ (map-hom-Semiringᵉ xᵉ) (map-hom-Semiringᵉ yᵉ)
    preserves-addition-hom-Semiringᵉ =
      preserves-mul-hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)
        ( hom-additive-commutative-monoid-hom-Semiringᵉ)

    preserves-zero-hom-Semiringᵉ :
      map-hom-Semiringᵉ (zero-Semiringᵉ Rᵉ) ＝ᵉ zero-Semiringᵉ Sᵉ
    preserves-zero-hom-Semiringᵉ =
      preserves-unit-hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)
        ( hom-additive-commutative-monoid-hom-Semiringᵉ)

    preserves-mul-hom-Semiringᵉ :
      {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
      map-hom-Semiringᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
      mul-Semiringᵉ Sᵉ (map-hom-Semiringᵉ xᵉ) (map-hom-Semiringᵉ yᵉ)
    preserves-mul-hom-Semiringᵉ = pr1ᵉ (pr2ᵉ fᵉ)

    preserves-unit-hom-Semiringᵉ :
      map-hom-Semiringᵉ (one-Semiringᵉ Rᵉ) ＝ᵉ one-Semiringᵉ Sᵉ
    preserves-unit-hom-Semiringᵉ = pr2ᵉ (pr2ᵉ fᵉ)

    is-homomorphism-semiring-hom-Semiringᵉ :
      is-homomorphism-semiring-hom-Commutative-Monoidᵉ
        ( hom-additive-commutative-monoid-hom-Semiringᵉ)
    pr1ᵉ is-homomorphism-semiring-hom-Semiringᵉ = preserves-mul-hom-Semiringᵉ
    pr2ᵉ is-homomorphism-semiring-hom-Semiringᵉ = preserves-unit-hom-Semiringᵉ

    hom-multiplicative-monoid-hom-Semiringᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Semiringᵉ Rᵉ)
        ( multiplicative-monoid-Semiringᵉ Sᵉ)
    pr1ᵉ (pr1ᵉ hom-multiplicative-monoid-hom-Semiringᵉ) =
      map-hom-Semiringᵉ
    pr2ᵉ (pr1ᵉ hom-multiplicative-monoid-hom-Semiringᵉ) =
      preserves-mul-hom-Semiringᵉ
    pr2ᵉ hom-multiplicative-monoid-hom-Semiringᵉ =
      preserves-unit-hom-Semiringᵉ
```

### The identity homomorphism of semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  hom-additive-commutative-monoid-id-hom-Semiringᵉ :
    hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
  hom-additive-commutative-monoid-id-hom-Semiringᵉ =
    id-hom-Commutative-Monoidᵉ (additive-commutative-monoid-Semiringᵉ Rᵉ)

  preserves-mul-id-hom-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} → mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ xᵉ yᵉ
  preserves-mul-id-hom-Semiringᵉ = reflᵉ

  preserves-unit-id-hom-Semiringᵉ :
    one-Semiringᵉ Rᵉ ＝ᵉ one-Semiringᵉ Rᵉ
  preserves-unit-id-hom-Semiringᵉ = reflᵉ

  id-hom-Semiringᵉ : hom-Semiringᵉ Rᵉ Rᵉ
  pr1ᵉ id-hom-Semiringᵉ = hom-additive-commutative-monoid-id-hom-Semiringᵉ
  pr1ᵉ (pr2ᵉ id-hom-Semiringᵉ) = preserves-mul-id-hom-Semiringᵉ
  pr2ᵉ (pr2ᵉ id-hom-Semiringᵉ) = preserves-unit-id-hom-Semiringᵉ
```

### Composition of homomorphisms of semirings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ) (Tᵉ : Semiringᵉ l3ᵉ)
  (gᵉ : hom-Semiringᵉ Sᵉ Tᵉ) (fᵉ : hom-Semiringᵉ Rᵉ Sᵉ)
  where

  hom-additive-commutative-monoid-comp-hom-Semiringᵉ :
    hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Tᵉ)
  hom-additive-commutative-monoid-comp-hom-Semiringᵉ =
    comp-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Sᵉ)
      ( additive-commutative-monoid-Semiringᵉ Tᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)

  hom-multiplicative-monoid-comp-hom-Semiringᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( multiplicative-monoid-Semiringᵉ Tᵉ)
  hom-multiplicative-monoid-comp-hom-Semiringᵉ =
    comp-hom-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( multiplicative-monoid-Semiringᵉ Sᵉ)
      ( multiplicative-monoid-Semiringᵉ Tᵉ)
      ( hom-multiplicative-monoid-hom-Semiringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-multiplicative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)

  map-comp-hom-Semiringᵉ :
    type-Semiringᵉ Rᵉ → type-Semiringᵉ Tᵉ
  map-comp-hom-Semiringᵉ =
    map-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Tᵉ)
      ( hom-additive-commutative-monoid-comp-hom-Semiringᵉ)

  preserves-mul-comp-hom-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    map-comp-hom-Semiringᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    mul-Semiringᵉ Tᵉ (map-comp-hom-Semiringᵉ xᵉ) (map-comp-hom-Semiringᵉ yᵉ)
  preserves-mul-comp-hom-Semiringᵉ =
    preserves-mul-hom-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( multiplicative-monoid-Semiringᵉ Tᵉ)
      ( hom-multiplicative-monoid-comp-hom-Semiringᵉ)

  preserves-unit-comp-hom-Semiringᵉ :
    map-comp-hom-Semiringᵉ (one-Semiringᵉ Rᵉ) ＝ᵉ one-Semiringᵉ Tᵉ
  preserves-unit-comp-hom-Semiringᵉ =
    preserves-unit-hom-Monoidᵉ
      ( multiplicative-monoid-Semiringᵉ Rᵉ)
      ( multiplicative-monoid-Semiringᵉ Tᵉ)
      ( hom-multiplicative-monoid-comp-hom-Semiringᵉ)

  comp-hom-Semiringᵉ : hom-Semiringᵉ Rᵉ Tᵉ
  pr1ᵉ comp-hom-Semiringᵉ = hom-additive-commutative-monoid-comp-hom-Semiringᵉ
  pr1ᵉ (pr2ᵉ comp-hom-Semiringᵉ) = preserves-mul-comp-hom-Semiringᵉ
  pr2ᵉ (pr2ᵉ comp-hom-Semiringᵉ) = preserves-unit-comp-hom-Semiringᵉ
```

### Homotopies of homomorphisms of semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ)
  where

  htpy-hom-Semiringᵉ : (fᵉ gᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Semiringᵉ fᵉ gᵉ =
    htpy-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Sᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ gᵉ)

  refl-htpy-hom-Semiringᵉ : (fᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → htpy-hom-Semiringᵉ fᵉ fᵉ
  refl-htpy-hom-Semiringᵉ fᵉ =
    refl-htpy-hom-Commutative-Monoidᵉ
      ( additive-commutative-monoid-Semiringᵉ Rᵉ)
      ( additive-commutative-monoid-Semiringᵉ Sᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)
```

## Properties

### Homotopies characterize identifications of homomorphisms of semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ)
  (fᵉ : hom-Semiringᵉ Rᵉ Sᵉ)
  where

  is-torsorial-htpy-hom-Semiringᵉ :
    is-torsorialᵉ (htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)
  is-torsorial-htpy-hom-Semiringᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpy-hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Semiringᵉ Rᵉ)
        ( additive-commutative-monoid-Semiringᵉ Sᵉ)
        ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ))
      ( is-prop-is-homomorphism-semiring-hom-Commutative-Monoidᵉ Rᵉ Sᵉ)
      ( hom-additive-commutative-monoid-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)
      ( refl-htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)
      ( is-homomorphism-semiring-hom-Semiringᵉ Rᵉ Sᵉ fᵉ)

  htpy-eq-hom-Semiringᵉ :
    (gᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) → htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ gᵉ
  htpy-eq-hom-Semiringᵉ .fᵉ reflᵉ = refl-htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ

  is-equiv-htpy-eq-hom-Semiringᵉ :
    (gᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → is-equivᵉ (htpy-eq-hom-Semiringᵉ gᵉ)
  is-equiv-htpy-eq-hom-Semiringᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-hom-Semiringᵉ
      htpy-eq-hom-Semiringᵉ

  extensionality-hom-Semiringᵉ :
    (gᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Semiringᵉ gᵉ) = htpy-eq-hom-Semiringᵉ gᵉ
  pr2ᵉ (extensionality-hom-Semiringᵉ gᵉ) = is-equiv-htpy-eq-hom-Semiringᵉ gᵉ

  eq-htpy-hom-Semiringᵉ :
    (gᵉ : hom-Semiringᵉ Rᵉ Sᵉ) → htpy-hom-Semiringᵉ Rᵉ Sᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Semiringᵉ gᵉ = map-inv-equivᵉ (extensionality-hom-Semiringᵉ gᵉ)
```

### Associativity of composition of homomorphisms of semirings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ) (Tᵉ : Semiringᵉ l3ᵉ) (Uᵉ : Semiringᵉ l4ᵉ)
  (hᵉ : hom-Semiringᵉ Tᵉ Uᵉ)
  (gᵉ : hom-Semiringᵉ Sᵉ Tᵉ)
  (fᵉ : hom-Semiringᵉ Rᵉ Sᵉ)
  where

  associative-comp-hom-Semiringᵉ :
    comp-hom-Semiringᵉ Rᵉ Sᵉ Uᵉ (comp-hom-Semiringᵉ Sᵉ Tᵉ Uᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Semiringᵉ Rᵉ Tᵉ Uᵉ hᵉ (comp-hom-Semiringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ)
  associative-comp-hom-Semiringᵉ =
    eq-htpy-hom-Semiringᵉ Rᵉ Uᵉ
      ( comp-hom-Semiringᵉ Rᵉ Sᵉ Uᵉ (comp-hom-Semiringᵉ Sᵉ Tᵉ Uᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Semiringᵉ Rᵉ Tᵉ Uᵉ hᵉ (comp-hom-Semiringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)
```

### Unit laws for composition of homomorphisms of semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : Semiringᵉ l2ᵉ)
  (fᵉ : hom-Semiringᵉ Rᵉ Sᵉ)
  where

  left-unit-law-comp-hom-Semiringᵉ :
    comp-hom-Semiringᵉ Rᵉ Sᵉ Sᵉ (id-hom-Semiringᵉ Sᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Semiringᵉ =
    eq-htpy-hom-Semiringᵉ Rᵉ Sᵉ
      ( comp-hom-Semiringᵉ Rᵉ Sᵉ Sᵉ (id-hom-Semiringᵉ Sᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-hom-Semiringᵉ :
    comp-hom-Semiringᵉ Rᵉ Rᵉ Sᵉ fᵉ (id-hom-Semiringᵉ Rᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Semiringᵉ =
    eq-htpy-hom-Semiringᵉ Rᵉ Sᵉ
      ( comp-hom-Semiringᵉ Rᵉ Rᵉ Sᵉ fᵉ (id-hom-Semiringᵉ Rᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)
```