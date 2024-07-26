# Homomorphisms of rings

```agda
module ring-theory.homomorphisms-ringsᵉ where
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

open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ

open import ring-theory.homomorphisms-semiringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Ringᵉ homomorphismsᵉ areᵉ mapsᵉ betweenᵉ ringsᵉ thatᵉ preserveᵉ theᵉ ringᵉ structureᵉ

## Definitions

### The predicate on group homomorphisms between rings of preserving multiplication

```agda
preserves-mul-hom-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) →
  hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
preserves-mul-hom-Abᵉ Rᵉ Sᵉ fᵉ =
  {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
  map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
  mul-Ringᵉ Sᵉ
    ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ xᵉ)
    ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ yᵉ)

is-prop-preserves-mul-hom-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) →
  ( fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
  is-propᵉ (preserves-mul-hom-Abᵉ Rᵉ Sᵉ fᵉ)
is-prop-preserves-mul-hom-Abᵉ Rᵉ Sᵉ fᵉ =
  is-prop-implicit-Πᵉ
    ( λ xᵉ →
      is-prop-implicit-Πᵉ
        ( λ yᵉ →
          is-set-type-Ringᵉ Sᵉ
            ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ))
            ( mul-Ringᵉ Sᵉ
              ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ xᵉ)
              ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ yᵉ))))
```

### The predicate on group homomorphisms between rings of preserving the unit

```agda
preserves-unit-hom-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) →
  hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) → UUᵉ l2ᵉ
preserves-unit-hom-Abᵉ Rᵉ Sᵉ fᵉ =
  map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ (one-Ringᵉ Rᵉ) ＝ᵉ one-Ringᵉ Sᵉ

is-prop-preserves-unit-hom-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) →
  ( fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
  is-propᵉ (preserves-unit-hom-Abᵉ Rᵉ Sᵉ fᵉ)
is-prop-preserves-unit-hom-Abᵉ Rᵉ Sᵉ fᵉ =
  is-set-type-Ringᵉ Sᵉ
    ( map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ (one-Ringᵉ Rᵉ))
    ( one-Ringᵉ Sᵉ)
```

### The predicate of being a ring homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  is-ring-homomorphism-hom-Ab-Propᵉ :
    hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-ring-homomorphism-hom-Ab-Propᵉ fᵉ =
    is-homomorphism-semiring-prop-hom-Commutative-Monoidᵉ
      ( semiring-Ringᵉ Rᵉ)
      ( semiring-Ringᵉ Sᵉ)
      ( hom-commutative-monoid-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ)

  is-ring-homomorphism-hom-Abᵉ :
    hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-ring-homomorphism-hom-Abᵉ fᵉ =
    type-Propᵉ (is-ring-homomorphism-hom-Ab-Propᵉ fᵉ)

  is-prop-is-ring-homomorphism-hom-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
    is-propᵉ (is-ring-homomorphism-hom-Abᵉ fᵉ)
  is-prop-is-ring-homomorphism-hom-Abᵉ fᵉ =
    is-prop-type-Propᵉ (is-ring-homomorphism-hom-Ab-Propᵉ fᵉ)
```

### Ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  hom-set-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Ringᵉ =
    set-subsetᵉ
      ( hom-set-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ))
      ( is-ring-homomorphism-hom-Ab-Propᵉ Rᵉ Sᵉ)

  hom-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Ringᵉ = type-Setᵉ hom-set-Ringᵉ

  is-set-hom-Ringᵉ : is-setᵉ hom-Ringᵉ
  is-set-hom-Ringᵉ = is-set-type-Setᵉ hom-set-Ringᵉ

  module _
    (fᵉ : hom-Ringᵉ)
    where

    hom-ab-hom-Ringᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)
    hom-ab-hom-Ringᵉ = pr1ᵉ fᵉ

    hom-group-hom-Ringᵉ : hom-Groupᵉ (group-Ringᵉ Rᵉ) (group-Ringᵉ Sᵉ)
    hom-group-hom-Ringᵉ = hom-ab-hom-Ringᵉ

    hom-commutative-monoid-hom-Ringᵉ :
      hom-Commutative-Monoidᵉ
        ( additive-commutative-monoid-Ringᵉ Rᵉ)
        ( additive-commutative-monoid-Ringᵉ Sᵉ)
    hom-commutative-monoid-hom-Ringᵉ =
      hom-commutative-monoid-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) hom-ab-hom-Ringᵉ

    map-hom-Ringᵉ : type-Ringᵉ Rᵉ → type-Ringᵉ Sᵉ
    map-hom-Ringᵉ = map-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) hom-ab-hom-Ringᵉ

    preserves-add-hom-Ringᵉ :
      preserves-add-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) map-hom-Ringᵉ
    preserves-add-hom-Ringᵉ =
      preserves-add-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) hom-ab-hom-Ringᵉ

    preserves-zero-hom-Ringᵉ :
      preserves-zero-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) map-hom-Ringᵉ
    preserves-zero-hom-Ringᵉ =
      preserves-zero-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) hom-ab-hom-Ringᵉ

    preserves-neg-hom-Ringᵉ :
      preserves-negatives-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) map-hom-Ringᵉ
    preserves-neg-hom-Ringᵉ =
      preserves-negatives-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) hom-ab-hom-Ringᵉ

    preserves-mul-hom-Ringᵉ : preserves-mul-hom-Abᵉ Rᵉ Sᵉ hom-ab-hom-Ringᵉ
    preserves-mul-hom-Ringᵉ = pr1ᵉ (pr2ᵉ fᵉ)

    preserves-one-hom-Ringᵉ : preserves-unit-hom-Abᵉ Rᵉ Sᵉ hom-ab-hom-Ringᵉ
    preserves-one-hom-Ringᵉ = pr2ᵉ (pr2ᵉ fᵉ)

    is-ring-homomorphism-hom-Ringᵉ :
      is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ hom-ab-hom-Ringᵉ
    pr1ᵉ is-ring-homomorphism-hom-Ringᵉ = preserves-mul-hom-Ringᵉ
    pr2ᵉ is-ring-homomorphism-hom-Ringᵉ = preserves-one-hom-Ringᵉ

    hom-multiplicative-monoid-hom-Ringᵉ :
      hom-Monoidᵉ
        ( multiplicative-monoid-Ringᵉ Rᵉ)
        ( multiplicative-monoid-Ringᵉ Sᵉ)
    pr1ᵉ (pr1ᵉ hom-multiplicative-monoid-hom-Ringᵉ) = map-hom-Ringᵉ
    pr2ᵉ (pr1ᵉ hom-multiplicative-monoid-hom-Ringᵉ) = preserves-mul-hom-Ringᵉ
    pr2ᵉ hom-multiplicative-monoid-hom-Ringᵉ = preserves-one-hom-Ringᵉ

    hom-semiring-hom-Ringᵉ :
      hom-Semiringᵉ (semiring-Ringᵉ Rᵉ) (semiring-Ringᵉ Sᵉ)
    pr1ᵉ hom-semiring-hom-Ringᵉ = hom-commutative-monoid-hom-Ringᵉ
    pr2ᵉ hom-semiring-hom-Ringᵉ = is-ring-homomorphism-hom-Ringᵉ
```

### The identity ring homomorphism

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  preserves-mul-id-hom-Ringᵉ : preserves-mul-hom-Abᵉ Rᵉ Rᵉ (id-hom-Abᵉ (ab-Ringᵉ Rᵉ))
  preserves-mul-id-hom-Ringᵉ = reflᵉ

  preserves-unit-id-hom-Ringᵉ : preserves-unit-hom-Abᵉ Rᵉ Rᵉ (id-hom-Abᵉ (ab-Ringᵉ Rᵉ))
  preserves-unit-id-hom-Ringᵉ = reflᵉ

  is-ring-homomorphism-id-hom-Ringᵉ :
    is-ring-homomorphism-hom-Abᵉ Rᵉ Rᵉ (id-hom-Abᵉ (ab-Ringᵉ Rᵉ))
  pr1ᵉ is-ring-homomorphism-id-hom-Ringᵉ = preserves-mul-id-hom-Ringᵉ
  pr2ᵉ is-ring-homomorphism-id-hom-Ringᵉ = preserves-unit-id-hom-Ringᵉ

  id-hom-Ringᵉ : hom-Ringᵉ Rᵉ Rᵉ
  pr1ᵉ id-hom-Ringᵉ = id-hom-Abᵉ (ab-Ringᵉ Rᵉ)
  pr2ᵉ id-hom-Ringᵉ = is-ring-homomorphism-id-hom-Ringᵉ
```

### Composition of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ)
  (gᵉ : hom-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  hom-ab-comp-hom-Ringᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Tᵉ)
  hom-ab-comp-hom-Ringᵉ =
    comp-hom-Abᵉ
      ( ab-Ringᵉ Rᵉ)
      ( ab-Ringᵉ Sᵉ)
      ( ab-Ringᵉ Tᵉ)
      ( hom-ab-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  hom-multiplicative-monoid-comp-hom-Ringᵉ :
    hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Tᵉ)
  hom-multiplicative-monoid-comp-hom-Ringᵉ =
    comp-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( multiplicative-monoid-Ringᵉ Tᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  preserves-mul-comp-hom-Ringᵉ : preserves-mul-hom-Abᵉ Rᵉ Tᵉ hom-ab-comp-hom-Ringᵉ
  preserves-mul-comp-hom-Ringᵉ =
    preserves-mul-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Tᵉ)
      ( hom-multiplicative-monoid-comp-hom-Ringᵉ)

  preserves-unit-comp-hom-Ringᵉ :
    preserves-unit-hom-Abᵉ Rᵉ Tᵉ hom-ab-comp-hom-Ringᵉ
  preserves-unit-comp-hom-Ringᵉ =
    preserves-unit-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Tᵉ)
      ( hom-multiplicative-monoid-comp-hom-Ringᵉ)

  is-ring-homomorphism-comp-hom-Ringᵉ :
    is-ring-homomorphism-hom-Abᵉ Rᵉ Tᵉ hom-ab-comp-hom-Ringᵉ
  pr1ᵉ is-ring-homomorphism-comp-hom-Ringᵉ = preserves-mul-comp-hom-Ringᵉ
  pr2ᵉ is-ring-homomorphism-comp-hom-Ringᵉ = preserves-unit-comp-hom-Ringᵉ

  comp-hom-Ringᵉ : hom-Ringᵉ Rᵉ Tᵉ
  pr1ᵉ comp-hom-Ringᵉ = hom-ab-comp-hom-Ringᵉ
  pr2ᵉ comp-hom-Ringᵉ = is-ring-homomorphism-comp-hom-Ringᵉ
```

### Homotopies of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  htpy-hom-Ringᵉ : hom-Ringᵉ Rᵉ Sᵉ → hom-Ringᵉ Rᵉ Sᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Ringᵉ fᵉ gᵉ = map-hom-Ringᵉ Rᵉ Sᵉ fᵉ ~ᵉ map-hom-Ringᵉ Rᵉ Sᵉ gᵉ

  refl-htpy-hom-Ringᵉ : (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) → htpy-hom-Ringᵉ fᵉ fᵉ
  refl-htpy-hom-Ringᵉ fᵉ = refl-htpyᵉ
```

### Evaluating ring homomorphisms at an element

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  ev-element-hom-Ringᵉ : type-Ringᵉ Rᵉ → hom-Ringᵉ Rᵉ Sᵉ → type-Ringᵉ Sᵉ
  ev-element-hom-Ringᵉ xᵉ fᵉ = map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ
```

## Properties

### Homotopies characterize identifications of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  htpy-eq-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) → htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ gᵉ
  htpy-eq-hom-Ringᵉ .fᵉ reflᵉ = refl-htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ

  is-torsorial-htpy-hom-Ringᵉ :
    is-torsorialᵉ (htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
  is-torsorial-htpy-hom-Ringᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpy-hom-Abᵉ
        ( ab-Ringᵉ Rᵉ)
        ( ab-Ringᵉ Sᵉ)
        ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ))
      ( is-prop-is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ)
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
      ( refl-htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
      ( is-ring-homomorphism-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  is-equiv-htpy-eq-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Rᵉ Sᵉ) → is-equivᵉ (htpy-eq-hom-Ringᵉ gᵉ)
  is-equiv-htpy-eq-hom-Ringᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-hom-Ringᵉ
      htpy-eq-hom-Ringᵉ

  extensionality-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Rᵉ Sᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Ringᵉ gᵉ) = htpy-eq-hom-Ringᵉ gᵉ
  pr2ᵉ (extensionality-hom-Ringᵉ gᵉ) = is-equiv-htpy-eq-hom-Ringᵉ gᵉ

  eq-htpy-hom-Ringᵉ :
    (gᵉ : hom-Ringᵉ Rᵉ Sᵉ) → htpy-hom-Ringᵉ Rᵉ Sᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-Ringᵉ gᵉ = map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-Ringᵉ gᵉ)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  ( Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) (Uᵉ : Ringᵉ l4ᵉ)
  ( hᵉ : hom-Ringᵉ Tᵉ Uᵉ)
  ( gᵉ : hom-Ringᵉ Sᵉ Tᵉ)
  ( fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  associative-comp-hom-Ringᵉ :
    comp-hom-Ringᵉ Rᵉ Sᵉ Uᵉ (comp-hom-Ringᵉ Sᵉ Tᵉ Uᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Ringᵉ Rᵉ Tᵉ Uᵉ hᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ)
  associative-comp-hom-Ringᵉ =
    eq-htpy-hom-Ringᵉ Rᵉ Uᵉ
      ( comp-hom-Ringᵉ Rᵉ Sᵉ Uᵉ (comp-hom-Ringᵉ Sᵉ Tᵉ Uᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Ringᵉ Rᵉ Tᵉ Uᵉ hᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)
```

### Unit laws for composition of ring homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  left-unit-law-comp-hom-Ringᵉ : comp-hom-Ringᵉ Rᵉ Sᵉ Sᵉ (id-hom-Ringᵉ Sᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Ringᵉ =
    eq-htpy-hom-Ringᵉ Rᵉ Sᵉ
      ( comp-hom-Ringᵉ Rᵉ Sᵉ Sᵉ (id-hom-Ringᵉ Sᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-hom-Ringᵉ : comp-hom-Ringᵉ Rᵉ Rᵉ Sᵉ fᵉ (id-hom-Ringᵉ Rᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Ringᵉ =
    eq-htpy-hom-Ringᵉ Rᵉ Sᵉ
      ( comp-hom-Ringᵉ Rᵉ Rᵉ Sᵉ fᵉ (id-hom-Ringᵉ Rᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)
```

### The underlying morphism of abelian groups of the identity ring homomorphism is the identity homomorphism of abelian groups

```agda
id-law-ab-Ringᵉ :
  { l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) →
  hom-ab-hom-Ringᵉ Rᵉ Rᵉ (id-hom-Ringᵉ Rᵉ) ＝ᵉ id-hom-Abᵉ (ab-Ringᵉ Rᵉ)
id-law-ab-Ringᵉ Rᵉ =
  eq-htpy-hom-Abᵉ
    ( ab-Ringᵉ Rᵉ)
    ( ab-Ringᵉ Rᵉ)
    ( refl-htpyᵉ)
```

### The underlying morphism of abelian groups of a composition of ring homomorphisms is a composition of homomorphisms of abelian groups

```agda
comp-law-ab-Ringᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (Tᵉ : Ringᵉ l3ᵉ) →
  ( gᵉ : hom-Ringᵉ Sᵉ Tᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
  hom-ab-hom-Ringᵉ Rᵉ Tᵉ (comp-hom-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ) ＝ᵉ
  comp-hom-Abᵉ
    ( ab-Ringᵉ Rᵉ)
    ( ab-Ringᵉ Sᵉ)
    ( ab-Ringᵉ Tᵉ)
    ( hom-ab-hom-Ringᵉ Sᵉ Tᵉ gᵉ)
    ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
comp-law-ab-Ringᵉ Rᵉ Sᵉ Tᵉ gᵉ fᵉ =
  eq-htpy-hom-Abᵉ
    ( ab-Ringᵉ Rᵉ)
    ( ab-Ringᵉ Tᵉ)
    ( refl-htpyᵉ)
```

### Any ring homomorphism preserves invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  preserves-invertible-elements-hom-Ringᵉ :
    {xᵉ : type-Ringᵉ Rᵉ} →
    is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-invertible-element-Ringᵉ Sᵉ (map-hom-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ)
  preserves-invertible-elements-hom-Ringᵉ =
    preserves-invertible-elements-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
```