# The full subsemigroup of a semigroup

```agda
module group-theory.full-subsemigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.equivalences-semigroupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.isomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsemigroupsᵉ
open import group-theory.subsets-semigroupsᵉ
```

</details>

## Idea

Theᵉ **fullᵉ subsemigroup**ᵉ ofᵉ aᵉ [semigroup](group-theory.semigroups.mdᵉ) `G`ᵉ isᵉ
theᵉ [subsemigroup](group-theory.subsemigroups.mdᵉ) consistingᵉ ofᵉ allᵉ elementsᵉ ofᵉ
theᵉ semigroupᵉ `G`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ fullᵉ subsemigroupᵉ isᵉ theᵉ subsemigroupᵉ
whoseᵉ underlyingᵉ subsetᵉ isᵉ theᵉ [fullᵉ subset](foundation.full-subtypes.mdᵉ) ofᵉ theᵉ
semigroup.ᵉ

## Definition

### Full subsemigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Subsemigroupᵉ l2ᵉ Gᵉ)
  where

  is-full-prop-Subsemigroupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-prop-Subsemigroupᵉ = is-full-subtype-Propᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ)

  is-full-Subsemigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-Subsemigroupᵉ = type-Propᵉ is-full-prop-Subsemigroupᵉ

  is-prop-is-full-Subsemigroupᵉ : is-propᵉ is-full-Subsemigroupᵉ
  is-prop-is-full-Subsemigroupᵉ = is-prop-type-Propᵉ is-full-prop-Subsemigroupᵉ
```

### The full subsemigroup at each universe level

```agda
subset-full-Subsemigroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) → subset-Semigroupᵉ l2ᵉ Gᵉ
subset-full-Subsemigroupᵉ l2ᵉ Gᵉ = full-subtypeᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)

type-full-Subsemigroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-full-Subsemigroupᵉ l2ᵉ Gᵉ = type-full-subtypeᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)

is-closed-under-multiplication-full-Subsemigroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) →
  is-closed-under-multiplication-subset-Semigroupᵉ Gᵉ
    ( subset-full-Subsemigroupᵉ l2ᵉ Gᵉ)
is-closed-under-multiplication-full-Subsemigroupᵉ Gᵉ {xᵉ} {yᵉ} _ _ =
  is-in-full-subtypeᵉ (mul-Semigroupᵉ Gᵉ xᵉ yᵉ)

full-Subsemigroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) → Subsemigroupᵉ l2ᵉ Gᵉ
pr1ᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ) =
  subset-full-Subsemigroupᵉ l2ᵉ Gᵉ
pr2ᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ) {xᵉ} {yᵉ} =
  is-closed-under-multiplication-full-Subsemigroupᵉ Gᵉ {xᵉ} {yᵉ}

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ)
  where

  inclusion-full-Subsemigroupᵉ : type-full-Subsemigroupᵉ l2ᵉ Gᵉ → type-Semigroupᵉ Gᵉ
  inclusion-full-Subsemigroupᵉ =
    inclusion-Subsemigroupᵉ Gᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ)

  is-equiv-inclusion-full-Subsemigroupᵉ : is-equivᵉ inclusion-full-Subsemigroupᵉ
  is-equiv-inclusion-full-Subsemigroupᵉ = is-equiv-inclusion-full-subtypeᵉ

  equiv-inclusion-full-Subsemigroupᵉ :
    type-full-Subsemigroupᵉ l2ᵉ Gᵉ ≃ᵉ type-Semigroupᵉ Gᵉ
  pr1ᵉ equiv-inclusion-full-Subsemigroupᵉ = inclusion-full-Subsemigroupᵉ
  pr2ᵉ equiv-inclusion-full-Subsemigroupᵉ = is-equiv-inclusion-full-Subsemigroupᵉ

  semigroup-full-Subsemigroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-full-Subsemigroupᵉ =
    semigroup-Subsemigroupᵉ Gᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ)

  hom-inclusion-full-Subsemigroupᵉ : hom-Semigroupᵉ semigroup-full-Subsemigroupᵉ Gᵉ
  hom-inclusion-full-Subsemigroupᵉ =
    hom-inclusion-Subsemigroupᵉ Gᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ)

  preserves-mul-inclusion-full-Subsemigroupᵉ :
    preserves-mul-Semigroupᵉ
      ( semigroup-full-Subsemigroupᵉ)
      ( Gᵉ)
      ( inclusion-full-Subsemigroupᵉ)
  preserves-mul-inclusion-full-Subsemigroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subsemigroupᵉ Gᵉ (full-Subsemigroupᵉ l2ᵉ Gᵉ) {xᵉ} {yᵉ}

  equiv-semigroup-inclusion-full-Subsemigroupᵉ :
    equiv-Semigroupᵉ semigroup-full-Subsemigroupᵉ Gᵉ
  pr1ᵉ equiv-semigroup-inclusion-full-Subsemigroupᵉ =
    equiv-inclusion-full-Subsemigroupᵉ
  pr2ᵉ equiv-semigroup-inclusion-full-Subsemigroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-full-Subsemigroupᵉ {xᵉ} {yᵉ}

  iso-full-Subsemigroupᵉ : iso-Semigroupᵉ semigroup-full-Subsemigroupᵉ Gᵉ
  iso-full-Subsemigroupᵉ =
    iso-equiv-Semigroupᵉ
      ( semigroup-full-Subsemigroupᵉ)
      ( Gᵉ)
      ( equiv-semigroup-inclusion-full-Subsemigroupᵉ)

  inv-iso-full-Subsemigroupᵉ :
    iso-Semigroupᵉ Gᵉ semigroup-full-Subsemigroupᵉ
  inv-iso-full-Subsemigroupᵉ =
    inv-iso-Semigroupᵉ semigroup-full-Subsemigroupᵉ Gᵉ iso-full-Subsemigroupᵉ
```

## Properties

### A subsemigroup is full if and only if the inclusion is an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Subsemigroupᵉ l2ᵉ Gᵉ)
  where

  is-iso-inclusion-is-full-Subsemigroupᵉ :
    is-full-Subsemigroupᵉ Gᵉ Hᵉ →
    is-iso-Semigroupᵉ
      ( semigroup-Subsemigroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( hom-inclusion-Subsemigroupᵉ Gᵉ Hᵉ)
  is-iso-inclusion-is-full-Subsemigroupᵉ Kᵉ =
    is-iso-is-equiv-hom-Semigroupᵉ
      ( semigroup-Subsemigroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( hom-inclusion-Subsemigroupᵉ Gᵉ Hᵉ)
      ( is-equiv-inclusion-is-full-subtypeᵉ (subset-Subsemigroupᵉ Gᵉ Hᵉ) Kᵉ)

  iso-inclusion-is-full-Subsemigroupᵉ :
    is-full-Subsemigroupᵉ Gᵉ Hᵉ → iso-Semigroupᵉ (semigroup-Subsemigroupᵉ Gᵉ Hᵉ) Gᵉ
  pr1ᵉ (iso-inclusion-is-full-Subsemigroupᵉ Kᵉ) =
    hom-inclusion-Subsemigroupᵉ Gᵉ Hᵉ
  pr2ᵉ (iso-inclusion-is-full-Subsemigroupᵉ Kᵉ) =
    is-iso-inclusion-is-full-Subsemigroupᵉ Kᵉ

  is-full-is-iso-inclusion-Subsemigroupᵉ :
    is-iso-Semigroupᵉ
      ( semigroup-Subsemigroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( hom-inclusion-Subsemigroupᵉ Gᵉ Hᵉ) →
    is-full-Subsemigroupᵉ Gᵉ Hᵉ
  is-full-is-iso-inclusion-Subsemigroupᵉ Kᵉ =
    is-full-is-equiv-inclusion-subtypeᵉ
      ( subset-Subsemigroupᵉ Gᵉ Hᵉ)
      ( is-equiv-is-iso-Semigroupᵉ
        ( semigroup-Subsemigroupᵉ Gᵉ Hᵉ)
        ( Gᵉ)
        ( hom-inclusion-Subsemigroupᵉ Gᵉ Hᵉ)
        ( Kᵉ))
```