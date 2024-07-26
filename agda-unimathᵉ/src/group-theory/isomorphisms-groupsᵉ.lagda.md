# Isomorphisms of groups

```agda
module group-theory.isomorphisms-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.category-of-semigroupsᵉ
open import group-theory.equivalences-semigroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-semigroupsᵉ
open import group-theory.precategory-of-groupsᵉ
```

</details>

## Definitions

### The predicate of being an isomorphism of groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  is-iso-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Groupᵉ =
    is-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  is-prop-is-iso-Groupᵉ : is-propᵉ is-iso-Groupᵉ
  is-prop-is-iso-Groupᵉ =
    is-prop-is-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  is-iso-prop-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Groupᵉ =
    is-iso-prop-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  hom-inv-is-iso-Groupᵉ :
    is-iso-Groupᵉ → hom-Groupᵉ Hᵉ Gᵉ
  hom-inv-is-iso-Groupᵉ =
    hom-inv-is-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  map-inv-is-iso-Groupᵉ :
    is-iso-Groupᵉ → type-Groupᵉ Hᵉ → type-Groupᵉ Gᵉ
  map-inv-is-iso-Groupᵉ =
    map-inv-is-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  is-section-hom-inv-is-iso-Groupᵉ :
    (Uᵉ : is-iso-Groupᵉ) →
    comp-hom-Groupᵉ Hᵉ Gᵉ Hᵉ fᵉ (hom-inv-is-iso-Groupᵉ Uᵉ) ＝ᵉ
    id-hom-Groupᵉ Hᵉ
  is-section-hom-inv-is-iso-Groupᵉ =
    is-section-hom-inv-is-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)

  is-section-map-inv-is-iso-Groupᵉ :
    (Uᵉ : is-iso-Groupᵉ) →
    ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ ∘ᵉ map-inv-is-iso-Groupᵉ Uᵉ) ~ᵉ idᵉ
  is-section-map-inv-is-iso-Groupᵉ =
    is-section-map-inv-is-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Groupᵉ :
    (Uᵉ : is-iso-Groupᵉ) →
    comp-hom-Groupᵉ Gᵉ Hᵉ Gᵉ (hom-inv-is-iso-Groupᵉ Uᵉ) fᵉ ＝ᵉ
    id-hom-Groupᵉ Gᵉ
  is-retraction-hom-inv-is-iso-Groupᵉ =
    is-retraction-hom-inv-is-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)

  is-retraction-map-inv-is-iso-Groupᵉ :
    (Uᵉ : is-iso-Groupᵉ) →
    ( map-inv-is-iso-Groupᵉ Uᵉ ∘ᵉ map-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-is-iso-Groupᵉ =
    is-retraction-map-inv-is-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( fᵉ)
```

### The predicate of being an equivalence of groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  is-equiv-hom-Groupᵉ : hom-Groupᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-hom-Groupᵉ =
    is-equiv-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  equiv-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Groupᵉ = equiv-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)
```

### Group isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  iso-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Groupᵉ = iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  hom-iso-Groupᵉ : iso-Groupᵉ → hom-Groupᵉ Gᵉ Hᵉ
  hom-iso-Groupᵉ = hom-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  map-iso-Groupᵉ : iso-Groupᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ
  map-iso-Groupᵉ = map-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  preserves-mul-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    map-iso-Groupᵉ fᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Hᵉ (map-iso-Groupᵉ fᵉ xᵉ) (map-iso-Groupᵉ fᵉ yᵉ)
  preserves-mul-iso-Groupᵉ =
    preserves-mul-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-iso-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) → is-iso-Groupᵉ Gᵉ Hᵉ (hom-iso-Groupᵉ fᵉ)
  is-iso-iso-Groupᵉ =
    is-iso-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  hom-inv-iso-Groupᵉ : iso-Groupᵉ → hom-Groupᵉ Hᵉ Gᵉ
  hom-inv-iso-Groupᵉ =
    hom-inv-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  map-inv-iso-Groupᵉ : iso-Groupᵉ → type-Groupᵉ Hᵉ → type-Groupᵉ Gᵉ
  map-inv-iso-Groupᵉ =
    map-inv-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  preserves-mul-inv-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) {xᵉ yᵉ : type-Groupᵉ Hᵉ} →
    map-inv-iso-Groupᵉ fᵉ (mul-Groupᵉ Hᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ (map-inv-iso-Groupᵉ fᵉ xᵉ) (map-inv-iso-Groupᵉ fᵉ yᵉ)
  preserves-mul-inv-iso-Groupᵉ =
    preserves-mul-inv-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-section-hom-inv-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) →
    comp-hom-Groupᵉ Hᵉ Gᵉ Hᵉ (hom-iso-Groupᵉ fᵉ) (hom-inv-iso-Groupᵉ fᵉ) ＝ᵉ
    id-hom-Groupᵉ Hᵉ
  is-section-hom-inv-iso-Groupᵉ =
    is-section-hom-inv-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-section-map-inv-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) →
    ( map-iso-Groupᵉ fᵉ ∘ᵉ map-inv-iso-Groupᵉ fᵉ) ~ᵉ idᵉ
  is-section-map-inv-iso-Groupᵉ =
    is-section-map-inv-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-retraction-hom-inv-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) →
    comp-hom-Groupᵉ Gᵉ Hᵉ Gᵉ (hom-inv-iso-Groupᵉ fᵉ) (hom-iso-Groupᵉ fᵉ) ＝ᵉ
    id-hom-Groupᵉ Gᵉ
  is-retraction-hom-inv-iso-Groupᵉ =
    is-retraction-hom-inv-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)

  is-retraction-map-inv-iso-Groupᵉ :
    (fᵉ : iso-Groupᵉ) →
    ( map-inv-iso-Groupᵉ fᵉ ∘ᵉ map-iso-Groupᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-iso-Groupᵉ =
    is-retraction-map-inv-iso-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)

  is-iso-is-equiv-hom-Groupᵉ :
    (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → is-equiv-hom-Groupᵉ Gᵉ Hᵉ fᵉ → is-iso-Groupᵉ Gᵉ Hᵉ fᵉ
  is-iso-is-equiv-hom-Groupᵉ =
    is-iso-is-equiv-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-equiv-is-iso-Groupᵉ :
    (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → is-iso-Groupᵉ Gᵉ Hᵉ fᵉ → is-equiv-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  is-equiv-is-iso-Groupᵉ =
    is-equiv-is-iso-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  equiv-iso-equiv-Groupᵉ : equiv-Groupᵉ Gᵉ Hᵉ ≃ᵉ iso-Groupᵉ
  equiv-iso-equiv-Groupᵉ =
    equiv-iso-equiv-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  iso-equiv-Groupᵉ : equiv-Groupᵉ Gᵉ Hᵉ → iso-Groupᵉ
  iso-equiv-Groupᵉ = map-equivᵉ equiv-iso-equiv-Groupᵉ
```

### The identity isomorphism

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  id-iso-Groupᵉ : iso-Groupᵉ Gᵉ Gᵉ
  id-iso-Groupᵉ = id-iso-Large-Precategoryᵉ Group-Large-Precategoryᵉ {Xᵉ = Gᵉ}
```

## Properties

### The total space of group isomorphisms from a given group `G` is contractible

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  iso-eq-Groupᵉ : (Hᵉ : Groupᵉ lᵉ) → Idᵉ Gᵉ Hᵉ → iso-Groupᵉ Gᵉ Hᵉ
  iso-eq-Groupᵉ = iso-eq-Large-Precategoryᵉ Group-Large-Precategoryᵉ Gᵉ

  abstract
    extensionality-Group'ᵉ : (Hᵉ : Groupᵉ lᵉ) → Idᵉ Gᵉ Hᵉ ≃ᵉ iso-Groupᵉ Gᵉ Hᵉ
    extensionality-Group'ᵉ Hᵉ =
      ( extensionality-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)) ∘eᵉ
      ( equiv-ap-inclusion-subtypeᵉ is-group-prop-Semigroupᵉ {sᵉ = Gᵉ} {tᵉ = Hᵉ})

  abstract
    is-torsorial-iso-Groupᵉ : is-torsorialᵉ (λ (Hᵉ : Groupᵉ lᵉ) → iso-Groupᵉ Gᵉ Hᵉ)
    is-torsorial-iso-Groupᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (Groupᵉ lᵉ) (Idᵉ Gᵉ))
        ( equiv-totᵉ extensionality-Group'ᵉ)
        ( is-torsorial-Idᵉ Gᵉ)
```

### Group isomorphisms are stable by composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  where

  comp-iso-Groupᵉ : iso-Groupᵉ Hᵉ Kᵉ → iso-Groupᵉ Gᵉ Hᵉ → iso-Groupᵉ Gᵉ Kᵉ
  comp-iso-Groupᵉ =
    comp-iso-Large-Precategoryᵉ Group-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ} {Zᵉ = Kᵉ}
```

### Group isomorphisms are stable by inversion

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  inv-iso-Groupᵉ : iso-Groupᵉ Gᵉ Hᵉ → iso-Groupᵉ Hᵉ Gᵉ
  inv-iso-Groupᵉ =
    inv-iso-Large-Precategoryᵉ Group-Large-Precategoryᵉ {Xᵉ = Gᵉ} {Yᵉ = Hᵉ}
```