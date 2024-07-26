# Isomorphisms of commutative rings

```agda
module commutative-algebra.isomorphisms-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.homomorphisms-commutative-ringsᵉ
open import commutative-algebra.invertible-elements-commutative-ringsᵉ
open import commutative-algebra.precategory-of-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.isomorphisms-abelian-groupsᵉ

open import ring-theory.isomorphisms-ringsᵉ
```

</details>

## Idea

Anᵉ **isomorphism**ᵉ ofᵉ
[commutativeᵉ rings](commutative-algebra.commutative-rings.mdᵉ) isᵉ anᵉ invertibleᵉ
[homomorphism](commutative-algebra.homomorphisms-commutative-rings.mdᵉ) ofᵉ
commutativeᵉ rings.ᵉ

## Definitions

### The predicate of being an isomorphism of rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ)
  where

  is-iso-prop-Commutative-Ringᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Commutative-Ringᵉ =
    is-iso-prop-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-iso-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Commutative-Ringᵉ =
    is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-prop-is-iso-Commutative-Ringᵉ : is-propᵉ is-iso-Commutative-Ringᵉ
  is-prop-is-iso-Commutative-Ringᵉ =
    is-prop-is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  hom-inv-is-iso-Commutative-Ringᵉ :
    is-iso-Commutative-Ringᵉ → hom-Commutative-Ringᵉ Bᵉ Aᵉ
  hom-inv-is-iso-Commutative-Ringᵉ =
    hom-inv-is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-section-hom-inv-is-iso-Commutative-Ringᵉ :
    (Uᵉ : is-iso-Commutative-Ringᵉ) →
    comp-hom-Commutative-Ringᵉ Bᵉ Aᵉ Bᵉ fᵉ (hom-inv-is-iso-Commutative-Ringᵉ Uᵉ) ＝ᵉ
    id-hom-Commutative-Ringᵉ Bᵉ
  is-section-hom-inv-is-iso-Commutative-Ringᵉ =
    is-section-hom-inv-is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Commutative-Ringᵉ :
    (Uᵉ : is-iso-Commutative-Ringᵉ) →
    comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Aᵉ (hom-inv-is-iso-Commutative-Ringᵉ Uᵉ) fᵉ ＝ᵉ
    id-hom-Commutative-Ringᵉ Aᵉ
  is-retraction-hom-inv-is-iso-Commutative-Ringᵉ =
    is-retraction-hom-inv-is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
      ( fᵉ)

  map-inv-is-iso-Commutative-Ringᵉ :
    is-iso-Commutative-Ringᵉ →
    type-Commutative-Ringᵉ Bᵉ → type-Commutative-Ringᵉ Aᵉ
  map-inv-is-iso-Commutative-Ringᵉ Uᵉ =
    map-hom-Commutative-Ringᵉ Bᵉ Aᵉ (hom-inv-is-iso-Commutative-Ringᵉ Uᵉ)

  is-section-map-inv-is-iso-Commutative-Ringᵉ :
    (Uᵉ : is-iso-Commutative-Ringᵉ) →
    map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ ∘ᵉ map-inv-is-iso-Commutative-Ringᵉ Uᵉ ~ᵉ idᵉ
  is-section-map-inv-is-iso-Commutative-Ringᵉ Uᵉ =
    htpy-eq-hom-Commutative-Ringᵉ Bᵉ Bᵉ
      ( comp-hom-Commutative-Ringᵉ Bᵉ Aᵉ Bᵉ fᵉ
        ( hom-inv-is-iso-Commutative-Ringᵉ Uᵉ))
      ( id-hom-Commutative-Ringᵉ Bᵉ)
      ( is-section-hom-inv-is-iso-Commutative-Ringᵉ Uᵉ)

  is-retraction-map-inv-is-iso-Commutative-Ringᵉ :
    (Uᵉ : is-iso-Commutative-Ringᵉ) →
    map-inv-is-iso-Commutative-Ringᵉ Uᵉ ∘ᵉ map-hom-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-is-iso-Commutative-Ringᵉ Uᵉ =
    htpy-eq-hom-Commutative-Ringᵉ Aᵉ Aᵉ
      ( comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Aᵉ
        ( hom-inv-is-iso-Commutative-Ringᵉ Uᵉ) fᵉ)
      ( id-hom-Commutative-Ringᵉ Aᵉ)
      ( is-retraction-hom-inv-is-iso-Commutative-Ringᵉ Uᵉ)
```

### Isomorphisms of commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  iso-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Commutative-Ringᵉ =
    iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  hom-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ → hom-Commutative-Ringᵉ Aᵉ Bᵉ
  hom-iso-Commutative-Ringᵉ =
    hom-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  map-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ → type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Bᵉ
  map-iso-Commutative-Ringᵉ =
    map-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-zero-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-iso-Commutative-Ringᵉ fᵉ (zero-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    zero-Commutative-Ringᵉ Bᵉ
  preserves-zero-iso-Commutative-Ringᵉ =
    preserves-zero-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-one-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-iso-Commutative-Ringᵉ fᵉ (one-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    one-Commutative-Ringᵉ Bᵉ
  preserves-one-iso-Commutative-Ringᵉ =
    preserves-one-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-add-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    map-iso-Commutative-Ringᵉ fᵉ (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ Bᵉ
      ( map-iso-Commutative-Ringᵉ fᵉ xᵉ)
      ( map-iso-Commutative-Ringᵉ fᵉ yᵉ)
  preserves-add-iso-Commutative-Ringᵉ =
    preserves-add-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-neg-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    map-iso-Commutative-Ringᵉ fᵉ (neg-Commutative-Ringᵉ Aᵉ xᵉ) ＝ᵉ
    neg-Commutative-Ringᵉ Bᵉ (map-iso-Commutative-Ringᵉ fᵉ xᵉ)
  preserves-neg-iso-Commutative-Ringᵉ =
    preserves-neg-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-mul-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    map-iso-Commutative-Ringᵉ fᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ Bᵉ
      ( map-iso-Commutative-Ringᵉ fᵉ xᵉ)
      ( map-iso-Commutative-Ringᵉ fᵉ yᵉ)
  preserves-mul-iso-Commutative-Ringᵉ =
    preserves-mul-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-iso-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    is-iso-Commutative-Ringᵉ Aᵉ Bᵉ (hom-iso-Commutative-Ringᵉ fᵉ)
  is-iso-iso-Commutative-Ringᵉ =
    is-iso-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  hom-inv-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ → hom-Commutative-Ringᵉ Bᵉ Aᵉ
  hom-inv-iso-Commutative-Ringᵉ =
    hom-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  map-inv-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ → type-Commutative-Ringᵉ Bᵉ → type-Commutative-Ringᵉ Aᵉ
  map-inv-iso-Commutative-Ringᵉ =
    map-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-zero-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-inv-iso-Commutative-Ringᵉ fᵉ (zero-Commutative-Ringᵉ Bᵉ) ＝ᵉ
    zero-Commutative-Ringᵉ Aᵉ
  preserves-zero-inv-iso-Commutative-Ringᵉ =
    preserves-zero-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-one-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-inv-iso-Commutative-Ringᵉ fᵉ (one-Commutative-Ringᵉ Bᵉ) ＝ᵉ
    one-Commutative-Ringᵉ Aᵉ
  preserves-one-inv-iso-Commutative-Ringᵉ =
    preserves-one-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-add-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ yᵉ : type-Commutative-Ringᵉ Bᵉ} →
    map-inv-iso-Commutative-Ringᵉ fᵉ (add-Commutative-Ringᵉ Bᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( map-inv-iso-Commutative-Ringᵉ fᵉ xᵉ)
      ( map-inv-iso-Commutative-Ringᵉ fᵉ yᵉ)
  preserves-add-inv-iso-Commutative-Ringᵉ =
    preserves-add-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-neg-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ : type-Commutative-Ringᵉ Bᵉ} →
    map-inv-iso-Commutative-Ringᵉ fᵉ (neg-Commutative-Ringᵉ Bᵉ xᵉ) ＝ᵉ
    neg-Commutative-Ringᵉ Aᵉ (map-inv-iso-Commutative-Ringᵉ fᵉ xᵉ)
  preserves-neg-inv-iso-Commutative-Ringᵉ =
    preserves-neg-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  preserves-mul-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) {xᵉ yᵉ : type-Commutative-Ringᵉ Bᵉ} →
    map-inv-iso-Commutative-Ringᵉ fᵉ (mul-Commutative-Ringᵉ Bᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ
      ( map-inv-iso-Commutative-Ringᵉ fᵉ xᵉ)
      ( map-inv-iso-Commutative-Ringᵉ fᵉ yᵉ)
  preserves-mul-inv-iso-Commutative-Ringᵉ =
    preserves-mul-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-section-hom-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    comp-hom-Commutative-Ringᵉ Bᵉ Aᵉ Bᵉ
      ( hom-iso-Commutative-Ringᵉ fᵉ)
      ( hom-inv-iso-Commutative-Ringᵉ fᵉ) ＝ᵉ
    id-hom-Commutative-Ringᵉ Bᵉ
  is-section-hom-inv-iso-Commutative-Ringᵉ =
    is-section-hom-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-section-map-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-iso-Commutative-Ringᵉ fᵉ ∘ᵉ map-inv-iso-Commutative-Ringᵉ fᵉ ~ᵉ idᵉ
  is-section-map-inv-iso-Commutative-Ringᵉ =
    is-section-map-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-retraction-hom-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    comp-hom-Commutative-Ringᵉ Aᵉ Bᵉ Aᵉ
      ( hom-inv-iso-Commutative-Ringᵉ fᵉ)
      ( hom-iso-Commutative-Ringᵉ fᵉ) ＝ᵉ
    id-hom-Commutative-Ringᵉ Aᵉ
  is-retraction-hom-inv-iso-Commutative-Ringᵉ =
    is-retraction-hom-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-retraction-map-inv-iso-Commutative-Ringᵉ :
    (fᵉ : iso-Commutative-Ringᵉ) →
    map-inv-iso-Commutative-Ringᵉ fᵉ ∘ᵉ map-iso-Commutative-Ringᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-iso-Commutative-Ringᵉ =
    is-retraction-map-inv-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
```

### The identity isomorphism of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-iso-id-hom-Commutative-Ringᵉ :
    is-iso-Commutative-Ringᵉ Aᵉ Aᵉ (id-hom-Commutative-Ringᵉ Aᵉ)
  is-iso-id-hom-Commutative-Ringᵉ =
    is-iso-id-hom-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  id-iso-Commutative-Ringᵉ : iso-Commutative-Ringᵉ Aᵉ Aᵉ
  id-iso-Commutative-Ringᵉ = id-iso-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Converting identifications of commutative rings to isomorphisms of commutative rings

```agda
iso-eq-Commutative-Ringᵉ :
  { lᵉ : Level} (Aᵉ Bᵉ : Commutative-Ringᵉ lᵉ) → Aᵉ ＝ᵉ Bᵉ → iso-Commutative-Ringᵉ Aᵉ Bᵉ
iso-eq-Commutative-Ringᵉ =
  iso-eq-Large-Precategoryᵉ Commutative-Ring-Large-Precategoryᵉ
```

## Properties

### A commutative ring homomorphism is an isomorphism if and only if the underlying homomorphism of abelian groups is an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Bᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  iso-ab-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-ab-Commutative-Ringᵉ =
    iso-ab-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  iso-ab-iso-ab-Commutative-Ringᵉ :
    iso-ab-Commutative-Ringᵉ →
    iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ)
  iso-ab-iso-ab-Commutative-Ringᵉ =
    iso-ab-iso-ab-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-iso-ab-hom-Commutative-Ringᵉ :
    hom-Commutative-Ringᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-ab-hom-Commutative-Ringᵉ =
    is-iso-ab-hom-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  is-iso-ab-is-iso-Commutative-Ringᵉ :
    (fᵉ : hom-Commutative-Ringᵉ Aᵉ Bᵉ) →
    is-iso-Commutative-Ringᵉ Aᵉ Bᵉ fᵉ → is-iso-ab-hom-Commutative-Ringᵉ fᵉ
  is-iso-ab-is-iso-Commutative-Ringᵉ =
    is-iso-ab-is-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  iso-ab-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ Aᵉ Bᵉ →
    iso-Abᵉ (ab-Commutative-Ringᵉ Aᵉ) (ab-Commutative-Ringᵉ Bᵉ)
  iso-ab-iso-Commutative-Ringᵉ =
    iso-ab-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)

  equiv-iso-ab-iso-Commutative-Ringᵉ :
    iso-Commutative-Ringᵉ Aᵉ Bᵉ ≃ᵉ iso-ab-Commutative-Ringᵉ
  equiv-iso-ab-iso-Commutative-Ringᵉ =
    equiv-iso-ab-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Bᵉ)
```

### Characterizing identifications of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  abstract
    is-torsorial-iso-Commutative-Ringᵉ :
      is-torsorialᵉ (λ (Bᵉ : Commutative-Ringᵉ lᵉ) → iso-Commutative-Ringᵉ Aᵉ Bᵉ)
    is-torsorial-iso-Commutative-Ringᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-iso-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ))
        ( is-prop-is-commutative-Ringᵉ)
        ( ring-Commutative-Ringᵉ Aᵉ)
        ( id-iso-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ))
        ( commutative-mul-Commutative-Ringᵉ Aᵉ)

  is-equiv-iso-eq-Commutative-Ringᵉ :
    (Bᵉ : Commutative-Ringᵉ lᵉ) → is-equivᵉ (iso-eq-Commutative-Ringᵉ Aᵉ Bᵉ)
  is-equiv-iso-eq-Commutative-Ringᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-Commutative-Ringᵉ)
      ( iso-eq-Commutative-Ringᵉ Aᵉ)

  extensionality-Commutative-Ringᵉ :
    (Bᵉ : Commutative-Ringᵉ lᵉ) → (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ iso-Commutative-Ringᵉ Aᵉ Bᵉ
  pr1ᵉ (extensionality-Commutative-Ringᵉ Bᵉ) = iso-eq-Commutative-Ringᵉ Aᵉ Bᵉ
  pr2ᵉ (extensionality-Commutative-Ringᵉ Bᵉ) = is-equiv-iso-eq-Commutative-Ringᵉ Bᵉ

  eq-iso-Commutative-Ringᵉ :
    (Bᵉ : Commutative-Ringᵉ lᵉ) → iso-Commutative-Ringᵉ Aᵉ Bᵉ → Aᵉ ＝ᵉ Bᵉ
  eq-iso-Commutative-Ringᵉ Bᵉ =
    map-inv-is-equivᵉ (is-equiv-iso-eq-Commutative-Ringᵉ Bᵉ)
```

### Any isomorphism of commutative rings preserves and reflects invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : Commutative-Ringᵉ l2ᵉ)
  (fᵉ : iso-Commutative-Ringᵉ Aᵉ Sᵉ)
  where

  preserves-invertible-elements-iso-Commutative-Ringᵉ :
    {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ →
    is-invertible-element-Commutative-Ringᵉ Sᵉ (map-iso-Commutative-Ringᵉ Aᵉ Sᵉ fᵉ xᵉ)
  preserves-invertible-elements-iso-Commutative-Ringᵉ =
    preserves-invertible-elements-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Sᵉ)
      ( fᵉ)

  reflects-invertible-elements-iso-Commutative-Ringᵉ :
    {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-invertible-element-Commutative-Ringᵉ Sᵉ
      ( map-iso-Commutative-Ringᵉ Aᵉ Sᵉ fᵉ xᵉ) →
    is-invertible-element-Commutative-Ringᵉ Aᵉ xᵉ
  reflects-invertible-elements-iso-Commutative-Ringᵉ =
    reflects-invertible-elements-iso-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( ring-Commutative-Ringᵉ Sᵉ)
      ( fᵉ)
```