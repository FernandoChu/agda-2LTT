# Isomorphisms of rings

```agda
module ring-theory.isomorphisms-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.propositionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.isomorphisms-abelian-groupsᵉ
open import group-theory.isomorphisms-monoidsᵉ

open import ring-theory.homomorphisms-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.precategory-of-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Definition

### The predicate of being an isomorphism of rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ) (fᵉ : hom-Ringᵉ Rᵉ Sᵉ)
  where

  is-iso-prop-Ringᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Ringᵉ =
    is-iso-prop-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ} fᵉ

  is-iso-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Ringᵉ =
    is-iso-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ} fᵉ

  is-prop-is-iso-Ringᵉ : is-propᵉ is-iso-Ringᵉ
  is-prop-is-iso-Ringᵉ =
    is-prop-is-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}
      ( fᵉ)

  hom-inv-is-iso-Ringᵉ : is-iso-Ringᵉ → hom-Ringᵉ Sᵉ Rᵉ
  hom-inv-is-iso-Ringᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}
      ( fᵉ)

  is-section-hom-inv-is-iso-Ringᵉ :
    (Uᵉ : is-iso-Ringᵉ) →
    comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ fᵉ (hom-inv-is-iso-Ringᵉ Uᵉ) ＝ᵉ id-hom-Ringᵉ Sᵉ
  is-section-hom-inv-is-iso-Ringᵉ =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Ringᵉ :
    (Uᵉ : is-iso-Ringᵉ) →
    comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ (hom-inv-is-iso-Ringᵉ Uᵉ) fᵉ ＝ᵉ id-hom-Ringᵉ Rᵉ
  is-retraction-hom-inv-is-iso-Ringᵉ =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}
      ( fᵉ)

  map-inv-is-iso-Ringᵉ : is-iso-Ringᵉ → type-Ringᵉ Sᵉ → type-Ringᵉ Rᵉ
  map-inv-is-iso-Ringᵉ Uᵉ =
    map-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-is-iso-Ringᵉ Uᵉ)

  is-section-map-inv-is-iso-Ringᵉ :
    (Uᵉ : is-iso-Ringᵉ) → map-hom-Ringᵉ Rᵉ Sᵉ fᵉ ∘ᵉ map-inv-is-iso-Ringᵉ Uᵉ ~ᵉ idᵉ
  is-section-map-inv-is-iso-Ringᵉ Uᵉ =
    htpy-eq-hom-Ringᵉ Sᵉ Sᵉ
      ( comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ fᵉ (hom-inv-is-iso-Ringᵉ Uᵉ))
      ( id-hom-Ringᵉ Sᵉ)
      ( is-section-hom-inv-is-iso-Ringᵉ Uᵉ)

  is-retraction-map-inv-is-iso-Ringᵉ :
    (Uᵉ : is-iso-Ringᵉ) → map-inv-is-iso-Ringᵉ Uᵉ ∘ᵉ map-hom-Ringᵉ Rᵉ Sᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-is-iso-Ringᵉ Uᵉ =
    htpy-eq-hom-Ringᵉ Rᵉ Rᵉ
      ( comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ (hom-inv-is-iso-Ringᵉ Uᵉ) fᵉ)
      ( id-hom-Ringᵉ Rᵉ)
      ( is-retraction-hom-inv-is-iso-Ringᵉ Uᵉ)
```

### Isomorphisms of rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  iso-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Ringᵉ = iso-Large-Precategoryᵉ Ring-Large-Precategoryᵉ Rᵉ Sᵉ

  hom-iso-Ringᵉ : iso-Ringᵉ → hom-Ringᵉ Rᵉ Sᵉ
  hom-iso-Ringᵉ =
    hom-iso-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ}

  map-iso-Ringᵉ : iso-Ringᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Sᵉ
  map-iso-Ringᵉ fᵉ = map-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  preserves-zero-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-iso-Ringᵉ fᵉ (zero-Ringᵉ Rᵉ) ＝ᵉ zero-Ringᵉ Sᵉ
  preserves-zero-iso-Ringᵉ fᵉ = preserves-zero-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  preserves-one-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-iso-Ringᵉ fᵉ (one-Ringᵉ Rᵉ) ＝ᵉ one-Ringᵉ Sᵉ
  preserves-one-iso-Ringᵉ fᵉ = preserves-one-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  preserves-add-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    map-iso-Ringᵉ fᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Sᵉ (map-iso-Ringᵉ fᵉ xᵉ) (map-iso-Ringᵉ fᵉ yᵉ)
  preserves-add-iso-Ringᵉ fᵉ = preserves-add-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  preserves-neg-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    map-iso-Ringᵉ fᵉ (neg-Ringᵉ Rᵉ xᵉ) ＝ᵉ neg-Ringᵉ Sᵉ (map-iso-Ringᵉ fᵉ xᵉ)
  preserves-neg-iso-Ringᵉ fᵉ = preserves-neg-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  preserves-mul-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    map-iso-Ringᵉ fᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    mul-Ringᵉ Sᵉ (map-iso-Ringᵉ fᵉ xᵉ) (map-iso-Ringᵉ fᵉ yᵉ)
  preserves-mul-iso-Ringᵉ fᵉ =
    preserves-mul-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)

  is-iso-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → is-iso-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)
  is-iso-iso-Ringᵉ =
    is-iso-iso-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ}

  hom-inv-iso-Ringᵉ : iso-Ringᵉ → hom-Ringᵉ Sᵉ Rᵉ
  hom-inv-iso-Ringᵉ =
    hom-inv-iso-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ} {Yᵉ = Sᵉ}

  map-inv-iso-Ringᵉ : iso-Ringᵉ → type-Ringᵉ Sᵉ → type-Ringᵉ Rᵉ
  map-inv-iso-Ringᵉ fᵉ = map-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  preserves-zero-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-inv-iso-Ringᵉ fᵉ (zero-Ringᵉ Sᵉ) ＝ᵉ zero-Ringᵉ Rᵉ
  preserves-zero-inv-iso-Ringᵉ fᵉ =
    preserves-zero-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  preserves-one-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-inv-iso-Ringᵉ fᵉ (one-Ringᵉ Sᵉ) ＝ᵉ one-Ringᵉ Rᵉ
  preserves-one-inv-iso-Ringᵉ fᵉ =
    preserves-one-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  preserves-add-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ yᵉ : type-Ringᵉ Sᵉ} →
    map-inv-iso-Ringᵉ fᵉ (add-Ringᵉ Sᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (map-inv-iso-Ringᵉ fᵉ xᵉ) (map-inv-iso-Ringᵉ fᵉ yᵉ)
  preserves-add-inv-iso-Ringᵉ fᵉ =
    preserves-add-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  preserves-neg-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ : type-Ringᵉ Sᵉ} →
    map-inv-iso-Ringᵉ fᵉ (neg-Ringᵉ Sᵉ xᵉ) ＝ᵉ neg-Ringᵉ Rᵉ (map-inv-iso-Ringᵉ fᵉ xᵉ)
  preserves-neg-inv-iso-Ringᵉ fᵉ =
    preserves-neg-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  preserves-mul-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) {xᵉ yᵉ : type-Ringᵉ Sᵉ} →
    map-inv-iso-Ringᵉ fᵉ (mul-Ringᵉ Sᵉ xᵉ yᵉ) ＝ᵉ
    mul-Ringᵉ Rᵉ (map-inv-iso-Ringᵉ fᵉ xᵉ) (map-inv-iso-Ringᵉ fᵉ yᵉ)
  preserves-mul-inv-iso-Ringᵉ fᵉ =
    preserves-mul-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)

  is-section-hom-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) →
    comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ) (hom-inv-iso-Ringᵉ fᵉ) ＝ᵉ id-hom-Ringᵉ Sᵉ
  is-section-hom-inv-iso-Ringᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}

  is-section-map-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-iso-Ringᵉ fᵉ ∘ᵉ map-inv-iso-Ringᵉ fᵉ ~ᵉ idᵉ
  is-section-map-inv-iso-Ringᵉ fᵉ =
    htpy-eq-hom-Ringᵉ Sᵉ Sᵉ
      ( comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ) (hom-inv-iso-Ringᵉ fᵉ))
      ( id-hom-Ringᵉ Sᵉ)
      ( is-section-hom-inv-iso-Ringᵉ fᵉ)

  is-retraction-hom-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) →
    comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ) (hom-iso-Ringᵉ fᵉ) ＝ᵉ id-hom-Ringᵉ Rᵉ
  is-retraction-hom-inv-iso-Ringᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      { Xᵉ = Rᵉ}
      { Yᵉ = Sᵉ}

  is-retraction-map-inv-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) → map-inv-iso-Ringᵉ fᵉ ∘ᵉ map-iso-Ringᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-iso-Ringᵉ fᵉ =
    htpy-eq-hom-Ringᵉ Rᵉ Rᵉ
      ( comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ) (hom-iso-Ringᵉ fᵉ))
      ( id-hom-Ringᵉ Rᵉ)
      ( is-retraction-hom-inv-iso-Ringᵉ fᵉ)

  iso-multiplicative-monoid-iso-Ringᵉ :
    (fᵉ : iso-Ringᵉ) →
    iso-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ) (multiplicative-monoid-Ringᵉ Sᵉ)
  pr1ᵉ (iso-multiplicative-monoid-iso-Ringᵉ fᵉ) =
    hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)
  pr1ᵉ (pr2ᵉ (iso-multiplicative-monoid-iso-Ringᵉ fᵉ)) =
    hom-multiplicative-monoid-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (iso-multiplicative-monoid-iso-Ringᵉ fᵉ))) =
    eq-htpy-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( comp-hom-Monoidᵉ
        ( multiplicative-monoid-Ringᵉ Sᵉ)
        ( multiplicative-monoid-Ringᵉ Rᵉ)
        ( multiplicative-monoid-Ringᵉ Sᵉ)
        ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ))
        ( hom-multiplicative-monoid-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ)))
      ( id-hom-Monoidᵉ (multiplicative-monoid-Ringᵉ Sᵉ))
      ( is-section-map-inv-iso-Ringᵉ fᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (iso-multiplicative-monoid-iso-Ringᵉ fᵉ))) =
    eq-htpy-hom-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( comp-hom-Monoidᵉ
        ( multiplicative-monoid-Ringᵉ Rᵉ)
        ( multiplicative-monoid-Ringᵉ Sᵉ)
        ( multiplicative-monoid-Ringᵉ Rᵉ)
        ( hom-multiplicative-monoid-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-iso-Ringᵉ fᵉ))
        ( hom-multiplicative-monoid-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ fᵉ)))
      ( id-hom-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ))
      ( is-retraction-map-inv-iso-Ringᵉ fᵉ)
```

### The identity isomorphism of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-iso-id-hom-Ringᵉ : is-iso-Ringᵉ Rᵉ Rᵉ (id-hom-Ringᵉ Rᵉ)
  is-iso-id-hom-Ringᵉ =
    is-iso-id-hom-Large-Precategoryᵉ Ring-Large-Precategoryᵉ {Xᵉ = Rᵉ}

  id-iso-Ringᵉ : iso-Ringᵉ Rᵉ Rᵉ
  pr1ᵉ id-iso-Ringᵉ = id-hom-Ringᵉ Rᵉ
  pr2ᵉ id-iso-Ringᵉ = is-iso-id-hom-Ringᵉ
```

### Converting identifications of rings to isomorphisms of rings

```agda
iso-eq-Ringᵉ :
  { lᵉ : Level} (Rᵉ Sᵉ : Ringᵉ lᵉ) → Rᵉ ＝ᵉ Sᵉ → iso-Ringᵉ Rᵉ Sᵉ
iso-eq-Ringᵉ Rᵉ Sᵉ = iso-eq-Large-Precategoryᵉ Ring-Large-Precategoryᵉ Rᵉ Sᵉ
```

## Properties

### A ring homomorphism is an isomorphism if and only if the underlying homomorphism of abelian groups is an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  where

  iso-ab-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-ab-Ringᵉ =
    Σᵉ ( iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ))
      ( λ fᵉ →
        is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ
          ( hom-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ))

  iso-ab-iso-ab-Ringᵉ :
    iso-ab-Ringᵉ → iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)
  iso-ab-iso-ab-Ringᵉ = pr1ᵉ

  is-iso-ab-hom-Ringᵉ : hom-Ringᵉ Rᵉ Sᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-ab-hom-Ringᵉ fᵉ =
    is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  is-iso-ab-is-iso-Ringᵉ :
    (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
    is-iso-Ringᵉ Rᵉ Sᵉ fᵉ → is-iso-ab-hom-Ringᵉ fᵉ
  pr1ᵉ (is-iso-ab-is-iso-Ringᵉ fᵉ Uᵉ) =
    hom-ab-hom-Ringᵉ Sᵉ Rᵉ (hom-inv-is-iso-Ringᵉ Rᵉ Sᵉ fᵉ Uᵉ)
  pr1ᵉ (pr2ᵉ (is-iso-ab-is-iso-Ringᵉ fᵉ Uᵉ)) =
    apᵉ
      ( hom-ab-hom-Ringᵉ Sᵉ Sᵉ)
      ( is-section-hom-inv-is-iso-Ringᵉ Rᵉ Sᵉ fᵉ Uᵉ)
  pr2ᵉ (pr2ᵉ (is-iso-ab-is-iso-Ringᵉ fᵉ Uᵉ)) =
    apᵉ
      ( hom-ab-hom-Ringᵉ Rᵉ Rᵉ)
      ( is-retraction-hom-inv-is-iso-Ringᵉ Rᵉ Sᵉ fᵉ Uᵉ)

  abstract
    preserves-mul-inv-is-iso-Abᵉ :
      (fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
      (Uᵉ : is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ) →
      preserves-mul-hom-Abᵉ Rᵉ Sᵉ fᵉ →
      preserves-mul-hom-Abᵉ Sᵉ Rᵉ
        ( hom-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ)
    preserves-mul-inv-is-iso-Abᵉ fᵉ Uᵉ μᵉ {xᵉ} {yᵉ} =
      ( invᵉ
        ( apᵉ
          ( map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ)
          ( ( μᵉ) ∙ᵉ
            ( ap-mul-Ringᵉ Sᵉ
              ( is-section-map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ xᵉ)
              ( is-section-map-inv-is-iso-Abᵉ
                ( ab-Ringᵉ Rᵉ)
                ( ab-Ringᵉ Sᵉ)
                ( fᵉ)
                ( Uᵉ)
                ( yᵉ)))))) ∙ᵉ
      ( is-retraction-map-inv-is-iso-Abᵉ
        ( ab-Ringᵉ Rᵉ)
        ( ab-Ringᵉ Sᵉ)
        ( fᵉ)
        ( Uᵉ)
        ( mul-Ringᵉ Rᵉ
          ( map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ xᵉ)
          ( map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ yᵉ)))

  preserves-unit-inv-is-iso-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
    (Uᵉ : is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ) →
    preserves-unit-hom-Abᵉ Rᵉ Sᵉ fᵉ →
    preserves-unit-hom-Abᵉ Sᵉ Rᵉ
      ( hom-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ)
  preserves-unit-inv-is-iso-Abᵉ fᵉ Uᵉ νᵉ =
    ( invᵉ (apᵉ (map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ) νᵉ)) ∙ᵉ
    ( is-retraction-map-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ _)

  is-ring-homomorphism-inv-is-iso-Abᵉ :
    (fᵉ : hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)) →
    (Uᵉ : is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ) →
    is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ fᵉ →
    is-ring-homomorphism-hom-Abᵉ Sᵉ Rᵉ
      ( hom-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) fᵉ Uᵉ)
  pr1ᵉ (is-ring-homomorphism-inv-is-iso-Abᵉ fᵉ Uᵉ (μᵉ ,ᵉ νᵉ)) =
    preserves-mul-inv-is-iso-Abᵉ fᵉ Uᵉ μᵉ
  pr2ᵉ (is-ring-homomorphism-inv-is-iso-Abᵉ fᵉ Uᵉ (μᵉ ,ᵉ νᵉ)) =
    preserves-unit-inv-is-iso-Abᵉ fᵉ Uᵉ νᵉ

  inv-hom-ring-is-iso-Abᵉ :
    (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
    is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ) →
    hom-Ringᵉ Sᵉ Rᵉ
  pr1ᵉ (inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ) =
    hom-inv-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ) Uᵉ
  pr2ᵉ (inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ) =
    is-ring-homomorphism-inv-is-iso-Abᵉ
      ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
      ( Uᵉ)
      ( is-ring-homomorphism-hom-Ringᵉ Rᵉ Sᵉ fᵉ)

  abstract
    is-iso-ring-is-iso-Abᵉ :
      (fᵉ : hom-Ringᵉ Rᵉ Sᵉ) →
      is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ) →
      is-iso-Ringᵉ Rᵉ Sᵉ fᵉ
    pr1ᵉ (is-iso-ring-is-iso-Abᵉ fᵉ Uᵉ) =
      inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ
    pr1ᵉ (pr2ᵉ (is-iso-ring-is-iso-Abᵉ fᵉ Uᵉ)) =
      eq-htpy-hom-Ringᵉ Sᵉ Sᵉ
        ( comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ fᵉ
          ( inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ))
        ( id-hom-Ringᵉ Sᵉ)
        ( htpy-eq-hom-Abᵉ (ab-Ringᵉ Sᵉ) (ab-Ringᵉ Sᵉ)
          ( hom-ab-hom-Ringᵉ Sᵉ Sᵉ
            ( comp-hom-Ringᵉ Sᵉ Rᵉ Sᵉ fᵉ
              ( inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ)))
          ( id-hom-Abᵉ (ab-Ringᵉ Sᵉ))
          ( is-section-hom-inv-is-iso-Abᵉ
            ( ab-Ringᵉ Rᵉ)
            ( ab-Ringᵉ Sᵉ)
            ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
            ( Uᵉ)))
    pr2ᵉ (pr2ᵉ (is-iso-ring-is-iso-Abᵉ fᵉ Uᵉ)) =
      eq-htpy-hom-Ringᵉ Rᵉ Rᵉ
        ( comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ
          ( inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ)
          ( fᵉ))
        ( id-hom-Ringᵉ Rᵉ)
        ( htpy-eq-hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Rᵉ)
          ( hom-ab-hom-Ringᵉ Rᵉ Rᵉ
            ( comp-hom-Ringᵉ Rᵉ Sᵉ Rᵉ
              ( inv-hom-ring-is-iso-Abᵉ fᵉ Uᵉ)
              ( fᵉ)))
          ( id-hom-Abᵉ (ab-Ringᵉ Rᵉ))
          ( is-retraction-hom-inv-is-iso-Abᵉ
            ( ab-Ringᵉ Rᵉ)
            ( ab-Ringᵉ Sᵉ)
            ( hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ)
            ( Uᵉ)))

  iso-ab-iso-Ringᵉ :
    iso-Ringᵉ Rᵉ Sᵉ → iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ)
  pr1ᵉ (iso-ab-iso-Ringᵉ fᵉ) = hom-ab-hom-Ringᵉ Rᵉ Sᵉ (hom-iso-Ringᵉ Rᵉ Sᵉ fᵉ)
  pr2ᵉ (iso-ab-iso-Ringᵉ fᵉ) =
    is-iso-ab-is-iso-Ringᵉ
      ( hom-iso-Ringᵉ Rᵉ Sᵉ fᵉ)
      ( is-iso-iso-Ringᵉ Rᵉ Sᵉ fᵉ)

  equiv-iso-ab-iso-Ringᵉ : iso-Ringᵉ Rᵉ Sᵉ ≃ᵉ iso-ab-Ringᵉ
  equiv-iso-ab-iso-Ringᵉ =
    ( inv-equivᵉ
      ( associative-Σᵉ
        ( hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ))
        ( is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ))
        ( λ fᵉ → is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ (pr1ᵉ fᵉ)))) ∘eᵉ
    ( equiv-totᵉ (λ fᵉ → commutative-productᵉ)) ∘eᵉ
    ( associative-Σᵉ
      ( hom-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ))
      ( is-ring-homomorphism-hom-Abᵉ Rᵉ Sᵉ)
      ( λ fᵉ → is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (pr1ᵉ fᵉ))) ∘eᵉ
    ( equiv-type-subtypeᵉ
      ( is-prop-is-iso-Ringᵉ Rᵉ Sᵉ)
      ( λ fᵉ → is-prop-is-iso-Abᵉ (ab-Ringᵉ Rᵉ) (ab-Ringᵉ Sᵉ) (hom-ab-hom-Ringᵉ Rᵉ Sᵉ fᵉ))
      ( is-iso-ab-is-iso-Ringᵉ)
      ( is-iso-ring-is-iso-Abᵉ))
```

### Characterizing identifications of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  abstract
    is-torsorial-iso-Ringᵉ : is-torsorialᵉ (λ (Sᵉ : Ringᵉ lᵉ) → iso-Ringᵉ Rᵉ Sᵉ)
    is-torsorial-iso-Ringᵉ =
      is-contr-equivᵉ
        ( Σᵉ (Ringᵉ lᵉ) (iso-ab-Ringᵉ Rᵉ))
        ( equiv-totᵉ (equiv-iso-ab-iso-Ringᵉ Rᵉ))
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-iso-Abᵉ (ab-Ringᵉ Rᵉ))
          ( ab-Ringᵉ Rᵉ ,ᵉ id-iso-Abᵉ (ab-Ringᵉ Rᵉ))
          ( is-torsorial-Eq-structureᵉ
            ( is-torsorial-Eq-subtypeᵉ
              ( is-torsorial-multivariable-implicit-htpyᵉ 2 (mul-Ringᵉ Rᵉ))
              ( λ μᵉ →
                is-prop-iterated-Πᵉ 3
                  ( λ xᵉ yᵉ zᵉ → is-set-type-Ringᵉ Rᵉ (μᵉ (μᵉ xᵉ yᵉ) zᵉ) (μᵉ xᵉ (μᵉ yᵉ zᵉ))))
              ( mul-Ringᵉ Rᵉ)
              ( λ {xᵉ} {yᵉ} → reflᵉ)
              ( associative-mul-Ringᵉ Rᵉ))
            ( (mul-Ringᵉ Rᵉ ,ᵉ associative-mul-Ringᵉ Rᵉ) ,ᵉ λ {xᵉ} {yᵉ} → reflᵉ)
            ( is-torsorial-Eq-subtypeᵉ
              ( is-torsorial-Eq-subtypeᵉ
                ( is-torsorial-Idᵉ (one-Ringᵉ Rᵉ))
                ( λ xᵉ →
                  is-prop-productᵉ
                    ( is-prop-Πᵉ (λ yᵉ → is-set-type-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) yᵉ))
                    ( is-prop-Πᵉ (λ yᵉ → is-set-type-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ yᵉ xᵉ) yᵉ)))
                ( one-Ringᵉ Rᵉ)
                ( reflᵉ)
                ( left-unit-law-mul-Ringᵉ Rᵉ ,ᵉ right-unit-law-mul-Ringᵉ Rᵉ))
              ( λ uᵉ →
                is-prop-productᵉ
                  ( is-prop-iterated-Πᵉ 3
                    ( λ xᵉ yᵉ zᵉ →
                      is-set-type-Ringᵉ Rᵉ
                        ( mul-Ringᵉ Rᵉ xᵉ (add-Ringᵉ Rᵉ yᵉ zᵉ))
                        ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) (mul-Ringᵉ Rᵉ xᵉ zᵉ))))
                  ( is-prop-iterated-Πᵉ 3
                    ( λ xᵉ yᵉ zᵉ →
                      is-set-type-Ringᵉ Rᵉ
                        ( mul-Ringᵉ Rᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) zᵉ)
                        ( add-Ringᵉ Rᵉ (mul-Ringᵉ Rᵉ xᵉ zᵉ) (mul-Ringᵉ Rᵉ yᵉ zᵉ)))))
              ( is-unital-Ringᵉ Rᵉ)
              ( reflᵉ)
              ( left-distributive-mul-add-Ringᵉ Rᵉ ,ᵉ
                right-distributive-mul-add-Ringᵉ Rᵉ))))

  is-equiv-iso-eq-Ringᵉ :
    (Sᵉ : Ringᵉ lᵉ) → is-equivᵉ (iso-eq-Ringᵉ Rᵉ Sᵉ)
  is-equiv-iso-eq-Ringᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-Ringᵉ)
      ( iso-eq-Ringᵉ Rᵉ)

  extensionality-Ringᵉ : (Sᵉ : Ringᵉ lᵉ) → (Rᵉ ＝ᵉ Sᵉ) ≃ᵉ iso-Ringᵉ Rᵉ Sᵉ
  pr1ᵉ (extensionality-Ringᵉ Sᵉ) = iso-eq-Ringᵉ Rᵉ Sᵉ
  pr2ᵉ (extensionality-Ringᵉ Sᵉ) = is-equiv-iso-eq-Ringᵉ Sᵉ

  eq-iso-Ringᵉ : (Sᵉ : Ringᵉ lᵉ) → iso-Ringᵉ Rᵉ Sᵉ → Rᵉ ＝ᵉ Sᵉ
  eq-iso-Ringᵉ Sᵉ = map-inv-is-equivᵉ (is-equiv-iso-eq-Ringᵉ Sᵉ)
```

### Any ring isomorphism preserves and reflects invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : Ringᵉ l2ᵉ)
  (fᵉ : iso-Ringᵉ Rᵉ Sᵉ)
  where

  preserves-invertible-elements-iso-Ringᵉ :
    {xᵉ : type-Ringᵉ Rᵉ} →
    is-invertible-element-Ringᵉ Rᵉ xᵉ →
    is-invertible-element-Ringᵉ Sᵉ (map-iso-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ)
  preserves-invertible-elements-iso-Ringᵉ =
    preserves-invertible-elements-iso-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( iso-multiplicative-monoid-iso-Ringᵉ Rᵉ Sᵉ fᵉ)

  reflects-invertible-elements-iso-Ringᵉ :
    {xᵉ : type-Ringᵉ Rᵉ} →
    is-invertible-element-Ringᵉ Sᵉ (map-iso-Ringᵉ Rᵉ Sᵉ fᵉ xᵉ) →
    is-invertible-element-Ringᵉ Rᵉ xᵉ
  reflects-invertible-elements-iso-Ringᵉ =
    reflects-invertible-elements-iso-Monoidᵉ
      ( multiplicative-monoid-Ringᵉ Rᵉ)
      ( multiplicative-monoid-Ringᵉ Sᵉ)
      ( iso-multiplicative-monoid-iso-Ringᵉ Rᵉ Sᵉ fᵉ)
```