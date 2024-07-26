# Homomorphisms of higher groups

```agda
module higher-group-theory.homomorphisms-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
```

</details>

## Idea

Aᵉ homomorphismᵉ ofᵉ ∞-groupsᵉ isᵉ aᵉ pointedᵉ mapᵉ betweenᵉ theirᵉ classifyingᵉ types.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ)
  where

  hom-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-∞-Groupᵉ =
    classifying-pointed-type-∞-Groupᵉ Gᵉ →∗ᵉ classifying-pointed-type-∞-Groupᵉ Hᵉ

  classifying-map-hom-∞-Groupᵉ :
    hom-∞-Groupᵉ → classifying-type-∞-Groupᵉ Gᵉ → classifying-type-∞-Groupᵉ Hᵉ
  classifying-map-hom-∞-Groupᵉ = map-pointed-mapᵉ

  preserves-point-classifying-map-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ) →
    classifying-map-hom-∞-Groupᵉ fᵉ (shape-∞-Groupᵉ Gᵉ) ＝ᵉ shape-∞-Groupᵉ Hᵉ
  preserves-point-classifying-map-hom-∞-Groupᵉ =
    preserves-point-pointed-mapᵉ

  map-hom-∞-Groupᵉ : hom-∞-Groupᵉ → type-∞-Groupᵉ Gᵉ → type-∞-Groupᵉ Hᵉ
  map-hom-∞-Groupᵉ = map-Ωᵉ

  preserves-unit-map-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ) → map-hom-∞-Groupᵉ fᵉ (unit-∞-Groupᵉ Gᵉ) ＝ᵉ unit-∞-Groupᵉ Hᵉ
  preserves-unit-map-hom-∞-Groupᵉ = preserves-refl-map-Ωᵉ

  preserves-mul-map-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ) {xᵉ yᵉ : type-∞-Groupᵉ Gᵉ} →
    map-hom-∞-Groupᵉ fᵉ (mul-∞-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-∞-Groupᵉ Hᵉ (map-hom-∞-Groupᵉ fᵉ xᵉ) (map-hom-∞-Groupᵉ fᵉ yᵉ)
  preserves-mul-map-hom-∞-Groupᵉ = preserves-mul-map-Ωᵉ

  preserves-inv-map-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ) (xᵉ : type-∞-Groupᵉ Gᵉ) →
    map-hom-∞-Groupᵉ fᵉ (inv-∞-Groupᵉ Gᵉ xᵉ) ＝ᵉ inv-∞-Groupᵉ Hᵉ (map-hom-∞-Groupᵉ fᵉ xᵉ)
  preserves-inv-map-hom-∞-Groupᵉ = preserves-inv-map-Ωᵉ
```

## Properties

### Homotopies of morphisms of ∞-groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ) (fᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ)
  where

  htpy-hom-∞-Groupᵉ : (gᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-∞-Groupᵉ = pointed-htpyᵉ fᵉ

  extensionality-hom-∞-Groupᵉ :
    (gᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-∞-Groupᵉ gᵉ
  extensionality-hom-∞-Groupᵉ = extensionality-pointed-mapᵉ fᵉ

  eq-htpy-hom-∞-Groupᵉ :
    (gᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) → (htpy-hom-∞-Groupᵉ gᵉ) → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-∞-Groupᵉ gᵉ = map-inv-equivᵉ (extensionality-hom-∞-Groupᵉ gᵉ)
```

### Wild category structure on higher groups

```agda
module _
  {lᵉ : Level} (Gᵉ : ∞-Groupᵉ lᵉ)
  where

  id-hom-∞-Groupᵉ : hom-∞-Groupᵉ Gᵉ Gᵉ
  id-hom-∞-Groupᵉ = id-pointed-mapᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ) (Kᵉ : ∞-Groupᵉ l3ᵉ)
  where

  comp-hom-∞-Groupᵉ :
    hom-∞-Groupᵉ Hᵉ Kᵉ → hom-∞-Groupᵉ Gᵉ Hᵉ → hom-∞-Groupᵉ Gᵉ Kᵉ
  comp-hom-∞-Groupᵉ = comp-pointed-mapᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ) (Kᵉ : ∞-Groupᵉ l3ᵉ) (Lᵉ : ∞-Groupᵉ l4ᵉ)
  where

  associative-comp-hom-∞-Groupᵉ :
    (hᵉ : hom-∞-Groupᵉ Kᵉ Lᵉ) (gᵉ : hom-∞-Groupᵉ Hᵉ Kᵉ) (fᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) →
    htpy-hom-∞-Groupᵉ Gᵉ Lᵉ
      ( comp-hom-∞-Groupᵉ Gᵉ Hᵉ Lᵉ (comp-hom-∞-Groupᵉ Hᵉ Kᵉ Lᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-∞-Groupᵉ Gᵉ Kᵉ Lᵉ hᵉ (comp-hom-∞-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ))
  associative-comp-hom-∞-Groupᵉ = associative-comp-pointed-mapᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ)
  where

  left-unit-law-comp-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) →
    htpy-hom-∞-Groupᵉ Gᵉ Hᵉ (comp-hom-∞-Groupᵉ Gᵉ Hᵉ Hᵉ (id-hom-∞-Groupᵉ Hᵉ) fᵉ) fᵉ
  left-unit-law-comp-hom-∞-Groupᵉ = left-unit-law-comp-pointed-mapᵉ

  right-unit-law-comp-hom-∞-Groupᵉ :
    (fᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ) →
    htpy-hom-∞-Groupᵉ Gᵉ Hᵉ (comp-hom-∞-Groupᵉ Gᵉ Gᵉ Hᵉ fᵉ (id-hom-∞-Groupᵉ Gᵉ)) fᵉ
  right-unit-law-comp-hom-∞-Groupᵉ = right-unit-law-comp-pointed-mapᵉ
```