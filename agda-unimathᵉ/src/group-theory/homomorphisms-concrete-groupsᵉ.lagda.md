# Homomorphisms of concrete groups

```agda
module group-theory.homomorphisms-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-groupsᵉ

open import higher-group-theory.homomorphisms-higher-groupsᵉ
```

</details>

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  where

  hom-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Concrete-Groupᵉ =
    hom-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) (∞-group-Concrete-Groupᵉ Hᵉ)

  is-set-hom-Concrete-Groupᵉ : is-setᵉ hom-Concrete-Groupᵉ
  is-set-hom-Concrete-Groupᵉ =
    is-trunc-map-ev-point-is-connectedᵉ
      ( zero-𝕋ᵉ)
      ( shape-Concrete-Groupᵉ Gᵉ)
      ( is-0-connected-classifying-type-Concrete-Groupᵉ Gᵉ)
      ( is-1-type-classifying-type-Concrete-Groupᵉ Hᵉ)
      ( shape-Concrete-Groupᵉ Hᵉ)

  hom-set-Concrete-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ hom-set-Concrete-Groupᵉ = hom-Concrete-Groupᵉ
  pr2ᵉ hom-set-Concrete-Groupᵉ = is-set-hom-Concrete-Groupᵉ

  classifying-map-hom-Concrete-Groupᵉ :
    hom-Concrete-Groupᵉ →
    classifying-type-Concrete-Groupᵉ Gᵉ → classifying-type-Concrete-Groupᵉ Hᵉ
  classifying-map-hom-Concrete-Groupᵉ =
    classifying-map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  preserves-point-classifying-map-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ) →
    Idᵉ
      ( classifying-map-hom-Concrete-Groupᵉ fᵉ (shape-Concrete-Groupᵉ Gᵉ))
      ( shape-Concrete-Groupᵉ Hᵉ)
  preserves-point-classifying-map-hom-Concrete-Groupᵉ =
    preserves-point-classifying-map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  map-hom-Concrete-Groupᵉ :
    hom-Concrete-Groupᵉ → type-Concrete-Groupᵉ Gᵉ → type-Concrete-Groupᵉ Hᵉ
  map-hom-Concrete-Groupᵉ =
    map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  preserves-unit-map-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ) →
    Idᵉ
      ( map-hom-Concrete-Groupᵉ fᵉ (unit-Concrete-Groupᵉ Gᵉ))
      ( unit-Concrete-Groupᵉ Hᵉ)
  preserves-unit-map-hom-Concrete-Groupᵉ =
    preserves-unit-map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  preserves-mul-map-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ) {xᵉ yᵉ : type-Concrete-Groupᵉ Gᵉ} →
    Idᵉ
      ( map-hom-Concrete-Groupᵉ fᵉ (mul-Concrete-Groupᵉ Gᵉ xᵉ yᵉ))
      ( mul-Concrete-Groupᵉ Hᵉ
        ( map-hom-Concrete-Groupᵉ fᵉ xᵉ)
        ( map-hom-Concrete-Groupᵉ fᵉ yᵉ))
  preserves-mul-map-hom-Concrete-Groupᵉ =
    preserves-mul-map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  preserves-inv-map-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ) (xᵉ : type-Concrete-Groupᵉ Gᵉ) →
    Idᵉ
      ( map-hom-Concrete-Groupᵉ fᵉ (inv-Concrete-Groupᵉ Gᵉ xᵉ))
      ( inv-Concrete-Groupᵉ Hᵉ (map-hom-Concrete-Groupᵉ fᵉ xᵉ))
  preserves-inv-map-hom-Concrete-Groupᵉ =
    preserves-inv-map-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  hom-group-hom-Concrete-Groupᵉ :
    hom-Concrete-Groupᵉ →
    hom-Groupᵉ
      ( group-Concrete-Groupᵉ Gᵉ)
      ( group-Concrete-Groupᵉ Hᵉ)
  hom-group-hom-Concrete-Groupᵉ fᵉ =
    pairᵉ (map-hom-Concrete-Groupᵉ fᵉ) (preserves-mul-map-hom-Concrete-Groupᵉ fᵉ)
```

### Homotopies of morphisms of concrete groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

  htpy-hom-Concrete-Groupᵉ :
    (gᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Concrete-Groupᵉ =
    htpy-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)
      ( fᵉ)

  extensionality-hom-Concrete-Groupᵉ :
    (gᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-Concrete-Groupᵉ gᵉ
  extensionality-hom-Concrete-Groupᵉ =
    extensionality-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)
      ( fᵉ)

  eq-htpy-hom-Concrete-Groupᵉ :
    (gᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) → (htpy-hom-Concrete-Groupᵉ gᵉ) → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Concrete-Groupᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-Concrete-Groupᵉ gᵉ)
```

```agda
id-hom-Concrete-Groupᵉ :
  {lᵉ : Level} (Gᵉ : Concrete-Groupᵉ lᵉ) → hom-Concrete-Groupᵉ Gᵉ Gᵉ
id-hom-Concrete-Groupᵉ Gᵉ = id-hom-∞-Groupᵉ ( ∞-group-Concrete-Groupᵉ Gᵉ)

comp-hom-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ) (Kᵉ : Concrete-Groupᵉ l3ᵉ) →
  hom-Concrete-Groupᵉ Hᵉ Kᵉ → hom-Concrete-Groupᵉ Gᵉ Hᵉ → hom-Concrete-Groupᵉ Gᵉ Kᵉ
comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Kᵉ =
  comp-hom-∞-Groupᵉ
    ( ∞-group-Concrete-Groupᵉ Gᵉ)
    ( ∞-group-Concrete-Groupᵉ Hᵉ)
    ( ∞-group-Concrete-Groupᵉ Kᵉ)

associative-comp-hom-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (Kᵉ : Concrete-Groupᵉ l3ᵉ) (Lᵉ : Concrete-Groupᵉ l4ᵉ)
  (hᵉ : hom-Concrete-Groupᵉ Kᵉ Lᵉ) (gᵉ : hom-Concrete-Groupᵉ Hᵉ Kᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) →
  htpy-hom-Concrete-Groupᵉ Gᵉ Lᵉ
    ( comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Lᵉ (comp-hom-Concrete-Groupᵉ Hᵉ Kᵉ Lᵉ hᵉ gᵉ) fᵉ)
    ( comp-hom-Concrete-Groupᵉ Gᵉ Kᵉ Lᵉ hᵉ (comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ))
associative-comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Kᵉ Lᵉ =
  associative-comp-hom-∞-Groupᵉ
    ( ∞-group-Concrete-Groupᵉ Gᵉ)
    ( ∞-group-Concrete-Groupᵉ Hᵉ)
    ( ∞-group-Concrete-Groupᵉ Kᵉ)
    ( ∞-group-Concrete-Groupᵉ Lᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  where

  left-unit-law-comp-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) →
    htpy-hom-Concrete-Groupᵉ Gᵉ Hᵉ
      ( comp-hom-Concrete-Groupᵉ Gᵉ Hᵉ Hᵉ (id-hom-Concrete-Groupᵉ Hᵉ) fᵉ)
      ( fᵉ)
  left-unit-law-comp-hom-Concrete-Groupᵉ =
    left-unit-law-comp-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)

  right-unit-law-comp-hom-Concrete-Groupᵉ :
    (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ) →
    htpy-hom-Concrete-Groupᵉ Gᵉ Hᵉ
      ( comp-hom-Concrete-Groupᵉ Gᵉ Gᵉ Hᵉ fᵉ (id-hom-Concrete-Groupᵉ Gᵉ))
      ( fᵉ)
  right-unit-law-comp-hom-Concrete-Groupᵉ =
    right-unit-law-comp-hom-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( ∞-group-Concrete-Groupᵉ Hᵉ)
```