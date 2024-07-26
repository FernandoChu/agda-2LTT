# Homomorphisms of groups

```agda
module group-theory.homomorphisms-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
```

</details>

## Idea

Aᵉ **groupᵉ homomorphism**ᵉ fromᵉ oneᵉ [group](group-theory.groups.mdᵉ) to anotherᵉ isᵉ
aᵉ [semigroupᵉ homomorphism](group-theory.homomorphisms-semigroups.mdᵉ) betweenᵉ
theirᵉ underlyingᵉ [semigroups](group-theory.semigroups.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  preserves-mul-Groupᵉ : (type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-Groupᵉ fᵉ =
    preserves-mul-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  preserves-mul-Group'ᵉ : (type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-Group'ᵉ fᵉ =
    preserves-mul-Semigroup'ᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ) fᵉ

  is-prop-preserves-mul-Groupᵉ :
    (fᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → is-propᵉ (preserves-mul-Groupᵉ fᵉ)
  is-prop-preserves-mul-Groupᵉ =
    is-prop-preserves-mul-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  preserves-mul-prop-Groupᵉ : (type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-mul-prop-Groupᵉ =
    preserves-mul-prop-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Groupᵉ =
    hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)

  map-hom-Groupᵉ : hom-Groupᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ
  map-hom-Groupᵉ = pr1ᵉ

  preserves-mul-hom-Groupᵉ :
    (fᵉ : hom-Groupᵉ) →
    preserves-mul-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( map-hom-Groupᵉ fᵉ)
  preserves-mul-hom-Groupᵉ = pr2ᵉ
```

### The identity group homomorphism

```agda
id-hom-Groupᵉ : {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) → hom-Groupᵉ Gᵉ Gᵉ
id-hom-Groupᵉ Gᵉ = id-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)
```

### Composition of group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  (gᵉ : hom-Groupᵉ Hᵉ Kᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  comp-hom-Groupᵉ : hom-Groupᵉ Gᵉ Kᵉ
  comp-hom-Groupᵉ =
    comp-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( semigroup-Groupᵉ Kᵉ)
      ( gᵉ)
      ( fᵉ)

  map-comp-hom-Groupᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Kᵉ
  map-comp-hom-Groupᵉ =
    map-comp-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( semigroup-Groupᵉ Kᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-mul-comp-hom-Groupᵉ :
    preserves-mul-Groupᵉ Gᵉ Kᵉ map-comp-hom-Groupᵉ
  preserves-mul-comp-hom-Groupᵉ =
    preserves-mul-comp-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( semigroup-Groupᵉ Kᵉ)
      ( gᵉ)
      ( fᵉ)
```

## Properties

### Characterization of the identity type of group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  htpy-hom-Groupᵉ : (fᵉ gᵉ : hom-Groupᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Groupᵉ = htpy-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  refl-htpy-hom-Groupᵉ : (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → htpy-hom-Groupᵉ fᵉ fᵉ
  refl-htpy-hom-Groupᵉ =
    refl-htpy-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)

  htpy-eq-hom-Groupᵉ : (fᵉ gᵉ : hom-Groupᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Groupᵉ fᵉ gᵉ
  htpy-eq-hom-Groupᵉ =
    htpy-eq-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)

  abstract
    is-torsorial-htpy-hom-Groupᵉ :
      ( fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → is-torsorialᵉ (htpy-hom-Groupᵉ fᵉ)
    is-torsorial-htpy-hom-Groupᵉ =
      is-torsorial-htpy-hom-Semigroupᵉ
        ( semigroup-Groupᵉ Gᵉ)
        ( semigroup-Groupᵉ Hᵉ)

  abstract
    is-equiv-htpy-eq-hom-Groupᵉ :
      (fᵉ gᵉ : hom-Groupᵉ Gᵉ Hᵉ) → is-equivᵉ (htpy-eq-hom-Groupᵉ fᵉ gᵉ)
    is-equiv-htpy-eq-hom-Groupᵉ =
      is-equiv-htpy-eq-hom-Semigroupᵉ
        ( semigroup-Groupᵉ Gᵉ)
        ( semigroup-Groupᵉ Hᵉ)

  extensionality-hom-Groupᵉ :
    (fᵉ gᵉ : hom-Groupᵉ Gᵉ Hᵉ) → Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-Groupᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Groupᵉ fᵉ gᵉ) = htpy-eq-hom-Groupᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-Groupᵉ fᵉ gᵉ) = is-equiv-htpy-eq-hom-Groupᵉ fᵉ gᵉ

  eq-htpy-hom-Groupᵉ : {fᵉ gᵉ : hom-Groupᵉ Gᵉ Hᵉ} → htpy-hom-Groupᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Groupᵉ =
    eq-htpy-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  is-set-hom-Groupᵉ : is-setᵉ (hom-Groupᵉ Gᵉ Hᵉ)
  is-set-hom-Groupᵉ =
    is-set-hom-Semigroupᵉ (semigroup-Groupᵉ Gᵉ) (semigroup-Groupᵉ Hᵉ)

  hom-set-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ hom-set-Groupᵉ = hom-Groupᵉ Gᵉ Hᵉ
  pr2ᵉ hom-set-Groupᵉ = is-set-hom-Groupᵉ
```

### Associativity of composition of group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ) (Lᵉ : Groupᵉ l4ᵉ)
  where

  associative-comp-hom-Groupᵉ :
    (hᵉ : hom-Groupᵉ Kᵉ Lᵉ) (gᵉ : hom-Groupᵉ Hᵉ Kᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
    comp-hom-Groupᵉ Gᵉ Hᵉ Lᵉ (comp-hom-Groupᵉ Hᵉ Kᵉ Lᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Groupᵉ Gᵉ Kᵉ Lᵉ hᵉ (comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ gᵉ fᵉ)
  associative-comp-hom-Groupᵉ =
    associative-comp-hom-Semigroupᵉ
      ( semigroup-Groupᵉ Gᵉ)
      ( semigroup-Groupᵉ Hᵉ)
      ( semigroup-Groupᵉ Kᵉ)
      ( semigroup-Groupᵉ Lᵉ)
```

### The left and right unit laws for composition of group homomorphisms

```agda
left-unit-law-comp-hom-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
  Idᵉ (comp-hom-Groupᵉ Gᵉ Hᵉ Hᵉ (id-hom-Groupᵉ Hᵉ) fᵉ) fᵉ
left-unit-law-comp-hom-Groupᵉ Gᵉ Hᵉ =
  left-unit-law-comp-hom-Semigroupᵉ
    ( semigroup-Groupᵉ Gᵉ)
    ( semigroup-Groupᵉ Hᵉ)

right-unit-law-comp-hom-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) →
  Idᵉ (comp-hom-Groupᵉ Gᵉ Gᵉ Hᵉ fᵉ (id-hom-Groupᵉ Gᵉ)) fᵉ
right-unit-law-comp-hom-Groupᵉ Gᵉ Hᵉ =
  right-unit-law-comp-hom-Semigroupᵉ
    ( semigroup-Groupᵉ Gᵉ)
    ( semigroup-Groupᵉ Hᵉ)
```

### Group homomorphisms preserve the unit element

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  preserves-unit-Groupᵉ : (type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → UUᵉ l2ᵉ
  preserves-unit-Groupᵉ fᵉ = fᵉ (unit-Groupᵉ Gᵉ) ＝ᵉ unit-Groupᵉ Hᵉ

  abstract
    preserves-unit-hom-Groupᵉ :
      ( fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → preserves-unit-Groupᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
    preserves-unit-hom-Groupᵉ fᵉ =
      ( invᵉ (left-unit-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ)))) ∙ᵉ
      ( apᵉ
        ( λ xᵉ → mul-Groupᵉ Hᵉ xᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ)))
        ( invᵉ
          ( left-inverse-law-mul-Groupᵉ Hᵉ
            ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ))))) ∙ᵉ
      ( associative-mul-Groupᵉ Hᵉ
        ( inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ)))
        ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ))
        ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ))) ∙ᵉ
      ( apᵉ
        ( mul-Groupᵉ Hᵉ (inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ))))
        ( invᵉ (preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))) ∙ᵉ
      ( apᵉ
        ( λ xᵉ →
          mul-Groupᵉ Hᵉ
            ( inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ)))
            ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ))
        ( left-unit-law-mul-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ))) ∙ᵉ
      ( left-inverse-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (unit-Groupᵉ Gᵉ)))
```

### Group homomorphisms preserve inverses

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  preserves-inverses-Groupᵉ :
    (type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-inverses-Groupᵉ fᵉ =
    {xᵉ : type-Groupᵉ Gᵉ} → Idᵉ (fᵉ (inv-Groupᵉ Gᵉ xᵉ)) (inv-Groupᵉ Hᵉ (fᵉ xᵉ))

  abstract
    preserves-inv-hom-Groupᵉ :
      (fᵉ : hom-Groupᵉ Gᵉ Hᵉ) → preserves-inverses-Groupᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
    preserves-inv-hom-Groupᵉ fᵉ {xᵉ} =
      ( invᵉ
        ( right-unit-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (inv-Groupᵉ Gᵉ xᵉ)))) ∙ᵉ
      ( apᵉ
        ( mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (inv-Groupᵉ Gᵉ xᵉ)))
        ( invᵉ (right-inverse-law-mul-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))) ∙ᵉ
      ( invᵉ
        ( associative-mul-Groupᵉ Hᵉ
          ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (inv-Groupᵉ Gᵉ xᵉ))
          ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)
          ( inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))) ∙ᵉ
      ( invᵉ
        ( apᵉ
          ( λ yᵉ → mul-Groupᵉ Hᵉ yᵉ (inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))
          ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))) ∙ᵉ
      ( apᵉ
        ( λ yᵉ →
          mul-Groupᵉ Hᵉ
            ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
            ( inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))
        ( left-inverse-law-mul-Groupᵉ Gᵉ xᵉ)) ∙ᵉ
      ( apᵉ
        ( λ yᵉ → mul-Groupᵉ Hᵉ yᵉ (inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))
        ( preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ∙ᵉ
      ( left-unit-law-mul-Groupᵉ Hᵉ (inv-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)))
```

### Group homomorphisms preserve all group structure

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  hom-Group'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Group'ᵉ =
    Σᵉ ( hom-Groupᵉ Gᵉ Hᵉ)
      ( λ fᵉ →
        ( preserves-unit-Groupᵉ Gᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)) ×ᵉ
        ( preserves-inverses-Groupᵉ Gᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)))

  preserves-group-structure-hom-Groupᵉ :
    hom-Groupᵉ Gᵉ Hᵉ → hom-Group'ᵉ
  pr1ᵉ (preserves-group-structure-hom-Groupᵉ fᵉ) = fᵉ
  pr1ᵉ (pr2ᵉ (preserves-group-structure-hom-Groupᵉ fᵉ)) =
    preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  pr2ᵉ (pr2ᵉ (preserves-group-structure-hom-Groupᵉ fᵉ)) =
    preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ
```

### Group homomorphisms induce monoid homomorphisms between the underlying monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  hom-monoid-hom-Groupᵉ : hom-Monoidᵉ (monoid-Groupᵉ Gᵉ) (monoid-Groupᵉ Hᵉ)
  pr1ᵉ hom-monoid-hom-Groupᵉ = fᵉ
  pr2ᵉ hom-monoid-hom-Groupᵉ = preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ
```

### Group homomorphisms preserve left and right division

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-left-div-hom-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (left-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    left-div-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
  preserves-left-div-hom-Groupᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( apᵉ (mul-Group'ᵉ Hᵉ _) (preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  preserves-right-div-hom-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (right-div-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    right-div-Groupᵉ Hᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ) (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ yᵉ)
  preserves-right-div-hom-Groupᵉ =
    ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ) ∙ᵉ
    ( apᵉ (mul-Groupᵉ Hᵉ _) (preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ))
```