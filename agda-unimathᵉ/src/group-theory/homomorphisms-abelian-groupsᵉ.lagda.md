# Homomorphisms of abelian groups

```agda
module group-theory.homomorphisms-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.category-of-abelian-groupsᵉ
open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-semigroupsᵉ
```

</details>

## Idea

Homomorphismsᵉ betweenᵉ abelianᵉ groupsᵉ areᵉ justᵉ homomorphismsᵉ betweenᵉ theirᵉ
underlyingᵉ groups.ᵉ

## Definition

### The predicate that a map between abelian groups preserves addition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  preserves-add-Abᵉ : (type-Abᵉ Aᵉ → type-Abᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-add-Abᵉ = preserves-mul-Semigroupᵉ (semigroup-Abᵉ Aᵉ) (semigroup-Abᵉ Bᵉ)
```

### The predicate that a map between abelian groups preserves zero

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  preserves-zero-Abᵉ : (type-Abᵉ Aᵉ → type-Abᵉ Bᵉ) → UUᵉ l2ᵉ
  preserves-zero-Abᵉ = preserves-unit-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### The predicate that a map between abelian groups preserves negatives

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  preserves-negatives-Abᵉ : (type-Abᵉ Aᵉ → type-Abᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-negatives-Abᵉ =
    preserves-inverses-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### Homomorphisms of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  hom-set-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Abᵉ = hom-set-Large-Categoryᵉ Ab-Large-Categoryᵉ Aᵉ Bᵉ

  hom-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Abᵉ = hom-Large-Categoryᵉ Ab-Large-Categoryᵉ Aᵉ Bᵉ

  map-hom-Abᵉ : hom-Abᵉ → type-Abᵉ Aᵉ → type-Abᵉ Bᵉ
  map-hom-Abᵉ = map-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  preserves-add-hom-Abᵉ : (fᵉ : hom-Abᵉ) → preserves-add-Abᵉ Aᵉ Bᵉ (map-hom-Abᵉ fᵉ)
  preserves-add-hom-Abᵉ fᵉ = preserves-mul-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  preserves-zero-hom-Abᵉ : (fᵉ : hom-Abᵉ) → preserves-zero-Abᵉ Aᵉ Bᵉ (map-hom-Abᵉ fᵉ)
  preserves-zero-hom-Abᵉ fᵉ = preserves-unit-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  preserves-negatives-hom-Abᵉ :
    (fᵉ : hom-Abᵉ) → preserves-negatives-Abᵉ Aᵉ Bᵉ (map-hom-Abᵉ fᵉ)
  preserves-negatives-hom-Abᵉ fᵉ =
    preserves-inv-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  hom-semigroup-hom-Abᵉ :
    hom-Abᵉ → hom-Semigroupᵉ (semigroup-Abᵉ Aᵉ) (semigroup-Abᵉ Bᵉ)
  pr1ᵉ (hom-semigroup-hom-Abᵉ fᵉ) = map-hom-Abᵉ fᵉ
  pr2ᵉ (hom-semigroup-hom-Abᵉ fᵉ) = preserves-add-hom-Abᵉ fᵉ

  hom-commutative-monoid-hom-Abᵉ :
    hom-Abᵉ →
    hom-Commutative-Monoidᵉ
      ( commutative-monoid-Abᵉ Aᵉ)
      ( commutative-monoid-Abᵉ Bᵉ)
  pr1ᵉ (hom-commutative-monoid-hom-Abᵉ fᵉ) = hom-semigroup-hom-Abᵉ fᵉ
  pr2ᵉ (hom-commutative-monoid-hom-Abᵉ fᵉ) = preserves-zero-hom-Abᵉ fᵉ
```

### Characterization of the identity type of the abelian group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  htpy-hom-Abᵉ : (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-Abᵉ fᵉ gᵉ = htpy-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ gᵉ

  refl-htpy-hom-Abᵉ : (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → htpy-hom-Abᵉ fᵉ fᵉ
  refl-htpy-hom-Abᵉ fᵉ = refl-htpy-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  htpy-eq-hom-Abᵉ : (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Abᵉ fᵉ gᵉ
  htpy-eq-hom-Abᵉ fᵉ gᵉ = htpy-eq-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ gᵉ

  abstract
    is-torsorial-htpy-hom-Abᵉ :
      (fᵉ : hom-Abᵉ Aᵉ Bᵉ) → is-torsorialᵉ (htpy-hom-Abᵉ fᵉ)
    is-torsorial-htpy-hom-Abᵉ fᵉ =
      is-torsorial-htpy-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ

  abstract
    is-equiv-htpy-eq-hom-Abᵉ :
      (fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ) → is-equivᵉ (htpy-eq-hom-Abᵉ fᵉ gᵉ)
    is-equiv-htpy-eq-hom-Abᵉ fᵉ gᵉ =
      is-equiv-htpy-eq-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) fᵉ gᵉ

  eq-htpy-hom-Abᵉ : {fᵉ gᵉ : hom-Abᵉ Aᵉ Bᵉ} → htpy-hom-Abᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Abᵉ = eq-htpy-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  is-set-hom-Abᵉ : is-setᵉ (hom-Abᵉ Aᵉ Bᵉ)
  is-set-hom-Abᵉ = is-set-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)
```

### The identity morphism of abelian groups

```agda
preserves-add-idᵉ : {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) → preserves-add-Abᵉ Aᵉ Aᵉ idᵉ
preserves-add-idᵉ Aᵉ = preserves-mul-id-Semigroupᵉ (semigroup-Abᵉ Aᵉ)

id-hom-Abᵉ : {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → hom-Abᵉ Aᵉ Aᵉ
id-hom-Abᵉ Aᵉ = id-hom-Groupᵉ (group-Abᵉ Aᵉ)
```

### Composition of morphisms of abelian groups

```agda
comp-hom-Abᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (Cᵉ : Abᵉ l3ᵉ) →
  ( hom-Abᵉ Bᵉ Cᵉ) → (hom-Abᵉ Aᵉ Bᵉ) → (hom-Abᵉ Aᵉ Cᵉ)
comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ =
  comp-hom-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ) (group-Abᵉ Cᵉ)
```

### Associativity of composition of morphisms of abelian groups

```agda
associative-comp-hom-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ) (Cᵉ : Abᵉ l3ᵉ) (Dᵉ : Abᵉ l4ᵉ)
  (hᵉ : hom-Abᵉ Cᵉ Dᵉ) (gᵉ : hom-Abᵉ Bᵉ Cᵉ) (fᵉ : hom-Abᵉ Aᵉ Bᵉ) →
  comp-hom-Abᵉ Aᵉ Bᵉ Dᵉ (comp-hom-Abᵉ Bᵉ Cᵉ Dᵉ hᵉ gᵉ) fᵉ ＝ᵉ
  comp-hom-Abᵉ Aᵉ Cᵉ Dᵉ hᵉ (comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
associative-comp-hom-Abᵉ Aᵉ Bᵉ Cᵉ Dᵉ =
  associative-comp-hom-Semigroupᵉ
    ( semigroup-Abᵉ Aᵉ)
    ( semigroup-Abᵉ Bᵉ)
    ( semigroup-Abᵉ Cᵉ)
    ( semigroup-Abᵉ Dᵉ)
```

### The unit laws for composition of abelian groups

```agda
left-unit-law-comp-hom-Abᵉ :
  { l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  ( fᵉ : hom-Abᵉ Aᵉ Bᵉ) → Idᵉ (comp-hom-Abᵉ Aᵉ Bᵉ Bᵉ (id-hom-Abᵉ Bᵉ) fᵉ) fᵉ
left-unit-law-comp-hom-Abᵉ Aᵉ Bᵉ =
  left-unit-law-comp-hom-Semigroupᵉ (semigroup-Abᵉ Aᵉ) (semigroup-Abᵉ Bᵉ)

right-unit-law-comp-hom-Abᵉ :
  { l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  ( fᵉ : hom-Abᵉ Aᵉ Bᵉ) → Idᵉ (comp-hom-Abᵉ Aᵉ Aᵉ Bᵉ fᵉ (id-hom-Abᵉ Aᵉ)) fᵉ
right-unit-law-comp-hom-Abᵉ Aᵉ Bᵉ =
  right-unit-law-comp-hom-Semigroupᵉ (semigroup-Abᵉ Aᵉ) (semigroup-Abᵉ Bᵉ)
```