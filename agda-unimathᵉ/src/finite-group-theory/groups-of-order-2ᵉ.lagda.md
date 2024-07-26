# Groups of order `2`

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.groups-of-order-2ᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.standard-cyclic-groupsᵉ

open import finite-group-theory.finite-groupsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.symmetric-groupsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ groupsᵉ ofᵉ orderᵉ 2 isᵉ contractibleᵉ

## Definitions

### The type of groups of order 2

```agda
Group-of-Order-2ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Group-of-Order-2ᵉ lᵉ = Group-of-Orderᵉ lᵉ 2

module _
  {lᵉ : Level} (Gᵉ : Group-of-Order-2ᵉ lᵉ)
  where

  group-Group-of-Order-2ᵉ : Groupᵉ lᵉ
  group-Group-of-Order-2ᵉ = pr1ᵉ Gᵉ

  type-Group-of-Order-2ᵉ : UUᵉ lᵉ
  type-Group-of-Order-2ᵉ = type-Groupᵉ group-Group-of-Order-2ᵉ

  is-set-type-Group-of-Order-2ᵉ : is-setᵉ type-Group-of-Order-2ᵉ
  is-set-type-Group-of-Order-2ᵉ = is-set-type-Groupᵉ group-Group-of-Order-2ᵉ

  mul-Group-of-Order-2ᵉ : (xᵉ yᵉ : type-Group-of-Order-2ᵉ) → type-Group-of-Order-2ᵉ
  mul-Group-of-Order-2ᵉ = mul-Groupᵉ group-Group-of-Order-2ᵉ

  unit-Group-of-Order-2ᵉ : type-Group-of-Order-2ᵉ
  unit-Group-of-Order-2ᵉ = unit-Groupᵉ group-Group-of-Order-2ᵉ

  has-two-elements-Group-of-Order-2ᵉ : has-two-elementsᵉ (type-Group-of-Order-2ᵉ)
  has-two-elements-Group-of-Order-2ᵉ = pr2ᵉ Gᵉ

  2-element-type-Group-of-Order-2ᵉ : 2-Element-Typeᵉ lᵉ
  pr1ᵉ 2-element-type-Group-of-Order-2ᵉ = type-Group-of-Order-2ᵉ
  pr2ᵉ 2-element-type-Group-of-Order-2ᵉ = has-two-elements-Group-of-Order-2ᵉ
```

### The group ℤ/2 of order 2

```agda
ℤ-Mod-2-Group-of-Order-2ᵉ : Group-of-Order-2ᵉ lzero
pr1ᵉ ℤ-Mod-2-Group-of-Order-2ᵉ = ℤ-Mod-Groupᵉ 2
pr2ᵉ ℤ-Mod-2-Group-of-Order-2ᵉ = refl-mere-equivᵉ (Finᵉ 2ᵉ)
```

### The permutation group S₂ of order 2

```agda
symmetric-Group-of-Order-2ᵉ : (lᵉ : Level) → Group-of-Order-2ᵉ lᵉ
pr1ᵉ (symmetric-Group-of-Order-2ᵉ lᵉ) =
  symmetric-Groupᵉ (raise-Fin-Setᵉ lᵉ 2ᵉ)
pr2ᵉ (symmetric-Group-of-Order-2ᵉ lᵉ) =
  has-two-elements-Aut-2-Element-Typeᵉ
    ( pairᵉ (raise-Finᵉ lᵉ 2ᵉ) (unit-trunc-Propᵉ (compute-raise-Finᵉ lᵉ 2ᵉ)))
```

## Properties

### Characterization of the identity type of the type of groups of order 2

```agda
iso-Group-of-Order-2ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-of-Order-2ᵉ l1ᵉ) (Hᵉ : Group-of-Order-2ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
iso-Group-of-Order-2ᵉ Gᵉ Hᵉ =
  iso-Groupᵉ (group-Group-of-Order-2ᵉ Gᵉ) (group-Group-of-Order-2ᵉ Hᵉ)

module _
  {lᵉ : Level} (Gᵉ : Group-of-Order-2ᵉ lᵉ)
  where

  iso-eq-Group-of-Order-2ᵉ :
    (Hᵉ : Group-of-Order-2ᵉ lᵉ) → Idᵉ Gᵉ Hᵉ → iso-Group-of-Order-2ᵉ Gᵉ Hᵉ
  iso-eq-Group-of-Order-2ᵉ Hᵉ pᵉ =
    iso-eq-Groupᵉ
      ( group-Group-of-Order-2ᵉ Gᵉ)
      ( group-Group-of-Order-2ᵉ Hᵉ)
      ( apᵉ pr1ᵉ pᵉ)

  is-torsorial-iso-Group-of-Order-2ᵉ :
    is-torsorialᵉ (iso-Group-of-Order-2ᵉ Gᵉ)
  is-torsorial-iso-Group-of-Order-2ᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-iso-Groupᵉ (group-Group-of-Order-2ᵉ Gᵉ))
      ( λ Hᵉ → is-prop-type-trunc-Propᵉ)
      ( group-Group-of-Order-2ᵉ Gᵉ)
      ( id-iso-Groupᵉ (group-Group-of-Order-2ᵉ Gᵉ))
      ( has-two-elements-Group-of-Order-2ᵉ Gᵉ)

  is-equiv-iso-eq-Group-of-Order-2ᵉ :
    (Hᵉ : Group-of-Order-2ᵉ lᵉ) → is-equivᵉ (iso-eq-Group-of-Order-2ᵉ Hᵉ)
  is-equiv-iso-eq-Group-of-Order-2ᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-Group-of-Order-2ᵉ)
      ( iso-eq-Group-of-Order-2ᵉ)

  eq-iso-Group-of-Order-2ᵉ :
    (Hᵉ : Group-of-Order-2ᵉ lᵉ) → iso-Group-of-Order-2ᵉ Gᵉ Hᵉ → Idᵉ Gᵉ Hᵉ
  eq-iso-Group-of-Order-2ᵉ Hᵉ =
    map-inv-is-equivᵉ (is-equiv-iso-eq-Group-of-Order-2ᵉ Hᵉ)
```

### A homomorphism from any group of order 2 to any group of order 2

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-of-Order-2ᵉ l1ᵉ) (Hᵉ : Group-of-Order-2ᵉ l2ᵉ)
  where

  equiv-Group-of-Order-2ᵉ :
    type-Group-of-Order-2ᵉ Gᵉ ≃ᵉ type-Group-of-Order-2ᵉ Hᵉ
  equiv-Group-of-Order-2ᵉ =
    ( equiv-point-2-Element-Typeᵉ
      ( 2-element-type-Group-of-Order-2ᵉ Hᵉ)
      ( unit-Groupᵉ (group-Group-of-Order-2ᵉ Hᵉ))) ∘eᵉ
    ( inv-equivᵉ
      ( equiv-point-2-Element-Typeᵉ
        ( 2-element-type-Group-of-Order-2ᵉ Gᵉ)
        ( unit-Groupᵉ (group-Group-of-Order-2ᵉ Gᵉ))))

  map-specified-hom-Group-of-Order-2ᵉ :
    type-Group-of-Order-2ᵉ Gᵉ → type-Group-of-Order-2ᵉ Hᵉ
  map-specified-hom-Group-of-Order-2ᵉ =
    map-equivᵉ equiv-Group-of-Order-2ᵉ
```

```text
  specified-hom-Group-of-Order-2ᵉ :
    hom-Groupᵉ (group-Group-of-Order-2ᵉ Gᵉ) (group-Group-of-Order-2ᵉ Hᵉ)
  specified-hom-Group-of-Order-2ᵉ = {!!ᵉ}
```

### The type of groups of order 2 is contractible

```text
is-contr-Group-of-Order-2ᵉ : (lᵉ : Level) → is-contrᵉ (Group-of-Order-2ᵉ lᵉ)
pr1ᵉ (is-contr-Group-of-Order-2ᵉ lᵉ) = symmetric-Group-of-Order-2ᵉ lᵉ
pr2ᵉ (is-contr-Group-of-Order-2ᵉ lᵉ) Gᵉ =
  eq-iso-Group-of-Order-2ᵉ
    ( symmetric-Group-of-Order-2ᵉ lᵉ)
    ( Gᵉ)
    {!!ᵉ}
```