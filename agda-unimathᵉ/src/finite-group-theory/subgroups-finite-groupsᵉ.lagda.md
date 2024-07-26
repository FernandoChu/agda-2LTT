# Subgroups of finite groups

```agda
module finite-group-theory.subgroups-finite-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-groupsᵉ
open import finite-group-theory.finite-semigroupsᵉ

open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.decidable-subgroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ finiteᵉ subgroupᵉ ofᵉ aᵉ finiteᵉ groupᵉ `G`ᵉ isᵉ aᵉ decidableᵉ subgroupᵉ ofᵉ `G`.ᵉ

## Definitions

### Decidable subsets of groups

```agda
decidable-subset-Group-𝔽ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
decidable-subset-Group-𝔽ᵉ lᵉ Gᵉ =
  decidable-subset-Groupᵉ lᵉ (group-Group-𝔽ᵉ Gᵉ)

is-set-decidable-subset-Group-𝔽ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) →
  is-setᵉ (decidable-subset-Group-𝔽ᵉ lᵉ Gᵉ)
is-set-decidable-subset-Group-𝔽ᵉ lᵉ Gᵉ =
  is-set-decidable-subset-Groupᵉ lᵉ (group-Group-𝔽ᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Pᵉ : decidable-subset-Group-𝔽ᵉ l2ᵉ Gᵉ)
  where

  subset-decidable-subset-Group-𝔽ᵉ : subset-Groupᵉ l2ᵉ (group-Group-𝔽ᵉ Gᵉ)
  subset-decidable-subset-Group-𝔽ᵉ =
    subset-decidable-subset-Groupᵉ (group-Group-𝔽ᵉ Gᵉ) Pᵉ
```

### Finite subgroups of finite groups

Byᵉ default,ᵉ finiteᵉ subgroupsᵉ ofᵉ finiteᵉ groupsᵉ areᵉ consideredᵉ to beᵉ decidable.ᵉ
Indeed,ᵉ oneᵉ canᵉ proveᵉ thatᵉ ifᵉ aᵉ subgroupᵉ ofᵉ aᵉ finiteᵉ groupᵉ hasᵉ aᵉ finiteᵉ
underlyingᵉ type,ᵉ thenᵉ itᵉ mustᵉ beᵉ aᵉ decidableᵉ subgroup.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Pᵉ : decidable-subset-Group-𝔽ᵉ l2ᵉ Gᵉ)
  where

  contains-unit-prop-decidable-subset-Group-𝔽ᵉ : Propᵉ l2ᵉ
  contains-unit-prop-decidable-subset-Group-𝔽ᵉ =
    contains-unit-prop-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  contains-unit-decidable-subset-Group-𝔽ᵉ : UUᵉ l2ᵉ
  contains-unit-decidable-subset-Group-𝔽ᵉ =
    contains-unit-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-prop-contains-unit-decidable-subset-Group-𝔽ᵉ :
    is-propᵉ contains-unit-decidable-subset-Group-𝔽ᵉ
  is-prop-contains-unit-decidable-subset-Group-𝔽ᵉ =
    is-prop-contains-unit-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-closed-under-multiplication-prop-decidable-subset-Group-𝔽ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-prop-decidable-subset-Group-𝔽ᵉ =
    is-closed-under-multiplication-prop-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-closed-under-multiplication-decidable-subset-Group-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-decidable-subset-Group-𝔽ᵉ =
    is-closed-under-multiplication-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-prop-is-closed-under-multiplication-decidable-subset-Group-𝔽ᵉ :
    is-propᵉ is-closed-under-multiplication-decidable-subset-Group-𝔽ᵉ
  is-prop-is-closed-under-multiplication-decidable-subset-Group-𝔽ᵉ =
    is-prop-is-closed-under-multiplication-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-closed-under-inverses-prop-decidable-subset-Group-𝔽ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-prop-decidable-subset-Group-𝔽ᵉ =
    is-closed-under-inverses-prop-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-closed-under-inverses-decidable-subset-Group-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-decidable-subset-Group-𝔽ᵉ =
    is-closed-under-inverses-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-prop-is-closed-under-inverses-decidable-subset-Group-𝔽ᵉ :
    is-propᵉ is-closed-under-inverses-decidable-subset-Group-𝔽ᵉ
  is-prop-is-closed-under-inverses-decidable-subset-Group-𝔽ᵉ =
    is-prop-is-closed-under-inverses-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-subgroup-prop-decidable-subset-Group-𝔽ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-prop-decidable-subset-Group-𝔽ᵉ =
    is-subgroup-prop-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-subgroup-decidable-subset-Group-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-decidable-subset-Group-𝔽ᵉ =
    is-subgroup-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

  is-prop-is-subgroup-decidable-subset-Group-𝔽ᵉ :
    is-propᵉ is-subgroup-decidable-subset-Group-𝔽ᵉ
  is-prop-is-subgroup-decidable-subset-Group-𝔽ᵉ =
    is-prop-is-subgroup-decidable-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( Pᵉ)

Subgroup-𝔽ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Subgroup-𝔽ᵉ lᵉ Gᵉ = Decidable-Subgroupᵉ lᵉ (group-Group-𝔽ᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  decidable-subset-Subgroup-𝔽ᵉ : decidable-subset-Groupᵉ l2ᵉ (group-Group-𝔽ᵉ Gᵉ)
  decidable-subset-Subgroup-𝔽ᵉ =
    decidable-subset-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  subset-Subgroup-𝔽ᵉ : subset-Groupᵉ l2ᵉ (group-Group-𝔽ᵉ Gᵉ)
  subset-Subgroup-𝔽ᵉ = subset-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-subgroup-subset-Subgroup-𝔽ᵉ :
    is-subgroup-subset-Groupᵉ (group-Group-𝔽ᵉ Gᵉ) subset-Subgroup-𝔽ᵉ
  is-subgroup-subset-Subgroup-𝔽ᵉ =
    is-subgroup-subset-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  subgroup-Subgroup-𝔽ᵉ : Subgroupᵉ l2ᵉ (group-Group-𝔽ᵉ Gᵉ)
  subgroup-Subgroup-𝔽ᵉ = subgroup-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  type-Subgroup-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Subgroup-𝔽ᵉ = type-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-finite-type-Subgroup-𝔽ᵉ : is-finiteᵉ type-Subgroup-𝔽ᵉ
  is-finite-type-Subgroup-𝔽ᵉ =
    is-finite-type-subset-𝔽ᵉ (finite-type-Group-𝔽ᵉ Gᵉ) decidable-subset-Subgroup-𝔽ᵉ

  finite-type-Subgroup-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  finite-type-Subgroup-𝔽ᵉ =
    finite-type-subset-𝔽ᵉ (finite-type-Group-𝔽ᵉ Gᵉ) decidable-subset-Subgroup-𝔽ᵉ

  inclusion-Subgroup-𝔽ᵉ : type-Subgroup-𝔽ᵉ → type-Group-𝔽ᵉ Gᵉ
  inclusion-Subgroup-𝔽ᵉ = inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-emb-inclusion-Subgroup-𝔽ᵉ : is-embᵉ inclusion-Subgroup-𝔽ᵉ
  is-emb-inclusion-Subgroup-𝔽ᵉ =
    is-emb-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  emb-inclusion-Subgroup-𝔽ᵉ : type-Subgroup-𝔽ᵉ ↪ᵉ type-Group-𝔽ᵉ Gᵉ
  emb-inclusion-Subgroup-𝔽ᵉ =
    emb-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-in-Subgroup-𝔽ᵉ : type-Group-𝔽ᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-Subgroup-𝔽ᵉ = is-in-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-in-subgroup-inclusion-Subgroup-𝔽ᵉ :
    (xᵉ : type-Subgroup-𝔽ᵉ) → is-in-Subgroup-𝔽ᵉ (inclusion-Subgroup-𝔽ᵉ xᵉ)
  is-in-subgroup-inclusion-Subgroup-𝔽ᵉ =
    is-in-subgroup-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-prop-is-in-Subgroup-𝔽ᵉ :
    (xᵉ : type-Group-𝔽ᵉ Gᵉ) → is-propᵉ (is-in-Subgroup-𝔽ᵉ xᵉ)
  is-prop-is-in-Subgroup-𝔽ᵉ =
    is-prop-is-in-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  contains-unit-Subgroup-𝔽ᵉ :
    contains-unit-subset-Groupᵉ (group-Group-𝔽ᵉ Gᵉ) subset-Subgroup-𝔽ᵉ
  contains-unit-Subgroup-𝔽ᵉ =
    contains-unit-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-closed-under-multiplication-Subgroup-𝔽ᵉ :
    is-closed-under-multiplication-subset-Groupᵉ
      ( group-Group-𝔽ᵉ Gᵉ)
      ( subset-Subgroup-𝔽ᵉ)
  is-closed-under-multiplication-Subgroup-𝔽ᵉ =
    is-closed-under-multiplication-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-closed-under-inverses-Subgroup-𝔽ᵉ :
    is-closed-under-inverses-subset-Groupᵉ (group-Group-𝔽ᵉ Gᵉ) subset-Subgroup-𝔽ᵉ
  is-closed-under-inverses-Subgroup-𝔽ᵉ =
    is-closed-under-inverses-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

is-emb-decidable-subset-Subgroup-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) →
  is-embᵉ (decidable-subset-Subgroup-𝔽ᵉ {l2ᵉ = l2ᵉ} Gᵉ)
is-emb-decidable-subset-Subgroup-𝔽ᵉ Gᵉ =
  is-emb-decidable-subset-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ)
```

### The underlying group of a decidable subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  type-group-Subgroup-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-group-Subgroup-𝔽ᵉ = type-Subgroup-𝔽ᵉ Gᵉ Hᵉ

  map-inclusion-group-Subgroup-𝔽ᵉ :
    type-group-Subgroup-𝔽ᵉ → type-Group-𝔽ᵉ Gᵉ
  map-inclusion-group-Subgroup-𝔽ᵉ = inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ

  is-emb-inclusion-group-Subgroup-𝔽ᵉ :
    is-embᵉ map-inclusion-group-Subgroup-𝔽ᵉ
  is-emb-inclusion-group-Subgroup-𝔽ᵉ = is-emb-inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ

  eq-subgroup-eq-Group-𝔽ᵉ :
    {xᵉ yᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ} →
    ( inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ xᵉ ＝ᵉ inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-subgroup-eq-Group-𝔽ᵉ =
    eq-decidable-subgroup-eq-groupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  set-group-Subgroup-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-group-Subgroup-𝔽ᵉ = set-group-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  mul-Subgroup-𝔽ᵉ : (xᵉ yᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) → type-Subgroup-𝔽ᵉ Gᵉ Hᵉ
  mul-Subgroup-𝔽ᵉ = mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  associative-mul-Subgroup-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) →
    mul-Subgroup-𝔽ᵉ (mul-Subgroup-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Subgroup-𝔽ᵉ xᵉ (mul-Subgroup-𝔽ᵉ yᵉ zᵉ)
  associative-mul-Subgroup-𝔽ᵉ =
    associative-mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  unit-Subgroup-𝔽ᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ
  unit-Subgroup-𝔽ᵉ = unit-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  left-unit-law-mul-Subgroup-𝔽ᵉ :
    (xᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) → mul-Subgroup-𝔽ᵉ unit-Subgroup-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Subgroup-𝔽ᵉ =
    left-unit-law-mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  right-unit-law-mul-Subgroup-𝔽ᵉ :
    (xᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) → mul-Subgroup-𝔽ᵉ xᵉ unit-Subgroup-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Subgroup-𝔽ᵉ =
    right-unit-law-mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  inv-Subgroup-𝔽ᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ → type-Subgroup-𝔽ᵉ Gᵉ Hᵉ
  inv-Subgroup-𝔽ᵉ = inv-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  left-inverse-law-mul-Subgroup-𝔽ᵉ :
    ( xᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) →
    mul-Subgroup-𝔽ᵉ (inv-Subgroup-𝔽ᵉ xᵉ) xᵉ ＝ᵉ unit-Subgroup-𝔽ᵉ
  left-inverse-law-mul-Subgroup-𝔽ᵉ =
    left-inverse-law-mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  right-inverse-law-mul-Subgroup-𝔽ᵉ :
    (xᵉ : type-Subgroup-𝔽ᵉ Gᵉ Hᵉ) →
    mul-Subgroup-𝔽ᵉ xᵉ (inv-Subgroup-𝔽ᵉ xᵉ) ＝ᵉ unit-Subgroup-𝔽ᵉ
  right-inverse-law-mul-Subgroup-𝔽ᵉ =
    right-inverse-law-mul-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  finite-semigroup-Subgroup-𝔽ᵉ : Semigroup-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ finite-semigroup-Subgroup-𝔽ᵉ = finite-type-Subgroup-𝔽ᵉ Gᵉ Hᵉ
  pr1ᵉ (pr2ᵉ finite-semigroup-Subgroup-𝔽ᵉ) = mul-Subgroup-𝔽ᵉ
  pr2ᵉ (pr2ᵉ finite-semigroup-Subgroup-𝔽ᵉ) = associative-mul-Subgroup-𝔽ᵉ

  finite-group-Subgroup-𝔽ᵉ : Group-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ finite-group-Subgroup-𝔽ᵉ = finite-semigroup-Subgroup-𝔽ᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ)) = unit-Subgroup-𝔽ᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ))) = left-unit-law-mul-Subgroup-𝔽ᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ))) = right-unit-law-mul-Subgroup-𝔽ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ)) = inv-Subgroup-𝔽ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ))) =
    left-inverse-law-mul-Subgroup-𝔽ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ finite-group-Subgroup-𝔽ᵉ))) =
    right-inverse-law-mul-Subgroup-𝔽ᵉ

semigroup-Subgroup-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) → Subgroup-𝔽ᵉ l2ᵉ Gᵉ → Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
semigroup-Subgroup-𝔽ᵉ Gᵉ Hᵉ =
  semigroup-Semigroup-𝔽ᵉ (finite-semigroup-Subgroup-𝔽ᵉ Gᵉ Hᵉ)

group-Subgroup-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) → Subgroup-𝔽ᵉ l2ᵉ Gᵉ → Groupᵉ (l1ᵉ ⊔ l2ᵉ)
group-Subgroup-𝔽ᵉ Gᵉ Hᵉ = group-Group-𝔽ᵉ (finite-group-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
```

### The inclusion homomorphism of the underlying finite group of a finite subgroup into the ambient group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  preserves-mul-inclusion-group-Subgroup-𝔽ᵉ :
    preserves-mul-Groupᵉ
      ( group-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
      ( group-Group-𝔽ᵉ Gᵉ)
      ( inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
  preserves-mul-inclusion-group-Subgroup-𝔽ᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ {xᵉ} {yᵉ}

  preserves-unit-inclusion-group-Subgroup-𝔽ᵉ :
    preserves-unit-Groupᵉ
      ( group-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
      ( group-Group-𝔽ᵉ Gᵉ)
      ( inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
  preserves-unit-inclusion-group-Subgroup-𝔽ᵉ =
    preserves-unit-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  preserves-inverses-inclusion-group-Subgroup-𝔽ᵉ :
    preserves-inverses-Groupᵉ
      ( group-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
      ( group-Group-𝔽ᵉ Gᵉ)
      ( inclusion-Subgroup-𝔽ᵉ Gᵉ Hᵉ)
  preserves-inverses-inclusion-group-Subgroup-𝔽ᵉ {xᵉ} =
    preserves-inverses-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ {xᵉ}

  inclusion-group-Subgroup-𝔽ᵉ :
    hom-Groupᵉ (group-Subgroup-𝔽ᵉ Gᵉ Hᵉ) (group-Group-𝔽ᵉ Gᵉ)
  inclusion-group-Subgroup-𝔽ᵉ =
    hom-inclusion-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  has-same-elements-Subgroup-𝔽ᵉ :
    {l3ᵉ : Level} → Subgroup-𝔽ᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Subgroup-𝔽ᵉ =
    has-same-elements-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  extensionality-Subgroup-𝔽ᵉ :
    (Kᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ) → (Hᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Subgroup-𝔽ᵉ Kᵉ
  extensionality-Subgroup-𝔽ᵉ =
    extensionality-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ
```

### Every finite subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  right-sim-Subgroup-𝔽ᵉ : (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → UUᵉ l2ᵉ
  right-sim-Subgroup-𝔽ᵉ = right-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-prop-right-sim-Subgroup-𝔽ᵉ :
    (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → is-propᵉ (right-sim-Subgroup-𝔽ᵉ xᵉ yᵉ)
  is-prop-right-sim-Subgroup-𝔽ᵉ =
    is-prop-right-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  prop-right-equivalence-relation-Subgroup-𝔽ᵉ :
    (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → Propᵉ l2ᵉ
  prop-right-equivalence-relation-Subgroup-𝔽ᵉ =
    prop-right-equivalence-relation-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  refl-right-sim-Subgroup-𝔽ᵉ : is-reflexiveᵉ right-sim-Subgroup-𝔽ᵉ
  refl-right-sim-Subgroup-𝔽ᵉ =
    refl-right-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  symmetric-right-sim-Subgroup-𝔽ᵉ : is-symmetricᵉ right-sim-Subgroup-𝔽ᵉ
  symmetric-right-sim-Subgroup-𝔽ᵉ =
    symmetric-right-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  transitive-right-sim-Subgroup-𝔽ᵉ : is-transitiveᵉ right-sim-Subgroup-𝔽ᵉ
  transitive-right-sim-Subgroup-𝔽ᵉ =
    transitive-right-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  right-equivalence-relation-Subgroup-𝔽ᵉ :
    equivalence-relationᵉ l2ᵉ (type-Group-𝔽ᵉ Gᵉ)
  right-equivalence-relation-Subgroup-𝔽ᵉ =
    right-equivalence-relation-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Group-𝔽ᵉ l1ᵉ) (Hᵉ : Subgroup-𝔽ᵉ l2ᵉ Gᵉ)
  where

  left-sim-Subgroup-𝔽ᵉ : (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → UUᵉ l2ᵉ
  left-sim-Subgroup-𝔽ᵉ = left-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  is-prop-left-sim-Subgroup-𝔽ᵉ :
    (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → is-propᵉ (left-sim-Subgroup-𝔽ᵉ xᵉ yᵉ)
  is-prop-left-sim-Subgroup-𝔽ᵉ =
    is-prop-left-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  prop-left-equivalence-relation-Subgroup-𝔽ᵉ : (xᵉ yᵉ : type-Group-𝔽ᵉ Gᵉ) → Propᵉ l2ᵉ
  prop-left-equivalence-relation-Subgroup-𝔽ᵉ =
    prop-left-equivalence-relation-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  refl-left-sim-Subgroup-𝔽ᵉ : is-reflexiveᵉ left-sim-Subgroup-𝔽ᵉ
  refl-left-sim-Subgroup-𝔽ᵉ =
    refl-left-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  symmetric-left-sim-Subgroup-𝔽ᵉ : is-symmetricᵉ left-sim-Subgroup-𝔽ᵉ
  symmetric-left-sim-Subgroup-𝔽ᵉ =
    symmetric-left-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  transitive-left-sim-Subgroup-𝔽ᵉ : is-transitiveᵉ left-sim-Subgroup-𝔽ᵉ
  transitive-left-sim-Subgroup-𝔽ᵉ =
    transitive-left-sim-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ

  left-equivalence-relation-Subgroup-𝔽ᵉ :
    equivalence-relationᵉ l2ᵉ (type-Group-𝔽ᵉ Gᵉ)
  left-equivalence-relation-Subgroup-𝔽ᵉ =
    left-equivalence-relation-Decidable-Subgroupᵉ (group-Group-𝔽ᵉ Gᵉ) Hᵉ
```