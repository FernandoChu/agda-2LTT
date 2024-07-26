# Decidable subgroups of groups

```agda
module group-theory.decidable-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Aᵉ decidableᵉ subgroupᵉ ofᵉ aᵉ groupᵉ `G`ᵉ isᵉ aᵉ subgroupᵉ ofᵉ `G`ᵉ definedᵉ byᵉ aᵉ decidableᵉ
predicateᵉ onᵉ theᵉ typeᵉ ofᵉ elementsᵉ ofᵉ `G`.ᵉ

## Definitions

### Decidable subsets of groups

```agda
decidable-subset-Groupᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
decidable-subset-Groupᵉ lᵉ Gᵉ = decidable-subtypeᵉ lᵉ (type-Groupᵉ Gᵉ)

is-set-decidable-subset-Groupᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → is-setᵉ (decidable-subset-Groupᵉ lᵉ Gᵉ)
is-set-decidable-subset-Groupᵉ lᵉ Gᵉ = is-set-decidable-subtypeᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Pᵉ : decidable-subset-Groupᵉ l2ᵉ Gᵉ)
  where

  subset-decidable-subset-Groupᵉ : subset-Groupᵉ l2ᵉ Gᵉ
  subset-decidable-subset-Groupᵉ = subtype-decidable-subtypeᵉ Pᵉ
```

### Decidable subgroups of groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Pᵉ : decidable-subset-Groupᵉ l2ᵉ Gᵉ)
  where

  contains-unit-prop-decidable-subset-Groupᵉ : Propᵉ l2ᵉ
  contains-unit-prop-decidable-subset-Groupᵉ =
    contains-unit-prop-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  contains-unit-decidable-subset-Groupᵉ : UUᵉ l2ᵉ
  contains-unit-decidable-subset-Groupᵉ =
    contains-unit-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-prop-contains-unit-decidable-subset-Groupᵉ :
    is-propᵉ contains-unit-decidable-subset-Groupᵉ
  is-prop-contains-unit-decidable-subset-Groupᵉ =
    is-prop-contains-unit-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-closed-under-multiplication-prop-decidable-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-prop-decidable-subset-Groupᵉ =
    is-closed-under-multiplication-prop-subset-Groupᵉ Gᵉ
      ( subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-closed-under-multiplication-decidable-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-decidable-subset-Groupᵉ =
    is-closed-under-multiplication-subset-Groupᵉ Gᵉ
      ( subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-prop-is-closed-under-multiplication-decidable-subset-Groupᵉ :
    is-propᵉ is-closed-under-multiplication-decidable-subset-Groupᵉ
  is-prop-is-closed-under-multiplication-decidable-subset-Groupᵉ =
    is-prop-is-closed-under-multiplication-subset-Groupᵉ Gᵉ
      ( subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-closed-under-inverses-prop-decidable-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-prop-decidable-subset-Groupᵉ =
    is-closed-under-inverses-prop-subset-Groupᵉ Gᵉ
      ( subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-closed-under-inverses-decidable-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-inverses-decidable-subset-Groupᵉ =
    is-closed-under-inverses-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-prop-is-closed-under-inverses-decidable-subset-Groupᵉ :
    is-propᵉ is-closed-under-inverses-decidable-subset-Groupᵉ
  is-prop-is-closed-under-inverses-decidable-subset-Groupᵉ =
    is-prop-is-closed-under-inverses-subset-Groupᵉ Gᵉ
      ( subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-subgroup-prop-decidable-subset-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-prop-decidable-subset-Groupᵉ =
    is-subgroup-prop-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-subgroup-decidable-subset-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-decidable-subset-Groupᵉ =
    is-subgroup-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

  is-prop-is-subgroup-decidable-subset-Groupᵉ :
    is-propᵉ is-subgroup-decidable-subset-Groupᵉ
  is-prop-is-subgroup-decidable-subset-Groupᵉ =
    is-prop-is-subgroup-subset-Groupᵉ Gᵉ (subset-decidable-subset-Groupᵉ Gᵉ Pᵉ)

Decidable-Subgroupᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Decidable-Subgroupᵉ lᵉ Gᵉ =
  type-subtypeᵉ (is-subgroup-prop-decidable-subset-Groupᵉ {l2ᵉ = lᵉ} Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  decidable-subset-Decidable-Subgroupᵉ : decidable-subset-Groupᵉ l2ᵉ Gᵉ
  decidable-subset-Decidable-Subgroupᵉ =
    inclusion-subtypeᵉ (is-subgroup-prop-decidable-subset-Groupᵉ Gᵉ) Hᵉ

  subset-Decidable-Subgroupᵉ : subset-Groupᵉ l2ᵉ Gᵉ
  subset-Decidable-Subgroupᵉ =
    subtype-decidable-subtypeᵉ decidable-subset-Decidable-Subgroupᵉ

  is-subgroup-subset-Decidable-Subgroupᵉ :
    is-subgroup-subset-Groupᵉ Gᵉ subset-Decidable-Subgroupᵉ
  is-subgroup-subset-Decidable-Subgroupᵉ = pr2ᵉ Hᵉ

  subgroup-Decidable-Subgroupᵉ : Subgroupᵉ l2ᵉ Gᵉ
  pr1ᵉ subgroup-Decidable-Subgroupᵉ = subset-Decidable-Subgroupᵉ
  pr2ᵉ subgroup-Decidable-Subgroupᵉ = is-subgroup-subset-Decidable-Subgroupᵉ

  type-Decidable-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Decidable-Subgroupᵉ =
    type-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  inclusion-Decidable-Subgroupᵉ : type-Decidable-Subgroupᵉ → type-Groupᵉ Gᵉ
  inclusion-Decidable-Subgroupᵉ =
    inclusion-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-emb-inclusion-Decidable-Subgroupᵉ : is-embᵉ inclusion-Decidable-Subgroupᵉ
  is-emb-inclusion-Decidable-Subgroupᵉ =
    is-emb-inclusion-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  emb-inclusion-Decidable-Subgroupᵉ : type-Decidable-Subgroupᵉ ↪ᵉ type-Groupᵉ Gᵉ
  emb-inclusion-Decidable-Subgroupᵉ =
    emb-inclusion-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-in-Decidable-Subgroupᵉ : type-Groupᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-Decidable-Subgroupᵉ =
    is-in-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-in-subgroup-inclusion-Decidable-Subgroupᵉ :
    (xᵉ : type-Decidable-Subgroupᵉ) →
    is-in-Decidable-Subgroupᵉ (inclusion-Decidable-Subgroupᵉ xᵉ)
  is-in-subgroup-inclusion-Decidable-Subgroupᵉ =
    is-in-subgroup-inclusion-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-prop-is-in-Decidable-Subgroupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (is-in-Decidable-Subgroupᵉ xᵉ)
  is-prop-is-in-Decidable-Subgroupᵉ =
    is-prop-is-in-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-subgroup-Decidable-Subgroupᵉ :
    is-subgroup-decidable-subset-Groupᵉ Gᵉ decidable-subset-Decidable-Subgroupᵉ
  is-subgroup-Decidable-Subgroupᵉ =
    is-subgroup-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  contains-unit-Decidable-Subgroupᵉ :
    contains-unit-decidable-subset-Groupᵉ Gᵉ decidable-subset-Decidable-Subgroupᵉ
  contains-unit-Decidable-Subgroupᵉ =
    contains-unit-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-closed-under-multiplication-Decidable-Subgroupᵉ :
    is-closed-under-multiplication-decidable-subset-Groupᵉ Gᵉ
      decidable-subset-Decidable-Subgroupᵉ
  is-closed-under-multiplication-Decidable-Subgroupᵉ =
    is-closed-under-multiplication-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

  is-closed-under-inverses-Decidable-Subgroupᵉ :
    is-closed-under-inverses-decidable-subset-Groupᵉ Gᵉ
      decidable-subset-Decidable-Subgroupᵉ
  is-closed-under-inverses-Decidable-Subgroupᵉ =
    is-closed-under-inverses-Subgroupᵉ Gᵉ subgroup-Decidable-Subgroupᵉ

is-emb-decidable-subset-Decidable-Subgroupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) →
    is-embᵉ (decidable-subset-Decidable-Subgroupᵉ {l2ᵉ = l2ᵉ} Gᵉ)
is-emb-decidable-subset-Decidable-Subgroupᵉ Gᵉ =
  is-emb-inclusion-subtypeᵉ (is-subgroup-prop-decidable-subset-Groupᵉ Gᵉ)
```

### The underlying group of a decidable subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  type-group-Decidable-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-group-Decidable-Subgroupᵉ =
    type-group-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  map-inclusion-Decidable-Subgroupᵉ :
    type-group-Decidable-Subgroupᵉ → type-Groupᵉ Gᵉ
  map-inclusion-Decidable-Subgroupᵉ =
    map-inclusion-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  eq-decidable-subgroup-eq-groupᵉ :
    {xᵉ yᵉ : type-group-Decidable-Subgroupᵉ} →
    ( map-inclusion-Decidable-Subgroupᵉ xᵉ ＝ᵉ
      map-inclusion-Decidable-Subgroupᵉ yᵉ) →
    xᵉ ＝ᵉ yᵉ
  eq-decidable-subgroup-eq-groupᵉ =
    eq-subgroup-eq-groupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  set-group-Decidable-Subgroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-group-Decidable-Subgroupᵉ =
    set-group-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  mul-Decidable-Subgroupᵉ :
    (xᵉ yᵉ : type-group-Decidable-Subgroupᵉ) → type-group-Decidable-Subgroupᵉ
  mul-Decidable-Subgroupᵉ = mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  associative-mul-Decidable-Subgroupᵉ :
    (xᵉ yᵉ zᵉ : type-group-Decidable-Subgroupᵉ) →
    Idᵉ
      ( mul-Decidable-Subgroupᵉ (mul-Decidable-Subgroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-Decidable-Subgroupᵉ xᵉ (mul-Decidable-Subgroupᵉ yᵉ zᵉ))
  associative-mul-Decidable-Subgroupᵉ =
    associative-mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  unit-Decidable-Subgroupᵉ : type-group-Decidable-Subgroupᵉ
  unit-Decidable-Subgroupᵉ = unit-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  left-unit-law-mul-Decidable-Subgroupᵉ :
    (xᵉ : type-group-Decidable-Subgroupᵉ) →
    Idᵉ (mul-Decidable-Subgroupᵉ unit-Decidable-Subgroupᵉ xᵉ) xᵉ
  left-unit-law-mul-Decidable-Subgroupᵉ =
    left-unit-law-mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  right-unit-law-mul-Decidable-Subgroupᵉ :
    (xᵉ : type-group-Decidable-Subgroupᵉ) →
    Idᵉ (mul-Decidable-Subgroupᵉ xᵉ unit-Decidable-Subgroupᵉ) xᵉ
  right-unit-law-mul-Decidable-Subgroupᵉ =
    right-unit-law-mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  inv-Decidable-Subgroupᵉ :
    type-group-Decidable-Subgroupᵉ → type-group-Decidable-Subgroupᵉ
  inv-Decidable-Subgroupᵉ = inv-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  left-inverse-law-mul-Decidable-Subgroupᵉ :
    ( xᵉ : type-group-Decidable-Subgroupᵉ) →
    Idᵉ
      ( mul-Decidable-Subgroupᵉ (inv-Decidable-Subgroupᵉ xᵉ) xᵉ)
      ( unit-Decidable-Subgroupᵉ)
  left-inverse-law-mul-Decidable-Subgroupᵉ =
    left-inverse-law-mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  right-inverse-law-mul-Decidable-Subgroupᵉ :
    (xᵉ : type-group-Decidable-Subgroupᵉ) →
    Idᵉ
      ( mul-Decidable-Subgroupᵉ xᵉ (inv-Decidable-Subgroupᵉ xᵉ))
      ( unit-Decidable-Subgroupᵉ)
  right-inverse-law-mul-Decidable-Subgroupᵉ =
    right-inverse-law-mul-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  semigroup-Decidable-Subgroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Decidable-Subgroupᵉ =
    semigroup-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  group-Decidable-Subgroupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Decidable-Subgroupᵉ = group-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
```

### The inclusion of the underlying group of a subgroup into the ambient group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  preserves-mul-inclusion-Decidable-Subgroupᵉ :
    preserves-mul-Groupᵉ
      ( group-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Decidable-Subgroupᵉ Gᵉ Hᵉ)
  preserves-mul-inclusion-Decidable-Subgroupᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ) {xᵉ} {yᵉ}

  preserves-unit-inclusion-Decidable-Subgroupᵉ :
    preserves-unit-Groupᵉ
      ( group-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Decidable-Subgroupᵉ Gᵉ Hᵉ)
  preserves-unit-inclusion-Decidable-Subgroupᵉ =
    preserves-unit-inclusion-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  preserves-inverses-inclusion-Decidable-Subgroupᵉ :
    preserves-inverses-Groupᵉ
      ( group-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      ( Gᵉ)
      ( map-inclusion-Decidable-Subgroupᵉ Gᵉ Hᵉ)
  preserves-inverses-inclusion-Decidable-Subgroupᵉ {xᵉ} =
    preserves-inverses-inclusion-Subgroupᵉ Gᵉ
      ( subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      { xᵉ}

  hom-inclusion-Decidable-Subgroupᵉ :
    hom-Groupᵉ (group-Decidable-Subgroupᵉ Gᵉ Hᵉ) Gᵉ
  hom-inclusion-Decidable-Subgroupᵉ =
    hom-inclusion-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
```

## Properties

### Extensionality of the type of all subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  has-same-elements-Decidable-Subgroupᵉ :
    {l3ᵉ : Level} → Decidable-Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Decidable-Subgroupᵉ Kᵉ =
    has-same-elements-decidable-subtypeᵉ
      ( decidable-subset-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      ( decidable-subset-Decidable-Subgroupᵉ Gᵉ Kᵉ)

  extensionality-Decidable-Subgroupᵉ :
    (Kᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ) →
    (Hᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Decidable-Subgroupᵉ Kᵉ
  extensionality-Decidable-Subgroupᵉ =
    extensionality-type-subtypeᵉ
      ( is-subgroup-prop-decidable-subset-Groupᵉ Gᵉ)
      ( is-subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
      ( λ xᵉ → pairᵉ idᵉ idᵉ)
      ( extensionality-decidable-subtypeᵉ
        ( decidable-subset-Decidable-Subgroupᵉ Gᵉ Hᵉ))
```

### Every subgroup induces two equivalence relations

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `xu = y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  right-sim-Decidable-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  right-sim-Decidable-Subgroupᵉ =
    right-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  is-prop-right-sim-Decidable-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (right-sim-Decidable-Subgroupᵉ xᵉ yᵉ)
  is-prop-right-sim-Decidable-Subgroupᵉ =
    is-prop-right-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  prop-right-equivalence-relation-Decidable-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ l2ᵉ
  prop-right-equivalence-relation-Decidable-Subgroupᵉ =
    prop-right-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  refl-right-sim-Decidable-Subgroupᵉ :
    is-reflexiveᵉ right-sim-Decidable-Subgroupᵉ
  refl-right-sim-Decidable-Subgroupᵉ =
    refl-right-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  symmetric-right-sim-Decidable-Subgroupᵉ :
    is-symmetricᵉ right-sim-Decidable-Subgroupᵉ
  symmetric-right-sim-Decidable-Subgroupᵉ =
    symmetric-right-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  transitive-right-sim-Decidable-Subgroupᵉ :
    is-transitiveᵉ right-sim-Decidable-Subgroupᵉ
  transitive-right-sim-Decidable-Subgroupᵉ =
    transitive-right-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  right-equivalence-relation-Decidable-Subgroupᵉ :
    equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  right-equivalence-relation-Decidable-Subgroupᵉ =
    right-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
```

#### The equivalence relation where `x ~ y` if and only if there exists `u : H` such that `ux = y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Decidable-Subgroupᵉ l2ᵉ Gᵉ)
  where

  left-sim-Decidable-Subgroupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ l2ᵉ
  left-sim-Decidable-Subgroupᵉ =
    left-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  is-prop-left-sim-Decidable-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (left-sim-Decidable-Subgroupᵉ xᵉ yᵉ)
  is-prop-left-sim-Decidable-Subgroupᵉ =
    is-prop-left-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  prop-left-equivalence-relation-Decidable-Subgroupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ l2ᵉ
  prop-left-equivalence-relation-Decidable-Subgroupᵉ =
    prop-left-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  refl-left-sim-Decidable-Subgroupᵉ :
    is-reflexiveᵉ left-sim-Decidable-Subgroupᵉ
  refl-left-sim-Decidable-Subgroupᵉ =
    refl-left-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  symmetric-left-sim-Decidable-Subgroupᵉ :
    is-symmetricᵉ left-sim-Decidable-Subgroupᵉ
  symmetric-left-sim-Decidable-Subgroupᵉ =
    symmetric-left-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  transitive-left-sim-Decidable-Subgroupᵉ :
    is-transitiveᵉ left-sim-Decidable-Subgroupᵉ
  transitive-left-sim-Decidable-Subgroupᵉ =
    transitive-left-sim-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)

  left-equivalence-relation-Decidable-Subgroupᵉ :
    equivalence-relationᵉ l2ᵉ (type-Groupᵉ Gᵉ)
  left-equivalence-relation-Decidable-Subgroupᵉ =
    left-equivalence-relation-Subgroupᵉ Gᵉ (subgroup-Decidable-Subgroupᵉ Gᵉ Hᵉ)
```