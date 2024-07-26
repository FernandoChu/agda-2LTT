# Subgroups of abelian groups

```agda
module group-theory.subgroups-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.congruence-relations-abelian-groupsᵉ
open import group-theory.congruence-relations-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-abelian-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-abelian-groupsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Definitions

### Subgroups of abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Pᵉ : subset-Abᵉ l2ᵉ Aᵉ)
  where

  contains-zero-subset-Abᵉ : UUᵉ l2ᵉ
  contains-zero-subset-Abᵉ = contains-unit-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-prop-contains-zero-subset-Abᵉ : is-propᵉ contains-zero-subset-Abᵉ
  is-prop-contains-zero-subset-Abᵉ =
    is-prop-contains-unit-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-closed-under-addition-subset-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-addition-subset-Abᵉ =
    is-closed-under-multiplication-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-prop-is-closed-under-addition-subset-Abᵉ :
    is-propᵉ is-closed-under-addition-subset-Abᵉ
  is-prop-is-closed-under-addition-subset-Abᵉ =
    is-prop-is-closed-under-multiplication-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-closed-under-negatives-subset-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-negatives-subset-Abᵉ =
    is-closed-under-inverses-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-prop-closed-under-neg-subset-Abᵉ :
    is-propᵉ is-closed-under-negatives-subset-Abᵉ
  is-prop-closed-under-neg-subset-Abᵉ =
    is-prop-is-closed-under-inverses-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-subgroup-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subgroup-Abᵉ = is-subgroup-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ

  is-prop-is-subgroup-Abᵉ : is-propᵉ is-subgroup-Abᵉ
  is-prop-is-subgroup-Abᵉ = is-prop-is-subgroup-subset-Groupᵉ (group-Abᵉ Aᵉ) Pᵉ
```

### The type of all subgroups of an abelian group

```agda
Subgroup-Abᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
Subgroup-Abᵉ lᵉ Aᵉ = Subgroupᵉ lᵉ (group-Abᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  subset-Subgroup-Abᵉ : subset-Abᵉ l2ᵉ Aᵉ
  subset-Subgroup-Abᵉ = subset-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  type-Subgroup-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Subgroup-Abᵉ = type-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  inclusion-Subgroup-Abᵉ : type-Subgroup-Abᵉ → type-Abᵉ Aᵉ
  inclusion-Subgroup-Abᵉ = inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-emb-inclusion-Subgroup-Abᵉ : is-embᵉ inclusion-Subgroup-Abᵉ
  is-emb-inclusion-Subgroup-Abᵉ =
    is-emb-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  emb-inclusion-Subgroup-Abᵉ : type-Subgroup-Abᵉ ↪ᵉ type-Abᵉ Aᵉ
  emb-inclusion-Subgroup-Abᵉ = emb-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-in-Subgroup-Abᵉ : type-Abᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-Subgroup-Abᵉ = is-in-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-closed-under-eq-Subgroup-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    is-in-Subgroup-Abᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-Subgroup-Abᵉ yᵉ
  is-closed-under-eq-Subgroup-Abᵉ =
    is-closed-under-eq-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-closed-under-eq-Subgroup-Ab'ᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    is-in-Subgroup-Abᵉ yᵉ → xᵉ ＝ᵉ yᵉ → is-in-Subgroup-Abᵉ xᵉ
  is-closed-under-eq-Subgroup-Ab'ᵉ =
    is-closed-under-eq-Subgroup'ᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-in-subgroup-inclusion-Subgroup-Abᵉ :
    (xᵉ : type-Subgroup-Abᵉ) →
    is-in-Subgroup-Abᵉ (inclusion-Subgroup-Abᵉ xᵉ)
  is-in-subgroup-inclusion-Subgroup-Abᵉ =
    is-in-subgroup-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-prop-is-in-Subgroup-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → is-propᵉ (is-in-Subgroup-Abᵉ xᵉ)
  is-prop-is-in-Subgroup-Abᵉ =
    is-prop-is-in-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-subgroup-Subgroup-Abᵉ :
    is-subgroup-Abᵉ Aᵉ subset-Subgroup-Abᵉ
  is-subgroup-Subgroup-Abᵉ = is-subgroup-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  contains-zero-Subgroup-Abᵉ :
    contains-zero-subset-Abᵉ Aᵉ subset-Subgroup-Abᵉ
  contains-zero-Subgroup-Abᵉ = contains-unit-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-closed-under-addition-Subgroup-Abᵉ :
    is-closed-under-addition-subset-Abᵉ Aᵉ subset-Subgroup-Abᵉ
  is-closed-under-addition-Subgroup-Abᵉ =
    is-closed-under-multiplication-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-closed-under-negatives-Subgroup-Abᵉ :
    is-closed-under-negatives-subset-Abᵉ Aᵉ subset-Subgroup-Abᵉ
  is-closed-under-negatives-Subgroup-Abᵉ =
    is-closed-under-inverses-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-in-subgroup-left-summand-Subgroup-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    is-in-Subgroup-Abᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) → is-in-Subgroup-Abᵉ yᵉ →
    is-in-Subgroup-Abᵉ xᵉ
  is-in-subgroup-left-summand-Subgroup-Abᵉ =
    is-in-subgroup-left-factor-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-in-subgroup-right-summand-Subgroup-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    is-in-Subgroup-Abᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) → is-in-Subgroup-Abᵉ xᵉ →
    is-in-Subgroup-Abᵉ yᵉ
  is-in-subgroup-right-summand-Subgroup-Abᵉ =
    is-in-subgroup-right-factor-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

is-emb-subset-Subgroup-Abᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → is-embᵉ (subset-Subgroup-Abᵉ {l2ᵉ = l2ᵉ} Aᵉ)
is-emb-subset-Subgroup-Abᵉ Aᵉ = is-emb-subset-Subgroupᵉ (group-Abᵉ Aᵉ)
```

### The underlying abelian group of a subgroup of an abelian group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  type-ab-Subgroup-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-ab-Subgroup-Abᵉ = type-group-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  map-inclusion-Subgroup-Abᵉ : type-ab-Subgroup-Abᵉ → type-Abᵉ Aᵉ
  map-inclusion-Subgroup-Abᵉ = map-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  is-emb-incl-ab-Subgroup-Abᵉ : is-embᵉ map-inclusion-Subgroup-Abᵉ
  is-emb-incl-ab-Subgroup-Abᵉ = is-emb-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  eq-subgroup-ab-eq-abᵉ :
    {xᵉ yᵉ : type-ab-Subgroup-Abᵉ} →
    Idᵉ (map-inclusion-Subgroup-Abᵉ xᵉ) (map-inclusion-Subgroup-Abᵉ yᵉ) →
    Idᵉ xᵉ yᵉ
  eq-subgroup-ab-eq-abᵉ = eq-subgroup-eq-groupᵉ (group-Abᵉ Aᵉ) Bᵉ

  set-ab-Subgroup-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-ab-Subgroup-Abᵉ = set-group-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  zero-ab-Subgroup-Abᵉ : type-ab-Subgroup-Abᵉ
  zero-ab-Subgroup-Abᵉ = unit-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  add-ab-Subgroup-Abᵉ : (xᵉ yᵉ : type-ab-Subgroup-Abᵉ) → type-ab-Subgroup-Abᵉ
  add-ab-Subgroup-Abᵉ = mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  neg-ab-Subgroup-Abᵉ : type-ab-Subgroup-Abᵉ → type-ab-Subgroup-Abᵉ
  neg-ab-Subgroup-Abᵉ = inv-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  associative-add-Subgroup-Abᵉ :
    ( xᵉ yᵉ zᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ
      ( add-ab-Subgroup-Abᵉ (add-ab-Subgroup-Abᵉ xᵉ yᵉ) zᵉ)
      ( add-ab-Subgroup-Abᵉ xᵉ (add-ab-Subgroup-Abᵉ yᵉ zᵉ))
  associative-add-Subgroup-Abᵉ =
    associative-mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  left-unit-law-add-Subgroup-Abᵉ :
    (xᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ (add-ab-Subgroup-Abᵉ zero-ab-Subgroup-Abᵉ xᵉ) xᵉ
  left-unit-law-add-Subgroup-Abᵉ =
    left-unit-law-mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  right-unit-law-add-Subgroup-Abᵉ :
    (xᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ (add-ab-Subgroup-Abᵉ xᵉ zero-ab-Subgroup-Abᵉ) xᵉ
  right-unit-law-add-Subgroup-Abᵉ =
    right-unit-law-mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  left-inverse-law-add-Subgroup-Abᵉ :
    (xᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ
      ( add-ab-Subgroup-Abᵉ (neg-ab-Subgroup-Abᵉ xᵉ) xᵉ)
      ( zero-ab-Subgroup-Abᵉ)
  left-inverse-law-add-Subgroup-Abᵉ =
    left-inverse-law-mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  right-inverse-law-add-Subgroup-Abᵉ :
    (xᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ
      ( add-ab-Subgroup-Abᵉ xᵉ (neg-ab-Subgroup-Abᵉ xᵉ))
      ( zero-ab-Subgroup-Abᵉ)
  right-inverse-law-add-Subgroup-Abᵉ =
    right-inverse-law-mul-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  commutative-add-Subgroup-Abᵉ :
    ( xᵉ yᵉ : type-ab-Subgroup-Abᵉ) →
    Idᵉ ( add-ab-Subgroup-Abᵉ xᵉ yᵉ) (add-ab-Subgroup-Abᵉ yᵉ xᵉ)
  commutative-add-Subgroup-Abᵉ xᵉ yᵉ =
    eq-subgroup-ab-eq-abᵉ (commutative-add-Abᵉ Aᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))

  semigroup-Subgroup-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Subgroup-Abᵉ = semigroup-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  group-Subgroup-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Subgroup-Abᵉ = group-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  ab-Subgroup-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ ab-Subgroup-Abᵉ = group-Subgroup-Abᵉ
  pr2ᵉ ab-Subgroup-Abᵉ = commutative-add-Subgroup-Abᵉ
```

### The inclusion of the underlying group of a subgroup into the ambient abelian group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  preserves-add-inclusion-Subgroup-Abᵉ :
    preserves-add-Abᵉ (ab-Subgroup-Abᵉ Aᵉ Bᵉ) Aᵉ (map-inclusion-Subgroup-Abᵉ Aᵉ Bᵉ)
  preserves-add-inclusion-Subgroup-Abᵉ {xᵉ} {yᵉ} =
    preserves-mul-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ {xᵉ} {yᵉ}

  preserves-zero-inclusion-Subgroup-Abᵉ :
    preserves-zero-Abᵉ (ab-Subgroup-Abᵉ Aᵉ Bᵉ) Aᵉ (map-inclusion-Subgroup-Abᵉ Aᵉ Bᵉ)
  preserves-zero-inclusion-Subgroup-Abᵉ =
    preserves-unit-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  preserves-negatives-inclusion-Subgroup-Abᵉ :
    preserves-negatives-Abᵉ
      ( ab-Subgroup-Abᵉ Aᵉ Bᵉ)
      ( Aᵉ)
      ( map-inclusion-Subgroup-Abᵉ Aᵉ Bᵉ)
  preserves-negatives-inclusion-Subgroup-Abᵉ {xᵉ} =
    preserves-inverses-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ {xᵉ}

  hom-inclusion-Subgroup-Abᵉ : hom-Abᵉ (ab-Subgroup-Abᵉ Aᵉ Bᵉ) Aᵉ
  hom-inclusion-Subgroup-Abᵉ = hom-inclusion-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ
```

### Normal subgroups of an abelian group

```agda
Normal-Subgroup-Abᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : Abᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Normal-Subgroup-Abᵉ l2ᵉ Aᵉ = Normal-Subgroupᵉ l2ᵉ (group-Abᵉ Aᵉ)
```

## Properties

### Extensionality of the type of all subgroups of an abelian group

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  has-same-elements-Subgroup-Abᵉ :
    {l3ᵉ : Level} → Subgroup-Abᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Subgroup-Abᵉ =
    has-same-elements-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  extensionality-Subgroup-Abᵉ :
    (Cᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ) → (Bᵉ ＝ᵉ Cᵉ) ≃ᵉ has-same-elements-Subgroup-Abᵉ Cᵉ
  extensionality-Subgroup-Abᵉ =
    extensionality-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  refl-has-same-elements-Subgroup-Abᵉ : has-same-elements-Subgroup-Abᵉ Bᵉ
  refl-has-same-elements-Subgroup-Abᵉ =
    refl-has-same-elements-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  has-same-elements-eq-Subgroup-Abᵉ :
    (Cᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ) → (Bᵉ ＝ᵉ Cᵉ) → has-same-elements-Subgroup-Abᵉ Cᵉ
  has-same-elements-eq-Subgroup-Abᵉ =
    has-same-elements-eq-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ

  eq-has-same-elements-Subgroup-Abᵉ :
    (Cᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ) → has-same-elements-Subgroup-Abᵉ Cᵉ → (Bᵉ ＝ᵉ Cᵉ)
  eq-has-same-elements-Subgroup-Abᵉ =
    eq-has-same-elements-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ
```

### The containment relation of subgroups of abelian groups

```agda
leq-prop-Subgroup-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  Subgroup-Abᵉ l2ᵉ Aᵉ → Subgroup-Abᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-prop-Subgroup-Abᵉ Aᵉ = leq-prop-Subgroupᵉ (group-Abᵉ Aᵉ)

leq-Subgroup-Abᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  Subgroup-Abᵉ l2ᵉ Aᵉ → Subgroup-Abᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
leq-Subgroup-Abᵉ Aᵉ = leq-Subgroupᵉ (group-Abᵉ Aᵉ)

refl-leq-Subgroup-Abᵉ :
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  is-reflexive-Large-Relationᵉ (λ lᵉ → Subgroup-Abᵉ lᵉ Aᵉ) (leq-Subgroup-Abᵉ Aᵉ)
refl-leq-Subgroup-Abᵉ Aᵉ = refl-leq-Subgroupᵉ (group-Abᵉ Aᵉ)

transitive-leq-Subgroup-Abᵉ :
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  is-transitive-Large-Relationᵉ (λ lᵉ → Subgroup-Abᵉ lᵉ Aᵉ) (leq-Subgroup-Abᵉ Aᵉ)
transitive-leq-Subgroup-Abᵉ Aᵉ = transitive-leq-Subgroupᵉ (group-Abᵉ Aᵉ)

antisymmetric-leq-Subgroup-Abᵉ :
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  is-antisymmetric-Large-Relationᵉ (λ lᵉ → Subgroup-Abᵉ lᵉ Aᵉ) (leq-Subgroup-Abᵉ Aᵉ)
antisymmetric-leq-Subgroup-Abᵉ Aᵉ =
  antisymmetric-leq-Subgroupᵉ (group-Abᵉ Aᵉ)

Subgroup-Ab-Large-Preorderᵉ :
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
Subgroup-Ab-Large-Preorderᵉ Aᵉ =
  Subgroup-Large-Preorderᵉ (group-Abᵉ Aᵉ)

Subgroup-Ab-Preorderᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : Abᵉ l1ᵉ) →
  Preorderᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subgroup-Ab-Preorderᵉ l2ᵉ Aᵉ = Subgroup-Preorderᵉ l2ᵉ (group-Abᵉ Aᵉ)

Subgroup-Ab-Large-Posetᵉ :
  {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) →
  Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
Subgroup-Ab-Large-Posetᵉ Aᵉ = Subgroup-Large-Posetᵉ (group-Abᵉ Aᵉ)

Subgroup-Ab-Posetᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : Abᵉ l1ᵉ) →
  Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
Subgroup-Ab-Posetᵉ l2ᵉ Aᵉ = Subgroup-Posetᵉ l2ᵉ (group-Abᵉ Aᵉ)
```

### Every subgroup of an abelian group is normal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  is-normal-Subgroup-Abᵉ : is-normal-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ
  is-normal-Subgroup-Abᵉ xᵉ yᵉ =
    is-closed-under-eq-Subgroup-Ab'ᵉ Aᵉ Bᵉ
      ( is-in-subgroup-inclusion-Subgroup-Abᵉ Aᵉ Bᵉ yᵉ)
      ( is-identity-conjugation-Abᵉ Aᵉ xᵉ (inclusion-Subgroup-Abᵉ Aᵉ Bᵉ yᵉ))

  normal-subgroup-Subgroup-Abᵉ : Normal-Subgroup-Abᵉ l2ᵉ Aᵉ
  pr1ᵉ normal-subgroup-Subgroup-Abᵉ = Bᵉ
  pr2ᵉ normal-subgroup-Subgroup-Abᵉ = is-normal-Subgroup-Abᵉ

  closure-property-Subgroup-Abᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ yᵉ →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ (add-Abᵉ Aᵉ xᵉ zᵉ) →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ (add-Abᵉ Aᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) zᵉ)
  closure-property-Subgroup-Abᵉ =
    closure-property-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ)

  closure-property-Subgroup-Ab'ᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ yᵉ →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ (add-Abᵉ Aᵉ xᵉ zᵉ) →
    is-in-Subgroup-Abᵉ Aᵉ Bᵉ (add-Abᵉ Aᵉ xᵉ (add-Abᵉ Aᵉ yᵉ zᵉ))
  closure-property-Subgroup-Ab'ᵉ =
    closure-property-Normal-Subgroup'ᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ)

  conjugation-Subgroup-Abᵉ :
    type-Abᵉ Aᵉ → type-Subgroup-Abᵉ Aᵉ Bᵉ → type-Subgroup-Abᵉ Aᵉ Bᵉ
  conjugation-Subgroup-Abᵉ =
    conjugation-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ)

  conjugation-Subgroup-Ab'ᵉ :
    type-Abᵉ Aᵉ → type-Subgroup-Abᵉ Aᵉ Bᵉ → type-Subgroup-Abᵉ Aᵉ Bᵉ
  conjugation-Subgroup-Ab'ᵉ =
    conjugation-Normal-Subgroup'ᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ)
```

### Subgroups of abelian groups are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from a subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  sim-congruence-Subgroup-Abᵉ : (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ l2ᵉ
  sim-congruence-Subgroup-Abᵉ =
    sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  is-prop-sim-congruence-Subgroup-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → is-propᵉ (sim-congruence-Subgroup-Abᵉ xᵉ yᵉ)
  is-prop-sim-congruence-Subgroup-Abᵉ =
    is-prop-sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  prop-congruence-Subgroup-Abᵉ : (xᵉ yᵉ : type-Abᵉ Aᵉ) → Propᵉ l2ᵉ
  prop-congruence-Subgroup-Abᵉ =
    prop-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)
```

#### The left equivalence relation obtained from a subgroup

```agda
  left-equivalence-relation-congruence-Subgroup-Abᵉ :
    equivalence-relationᵉ l2ᵉ (type-Abᵉ Aᵉ)
  left-equivalence-relation-congruence-Subgroup-Abᵉ =
    left-equivalence-relation-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  left-sim-congruence-Subgroup-Abᵉ :
    type-Abᵉ Aᵉ → type-Abᵉ Aᵉ → UUᵉ l2ᵉ
  left-sim-congruence-Subgroup-Abᵉ =
    left-sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)
```

#### The left similarity relation of a subgroup relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-Subgroup-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    sim-congruence-Subgroup-Abᵉ xᵉ yᵉ →
    left-sim-congruence-Subgroup-Abᵉ xᵉ yᵉ
  left-sim-sim-congruence-Subgroup-Abᵉ =
    left-sim-sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  sim-left-sim-congruence-Subgroup-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    left-sim-congruence-Subgroup-Abᵉ xᵉ yᵉ →
    sim-congruence-Subgroup-Abᵉ xᵉ yᵉ
  sim-left-sim-congruence-Subgroup-Abᵉ =
    sim-left-sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-Subgroup-Abᵉ :
    is-reflexiveᵉ sim-congruence-Subgroup-Abᵉ
  refl-congruence-Subgroup-Abᵉ =
    refl-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  symmetric-congruence-Subgroup-Abᵉ :
    is-symmetricᵉ sim-congruence-Subgroup-Abᵉ
  symmetric-congruence-Subgroup-Abᵉ =
    symmetric-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  transitive-congruence-Subgroup-Abᵉ :
    is-transitiveᵉ sim-congruence-Subgroup-Abᵉ
  transitive-congruence-Subgroup-Abᵉ =
    transitive-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  equivalence-relation-congruence-Subgroup-Abᵉ :
    equivalence-relationᵉ l2ᵉ (type-Abᵉ Aᵉ)
  equivalence-relation-congruence-Subgroup-Abᵉ =
    equivalence-relation-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  relate-same-elements-left-sim-congruence-Subgroup-Abᵉ :
    relate-same-elements-equivalence-relationᵉ
      ( equivalence-relation-congruence-Subgroup-Abᵉ)
      ( left-equivalence-relation-congruence-Subgroup-Abᵉ)
  relate-same-elements-left-sim-congruence-Subgroup-Abᵉ =
    relate-same-elements-left-sim-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  add-congruence-Subgroup-Abᵉ :
    is-congruence-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( equivalence-relation-congruence-Subgroup-Abᵉ)
  add-congruence-Subgroup-Abᵉ =
    mul-congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  congruence-Subgroup-Abᵉ : congruence-Abᵉ l2ᵉ Aᵉ
  congruence-Subgroup-Abᵉ =
    congruence-Normal-Subgroupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  neg-congruence-Subgroup-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    sim-congruence-Subgroup-Abᵉ xᵉ yᵉ →
    sim-congruence-Subgroup-Abᵉ (neg-Abᵉ Aᵉ xᵉ) (neg-Abᵉ Aᵉ yᵉ)
  neg-congruence-Subgroup-Abᵉ =
    neg-congruence-Abᵉ Aᵉ congruence-Subgroup-Abᵉ
```

#### The subgroup obtained from a congruence relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ : congruence-Abᵉ l2ᵉ Aᵉ)
  where

  subset-congruence-Abᵉ : subset-Abᵉ l2ᵉ Aᵉ
  subset-congruence-Abᵉ = prop-congruence-Abᵉ Aᵉ Rᵉ (zero-Abᵉ Aᵉ)

  is-in-subset-congruence-Abᵉ : (type-Abᵉ Aᵉ) → UUᵉ l2ᵉ
  is-in-subset-congruence-Abᵉ =
    is-in-subset-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  contains-zero-subset-congruence-Abᵉ :
    contains-zero-subset-Abᵉ Aᵉ subset-congruence-Abᵉ
  contains-zero-subset-congruence-Abᵉ =
    contains-unit-subset-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  is-closed-under-addition-subset-congruence-Abᵉ :
    is-closed-under-addition-subset-Abᵉ Aᵉ subset-congruence-Abᵉ
  is-closed-under-addition-subset-congruence-Abᵉ =
    is-closed-under-multiplication-subset-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  is-closed-under-negatives-subset-congruence-Abᵉ :
    is-closed-under-negatives-subset-Abᵉ Aᵉ subset-congruence-Abᵉ
  is-closed-under-negatives-subset-congruence-Abᵉ =
    is-closed-under-inverses-subset-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  subgroup-congruence-Abᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ
  subgroup-congruence-Abᵉ = subgroup-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  is-normal-subgroup-congruence-Abᵉ :
    is-normal-Subgroupᵉ (group-Abᵉ Aᵉ) subgroup-congruence-Abᵉ
  is-normal-subgroup-congruence-Abᵉ =
    is-normal-subgroup-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ

  normal-subgroup-congruence-Abᵉ : Normal-Subgroupᵉ l2ᵉ (group-Abᵉ Aᵉ)
  normal-subgroup-congruence-Abᵉ =
    normal-subgroup-congruence-Groupᵉ (group-Abᵉ Aᵉ) Rᵉ
```

#### The subgroup obtained from the congruence relation of a subgroup `N` is `N` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ)
  where

  has-same-elements-subgroup-congruence-Abᵉ :
    has-same-elements-Subgroup-Abᵉ Aᵉ
      ( subgroup-congruence-Abᵉ Aᵉ
        ( congruence-Subgroup-Abᵉ Aᵉ Bᵉ))
      ( Bᵉ)
  has-same-elements-subgroup-congruence-Abᵉ =
    has-same-elements-normal-subgroup-congruence-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( normal-subgroup-Subgroup-Abᵉ Aᵉ Bᵉ)

  is-retraction-subgroup-congruence-Abᵉ :
    subgroup-congruence-Abᵉ Aᵉ (congruence-Subgroup-Abᵉ Aᵉ Bᵉ) ＝ᵉ Bᵉ
  is-retraction-subgroup-congruence-Abᵉ =
    eq-has-same-elements-Subgroup-Abᵉ Aᵉ
      ( subgroup-congruence-Abᵉ Aᵉ (congruence-Subgroup-Abᵉ Aᵉ Bᵉ))
      ( Bᵉ)
      ( has-same-elements-subgroup-congruence-Abᵉ)
```

#### The congruence relation of the subgroup obtained from a congruence relation `R` is `R` itself

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Rᵉ : congruence-Abᵉ l2ᵉ Aᵉ)
  where

  relate-same-elements-congruence-subgroup-congruence-Abᵉ :
    relate-same-elements-congruence-Abᵉ Aᵉ
      ( congruence-Subgroup-Abᵉ Aᵉ (subgroup-congruence-Abᵉ Aᵉ Rᵉ))
      ( Rᵉ)
  relate-same-elements-congruence-subgroup-congruence-Abᵉ =
    relate-same-elements-congruence-normal-subgroup-congruence-Groupᵉ
      ( group-Abᵉ Aᵉ)
      ( Rᵉ)

  is-section-subgroup-congruence-Abᵉ :
    congruence-Subgroup-Abᵉ Aᵉ (subgroup-congruence-Abᵉ Aᵉ Rᵉ) ＝ᵉ Rᵉ
  is-section-subgroup-congruence-Abᵉ =
    eq-relate-same-elements-congruence-Abᵉ Aᵉ
      ( congruence-Subgroup-Abᵉ Aᵉ (subgroup-congruence-Abᵉ Aᵉ Rᵉ))
      ( Rᵉ)
      ( relate-same-elements-congruence-subgroup-congruence-Abᵉ)
```

#### The equivalence of subgroups and congruence relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ)
  where

  is-equiv-congruence-Subgroup-Abᵉ :
    is-equivᵉ (congruence-Subgroup-Abᵉ {l1ᵉ} {l2ᵉ} Aᵉ)
  is-equiv-congruence-Subgroup-Abᵉ =
    is-equiv-is-invertibleᵉ
      ( subgroup-congruence-Abᵉ Aᵉ)
      ( is-section-subgroup-congruence-Abᵉ Aᵉ)
      ( is-retraction-subgroup-congruence-Abᵉ Aᵉ)

  equiv-congruence-Subgroup-Abᵉ :
    Subgroup-Abᵉ l2ᵉ Aᵉ ≃ᵉ congruence-Abᵉ l2ᵉ Aᵉ
  pr1ᵉ equiv-congruence-Subgroup-Abᵉ =
    congruence-Subgroup-Abᵉ Aᵉ
  pr2ᵉ equiv-congruence-Subgroup-Abᵉ =
    is-equiv-congruence-Subgroup-Abᵉ

  is-equiv-subgroup-congruence-Abᵉ :
    is-equivᵉ (subgroup-congruence-Abᵉ {l1ᵉ} {l2ᵉ} Aᵉ)
  is-equiv-subgroup-congruence-Abᵉ =
    is-equiv-is-invertibleᵉ
      ( congruence-Subgroup-Abᵉ Aᵉ)
      ( is-retraction-subgroup-congruence-Abᵉ Aᵉ)
      ( is-section-subgroup-congruence-Abᵉ Aᵉ)

  equiv-subgroup-congruence-Abᵉ :
    congruence-Abᵉ l2ᵉ Aᵉ ≃ᵉ Subgroup-Abᵉ l2ᵉ Aᵉ
  pr1ᵉ equiv-subgroup-congruence-Abᵉ =
    subgroup-congruence-Abᵉ Aᵉ
  pr2ᵉ equiv-subgroup-congruence-Abᵉ =
    is-equiv-subgroup-congruence-Abᵉ
```