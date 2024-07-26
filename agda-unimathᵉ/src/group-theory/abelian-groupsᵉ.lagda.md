# Abelian groups

```agda
module group-theory.abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-groupsᵉ
open import group-theory.commutative-monoidsᵉ
open import group-theory.commutator-subgroupsᵉ
open import group-theory.commutators-of-elements-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.nullifying-group-homomorphismsᵉ
open import group-theory.pullbacks-subgroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subgroups-generated-by-families-of-elements-groupsᵉ
open import group-theory.trivial-subgroupsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import structured-types.pointed-types-equipped-with-automorphismsᵉ
```

</details>

## Idea

**Abelianᵉ groups**ᵉ areᵉ [groups](group-theory.groups.mdᵉ) ofᵉ whichᵉ theᵉ groupᵉ
operationᵉ isᵉ commutative.ᵉ Itᵉ isᵉ commonᵉ to writeᵉ abelianᵉ groupsᵉ additively,ᵉ i.e.,ᵉ
to writeᵉ

```text
  xᵉ +ᵉ yᵉ
```

forᵉ theᵉ groupᵉ operationᵉ ofᵉ anᵉ abelianᵉ group,ᵉ `0`ᵉ forᵉ itsᵉ unitᵉ element,ᵉ andᵉ `-x`ᵉ
forᵉ theᵉ inverseᵉ ofᵉ `x`.ᵉ

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Groupᵉ : {lᵉ : Level} → Groupᵉ lᵉ → Propᵉ lᵉ
is-abelian-prop-Groupᵉ Gᵉ =
  Π-Propᵉ
    ( type-Groupᵉ Gᵉ)
    ( λ xᵉ →
      Π-Propᵉ
        ( type-Groupᵉ Gᵉ)
        ( λ yᵉ →
          Id-Propᵉ (set-Groupᵉ Gᵉ) (mul-Groupᵉ Gᵉ xᵉ yᵉ) (mul-Groupᵉ Gᵉ yᵉ xᵉ)))

is-abelian-Groupᵉ : {lᵉ : Level} → Groupᵉ lᵉ → UUᵉ lᵉ
is-abelian-Groupᵉ Gᵉ = type-Propᵉ (is-abelian-prop-Groupᵉ Gᵉ)

is-prop-is-abelian-Groupᵉ :
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ) → is-propᵉ (is-abelian-Groupᵉ Gᵉ)
is-prop-is-abelian-Groupᵉ Gᵉ =
  is-prop-type-Propᵉ (is-abelian-prop-Groupᵉ Gᵉ)
```

### The type of abelian groups

```agda
Abᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Abᵉ lᵉ = Σᵉ (Groupᵉ lᵉ) is-abelian-Groupᵉ

module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  group-Abᵉ : Groupᵉ lᵉ
  group-Abᵉ = pr1ᵉ Aᵉ

  set-Abᵉ : Setᵉ lᵉ
  set-Abᵉ = set-Groupᵉ group-Abᵉ

  type-Abᵉ : UUᵉ lᵉ
  type-Abᵉ = type-Groupᵉ group-Abᵉ

  is-set-type-Abᵉ : is-setᵉ type-Abᵉ
  is-set-type-Abᵉ = is-set-type-Groupᵉ group-Abᵉ

  has-associative-add-Abᵉ : has-associative-mul-Setᵉ set-Abᵉ
  has-associative-add-Abᵉ = has-associative-mul-Groupᵉ group-Abᵉ

  add-Abᵉ : type-Abᵉ → type-Abᵉ → type-Abᵉ
  add-Abᵉ = mul-Groupᵉ group-Abᵉ

  add-Ab'ᵉ : type-Abᵉ → type-Abᵉ → type-Abᵉ
  add-Ab'ᵉ = mul-Group'ᵉ group-Abᵉ

  ap-add-Abᵉ :
    {xᵉ yᵉ x'ᵉ y'ᵉ : type-Abᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → add-Abᵉ xᵉ yᵉ ＝ᵉ add-Abᵉ x'ᵉ y'ᵉ
  ap-add-Abᵉ pᵉ qᵉ = ap-binaryᵉ add-Abᵉ pᵉ qᵉ

  associative-add-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ) → add-Abᵉ (add-Abᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Abᵉ xᵉ (add-Abᵉ yᵉ zᵉ)
  associative-add-Abᵉ = associative-mul-Groupᵉ group-Abᵉ

  semigroup-Abᵉ : Semigroupᵉ lᵉ
  semigroup-Abᵉ = semigroup-Groupᵉ group-Abᵉ

  is-group-Abᵉ : is-group-Semigroupᵉ semigroup-Abᵉ
  is-group-Abᵉ = is-group-Groupᵉ group-Abᵉ

  has-zero-Abᵉ : is-unital-Semigroupᵉ semigroup-Abᵉ
  has-zero-Abᵉ = is-unital-Groupᵉ group-Abᵉ

  zero-Abᵉ : type-Abᵉ
  zero-Abᵉ = unit-Groupᵉ group-Abᵉ

  is-zero-Abᵉ : type-Abᵉ → UUᵉ lᵉ
  is-zero-Abᵉ = is-unit-Groupᵉ group-Abᵉ

  is-zero-Ab'ᵉ : type-Abᵉ → UUᵉ lᵉ
  is-zero-Ab'ᵉ = is-unit-Group'ᵉ group-Abᵉ

  is-prop-is-zero-Abᵉ : (xᵉ : type-Abᵉ) → is-propᵉ (is-zero-Abᵉ xᵉ)
  is-prop-is-zero-Abᵉ = is-prop-is-unit-Groupᵉ group-Abᵉ

  is-zero-prop-Abᵉ : type-Abᵉ → Propᵉ lᵉ
  is-zero-prop-Abᵉ = is-unit-prop-Groupᵉ group-Abᵉ

  left-unit-law-add-Abᵉ : (xᵉ : type-Abᵉ) → add-Abᵉ zero-Abᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Abᵉ = left-unit-law-mul-Groupᵉ group-Abᵉ

  right-unit-law-add-Abᵉ : (xᵉ : type-Abᵉ) → add-Abᵉ xᵉ zero-Abᵉ ＝ᵉ xᵉ
  right-unit-law-add-Abᵉ = right-unit-law-mul-Groupᵉ group-Abᵉ

  has-negatives-Abᵉ : is-group-is-unital-Semigroupᵉ semigroup-Abᵉ has-zero-Abᵉ
  has-negatives-Abᵉ = has-inverses-Groupᵉ group-Abᵉ

  neg-Abᵉ : type-Abᵉ → type-Abᵉ
  neg-Abᵉ = inv-Groupᵉ group-Abᵉ

  left-inverse-law-add-Abᵉ :
    (xᵉ : type-Abᵉ) → add-Abᵉ (neg-Abᵉ xᵉ) xᵉ ＝ᵉ zero-Abᵉ
  left-inverse-law-add-Abᵉ = left-inverse-law-mul-Groupᵉ group-Abᵉ

  right-inverse-law-add-Abᵉ :
    (xᵉ : type-Abᵉ) → add-Abᵉ xᵉ (neg-Abᵉ xᵉ) ＝ᵉ zero-Abᵉ
  right-inverse-law-add-Abᵉ = right-inverse-law-mul-Groupᵉ group-Abᵉ

  commutative-add-Abᵉ : (xᵉ yᵉ : type-Abᵉ) → Idᵉ (add-Abᵉ xᵉ yᵉ) (add-Abᵉ yᵉ xᵉ)
  commutative-add-Abᵉ = pr2ᵉ Aᵉ

  interchange-add-add-Abᵉ :
    (aᵉ bᵉ cᵉ dᵉ : type-Abᵉ) →
    add-Abᵉ (add-Abᵉ aᵉ bᵉ) (add-Abᵉ cᵉ dᵉ) ＝ᵉ add-Abᵉ (add-Abᵉ aᵉ cᵉ) (add-Abᵉ bᵉ dᵉ)
  interchange-add-add-Abᵉ =
    interchange-law-commutative-and-associativeᵉ
      add-Abᵉ
      commutative-add-Abᵉ
      associative-add-Abᵉ

  right-swap-add-Abᵉ :
    (aᵉ bᵉ cᵉ : type-Abᵉ) → add-Abᵉ (add-Abᵉ aᵉ bᵉ) cᵉ ＝ᵉ add-Abᵉ (add-Abᵉ aᵉ cᵉ) bᵉ
  right-swap-add-Abᵉ aᵉ bᵉ cᵉ =
    ( associative-add-Abᵉ aᵉ bᵉ cᵉ) ∙ᵉ
    ( apᵉ (add-Abᵉ aᵉ) (commutative-add-Abᵉ bᵉ cᵉ)) ∙ᵉ
    ( invᵉ (associative-add-Abᵉ aᵉ cᵉ bᵉ))

  left-swap-add-Abᵉ :
    (aᵉ bᵉ cᵉ : type-Abᵉ) → add-Abᵉ aᵉ (add-Abᵉ bᵉ cᵉ) ＝ᵉ add-Abᵉ bᵉ (add-Abᵉ aᵉ cᵉ)
  left-swap-add-Abᵉ aᵉ bᵉ cᵉ =
    ( invᵉ (associative-add-Abᵉ aᵉ bᵉ cᵉ)) ∙ᵉ
    ( apᵉ (add-Ab'ᵉ cᵉ) (commutative-add-Abᵉ aᵉ bᵉ)) ∙ᵉ
    ( associative-add-Abᵉ bᵉ aᵉ cᵉ)

  distributive-neg-add-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ) →
    neg-Abᵉ (add-Abᵉ xᵉ yᵉ) ＝ᵉ add-Abᵉ (neg-Abᵉ xᵉ) (neg-Abᵉ yᵉ)
  distributive-neg-add-Abᵉ xᵉ yᵉ =
    ( distributive-inv-mul-Groupᵉ group-Abᵉ) ∙ᵉ
    ( commutative-add-Abᵉ (neg-Abᵉ yᵉ) (neg-Abᵉ xᵉ))

  neg-neg-Abᵉ : (xᵉ : type-Abᵉ) → neg-Abᵉ (neg-Abᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Abᵉ = inv-inv-Groupᵉ group-Abᵉ

  neg-zero-Abᵉ : neg-Abᵉ zero-Abᵉ ＝ᵉ zero-Abᵉ
  neg-zero-Abᵉ = inv-unit-Groupᵉ group-Abᵉ

  transpose-eq-neg-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ} → neg-Abᵉ xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ neg-Abᵉ yᵉ
  transpose-eq-neg-Abᵉ = transpose-eq-inv-Groupᵉ group-Abᵉ

  transpose-eq-neg-Ab'ᵉ :
    {xᵉ yᵉ : type-Abᵉ} → xᵉ ＝ᵉ neg-Abᵉ yᵉ → neg-Abᵉ xᵉ ＝ᵉ yᵉ
  transpose-eq-neg-Ab'ᵉ = transpose-eq-inv-Group'ᵉ group-Abᵉ
```

### The underlying commutative monoid of an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  monoid-Abᵉ : Monoidᵉ lᵉ
  pr1ᵉ monoid-Abᵉ = semigroup-Abᵉ Aᵉ
  pr1ᵉ (pr2ᵉ monoid-Abᵉ) = zero-Abᵉ Aᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ monoid-Abᵉ)) = left-unit-law-add-Abᵉ Aᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ monoid-Abᵉ)) = right-unit-law-add-Abᵉ Aᵉ

  commutative-monoid-Abᵉ : Commutative-Monoidᵉ lᵉ
  pr1ᵉ commutative-monoid-Abᵉ = monoid-Abᵉ
  pr2ᵉ commutative-monoid-Abᵉ = commutative-add-Abᵉ Aᵉ
```

### The structure of an abelian group

```agda
structure-abelian-groupᵉ :
  {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
structure-abelian-groupᵉ Xᵉ =
  Σᵉ (structure-groupᵉ Xᵉ) (λ pᵉ → is-abelian-Groupᵉ (group-structure-groupᵉ Xᵉ pᵉ))

abelian-group-structure-abelian-groupᵉ :
  {l1ᵉ : Level} → (Xᵉ : UUᵉ l1ᵉ) → structure-abelian-groupᵉ Xᵉ → Abᵉ l1ᵉ
pr1ᵉ (abelian-group-structure-abelian-groupᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) =
  group-structure-groupᵉ Xᵉ pᵉ
pr2ᵉ (abelian-group-structure-abelian-groupᵉ Xᵉ (pᵉ ,ᵉ qᵉ)) = qᵉ
```

### Conjugation in an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  equiv-conjugation-Abᵉ : (xᵉ : type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ ≃ᵉ type-Abᵉ Aᵉ
  equiv-conjugation-Abᵉ = equiv-conjugation-Groupᵉ (group-Abᵉ Aᵉ)

  conjugation-Abᵉ : (xᵉ : type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  conjugation-Abᵉ = conjugation-Groupᵉ (group-Abᵉ Aᵉ)

  equiv-conjugation-Ab'ᵉ : (xᵉ : type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ ≃ᵉ type-Abᵉ Aᵉ
  equiv-conjugation-Ab'ᵉ = equiv-conjugation-Group'ᵉ (group-Abᵉ Aᵉ)

  conjugation-Ab'ᵉ : (xᵉ : type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  conjugation-Ab'ᵉ = conjugation-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Commutators in an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  commutator-Abᵉ : type-Abᵉ Aᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  commutator-Abᵉ xᵉ yᵉ = commutator-Groupᵉ (group-Abᵉ Aᵉ) xᵉ yᵉ
```

### The commutator subgroup of an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  family-of-commutators-Abᵉ : type-Abᵉ Aᵉ ×ᵉ type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  family-of-commutators-Abᵉ = family-of-commutators-Groupᵉ (group-Abᵉ Aᵉ)

  commutator-subgroup-Abᵉ : Subgroupᵉ lᵉ (group-Abᵉ Aᵉ)
  commutator-subgroup-Abᵉ = commutator-subgroup-Groupᵉ (group-Abᵉ Aᵉ)
```

### Any abelian group element yields a type equipped with an automorphism

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ) (aᵉ : type-Abᵉ Aᵉ)
  where

  pointed-type-with-aut-Abᵉ : Pointed-Type-With-Autᵉ lᵉ
  pointed-type-with-aut-Abᵉ = pointed-type-with-aut-Groupᵉ (group-Abᵉ Aᵉ) aᵉ
```

## Properties

### Addition on an abelian group is a binary equivalence

#### Addition on the left is an equivalence

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  left-subtraction-Abᵉ : type-Abᵉ Aᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  left-subtraction-Abᵉ = left-div-Groupᵉ (group-Abᵉ Aᵉ)

  ap-left-subtraction-Abᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Abᵉ Aᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    left-subtraction-Abᵉ xᵉ yᵉ ＝ᵉ left-subtraction-Abᵉ x'ᵉ y'ᵉ
  ap-left-subtraction-Abᵉ = ap-left-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-section-left-subtraction-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → (add-Abᵉ Aᵉ xᵉ ∘ᵉ left-subtraction-Abᵉ xᵉ) ~ᵉ idᵉ
  is-section-left-subtraction-Abᵉ = is-section-left-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-retraction-left-subtraction-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → (left-subtraction-Abᵉ xᵉ ∘ᵉ add-Abᵉ Aᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-left-subtraction-Abᵉ = is-retraction-left-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-equiv-add-Abᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-equivᵉ (add-Abᵉ Aᵉ xᵉ)
  is-equiv-add-Abᵉ = is-equiv-mul-Groupᵉ (group-Abᵉ Aᵉ)

  equiv-add-Abᵉ : type-Abᵉ Aᵉ → (type-Abᵉ Aᵉ ≃ᵉ type-Abᵉ Aᵉ)
  equiv-add-Abᵉ = equiv-mul-Groupᵉ (group-Abᵉ Aᵉ)
```

#### Addition on the right is an equivalence

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  right-subtraction-Abᵉ : type-Abᵉ Aᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  right-subtraction-Abᵉ = right-div-Groupᵉ (group-Abᵉ Aᵉ)

  ap-right-subtraction-Abᵉ :
    {xᵉ x'ᵉ yᵉ y'ᵉ : type-Abᵉ Aᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ →
    right-subtraction-Abᵉ xᵉ yᵉ ＝ᵉ right-subtraction-Abᵉ x'ᵉ y'ᵉ
  ap-right-subtraction-Abᵉ = ap-right-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-section-right-subtraction-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) →
    (add-Ab'ᵉ Aᵉ xᵉ ∘ᵉ (λ yᵉ → right-subtraction-Abᵉ yᵉ xᵉ)) ~ᵉ idᵉ
  is-section-right-subtraction-Abᵉ = is-section-right-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-retraction-right-subtraction-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) →
    ((λ yᵉ → right-subtraction-Abᵉ yᵉ xᵉ) ∘ᵉ add-Ab'ᵉ Aᵉ xᵉ) ~ᵉ idᵉ
  is-retraction-right-subtraction-Abᵉ =
    is-retraction-right-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-equiv-add-Ab'ᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-equivᵉ (add-Ab'ᵉ Aᵉ xᵉ)
  is-equiv-add-Ab'ᵉ = is-equiv-mul-Group'ᵉ (group-Abᵉ Aᵉ)

  equiv-add-Ab'ᵉ : type-Abᵉ Aᵉ → (type-Abᵉ Aᵉ ≃ᵉ type-Abᵉ Aᵉ)
  equiv-add-Ab'ᵉ = equiv-mul-Group'ᵉ (group-Abᵉ Aᵉ)
```

#### Addition on an abelian group is a binary equivalence

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-binary-equiv-add-Abᵉ : is-binary-equivᵉ (add-Abᵉ Aᵉ)
  is-binary-equiv-add-Abᵉ = is-binary-equiv-mul-Groupᵉ (group-Abᵉ Aᵉ)
```

### Addition on an abelian group is a binary embedding

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-binary-emb-add-Abᵉ : is-binary-embᵉ (add-Abᵉ Aᵉ)
  is-binary-emb-add-Abᵉ = is-binary-emb-mul-Groupᵉ (group-Abᵉ Aᵉ)

  is-emb-add-Abᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-embᵉ (add-Abᵉ Aᵉ xᵉ)
  is-emb-add-Abᵉ = is-emb-mul-Groupᵉ (group-Abᵉ Aᵉ)

  is-emb-add-Ab'ᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-embᵉ (add-Ab'ᵉ Aᵉ xᵉ)
  is-emb-add-Ab'ᵉ = is-emb-mul-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Addition on an abelian group is pointwise injective from both sides

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-injective-add-Abᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-injectiveᵉ (add-Abᵉ Aᵉ xᵉ)
  is-injective-add-Abᵉ = is-injective-mul-Groupᵉ (group-Abᵉ Aᵉ)

  is-injective-add-Ab'ᵉ : (xᵉ : type-Abᵉ Aᵉ) → is-injectiveᵉ (add-Ab'ᵉ Aᵉ xᵉ)
  is-injective-add-Ab'ᵉ = is-injective-mul-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Transposing identifications in abelian groups

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  transpose-eq-add-Abᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    Idᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) zᵉ → Idᵉ xᵉ (add-Abᵉ Aᵉ zᵉ (neg-Abᵉ Aᵉ yᵉ))
  transpose-eq-add-Abᵉ = transpose-eq-mul-Groupᵉ (group-Abᵉ Aᵉ)

  inv-transpose-eq-add-Abᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    Idᵉ xᵉ (add-Abᵉ Aᵉ zᵉ (neg-Abᵉ Aᵉ yᵉ)) → add-Abᵉ Aᵉ xᵉ yᵉ ＝ᵉ zᵉ
  inv-transpose-eq-add-Abᵉ = inv-transpose-eq-mul-Groupᵉ (group-Abᵉ Aᵉ)

  transpose-eq-add-Ab'ᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    Idᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) zᵉ → Idᵉ yᵉ (add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) zᵉ)
  transpose-eq-add-Ab'ᵉ = transpose-eq-mul-Group'ᵉ (group-Abᵉ Aᵉ)

  inv-transpose-eq-add-Ab'ᵉ :
    {xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ} →
    Idᵉ yᵉ (add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) zᵉ) → Idᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) zᵉ
  inv-transpose-eq-add-Ab'ᵉ = inv-transpose-eq-mul-Group'ᵉ (group-Abᵉ Aᵉ)

  double-transpose-eq-add-Abᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Abᵉ Aᵉ} →
    add-Abᵉ Aᵉ yᵉ wᵉ ＝ᵉ add-Abᵉ Aᵉ xᵉ zᵉ →
    left-subtraction-Abᵉ Aᵉ xᵉ yᵉ ＝ᵉ right-subtraction-Abᵉ Aᵉ zᵉ wᵉ
  double-transpose-eq-add-Abᵉ =
    double-transpose-eq-mul-Groupᵉ (group-Abᵉ Aᵉ)

  double-transpose-eq-add-Ab'ᵉ :
    {xᵉ yᵉ zᵉ wᵉ : type-Abᵉ Aᵉ} →
    add-Abᵉ Aᵉ zᵉ xᵉ ＝ᵉ add-Abᵉ Aᵉ wᵉ yᵉ →
    right-subtraction-Abᵉ Aᵉ xᵉ yᵉ ＝ᵉ left-subtraction-Abᵉ Aᵉ zᵉ wᵉ
  double-transpose-eq-add-Ab'ᵉ =
    double-transpose-eq-mul-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Any idempotent element in an abelian group is zero

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-idempotent-Abᵉ : type-Abᵉ Aᵉ → UUᵉ lᵉ
  is-idempotent-Abᵉ = is-idempotent-Groupᵉ (group-Abᵉ Aᵉ)

  is-zero-is-idempotent-Abᵉ :
    {xᵉ : type-Abᵉ Aᵉ} → is-idempotent-Abᵉ xᵉ → is-zero-Abᵉ Aᵉ xᵉ
  is-zero-is-idempotent-Abᵉ = is-unit-is-idempotent-Groupᵉ (group-Abᵉ Aᵉ)
```

### Taking negatives of elements of an abelian group is an equivalence

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-equiv-neg-Abᵉ : is-equivᵉ (neg-Abᵉ Aᵉ)
  is-equiv-neg-Abᵉ = is-equiv-inv-Groupᵉ (group-Abᵉ Aᵉ)

  equiv-equiv-neg-Abᵉ : type-Abᵉ Aᵉ ≃ᵉ type-Abᵉ Aᵉ
  equiv-equiv-neg-Abᵉ = equiv-equiv-inv-Groupᵉ (group-Abᵉ Aᵉ)
```

### Two elements `x` and `y` are equal iff `-x + y = 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  eq-is-zero-left-subtraction-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    is-zero-Abᵉ Aᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-is-zero-left-subtraction-Abᵉ =
    eq-is-unit-left-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-zero-left-subtraction-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    xᵉ ＝ᵉ yᵉ → is-zero-Abᵉ Aᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ)
  is-zero-left-subtraction-Abᵉ = is-unit-left-div-eq-Groupᵉ (group-Abᵉ Aᵉ)
```

### Two elements `x` and `y` are equal iff `x - y = 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  eq-is-zero-right-subtraction-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    is-zero-Abᵉ Aᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-is-zero-right-subtraction-Abᵉ =
    eq-is-unit-right-div-Groupᵉ (group-Abᵉ Aᵉ)

  is-zero-right-subtraction-eq-Abᵉ :
    {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    xᵉ ＝ᵉ yᵉ → is-zero-Abᵉ Aᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ)
  is-zero-right-subtraction-eq-Abᵉ =
    is-unit-right-div-eq-Groupᵉ (group-Abᵉ Aᵉ)
```

### The negative of `-x + y` is `-y + x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  neg-left-subtraction-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    neg-Abᵉ Aᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ left-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  neg-left-subtraction-Abᵉ = inv-left-div-Groupᵉ (group-Abᵉ Aᵉ)
```

### The negative of `x - y` is `y - x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  neg-right-subtraction-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    neg-Abᵉ Aᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ right-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  neg-right-subtraction-Abᵉ = inv-right-div-Groupᵉ (group-Abᵉ Aᵉ)
```

### The sum of `-x + y` and `-y + z` is `-x + z`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  add-left-subtraction-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ) (left-subtraction-Abᵉ Aᵉ yᵉ zᵉ) ＝ᵉ
    left-subtraction-Abᵉ Aᵉ xᵉ zᵉ
  add-left-subtraction-Abᵉ = mul-left-div-Groupᵉ (group-Abᵉ Aᵉ)
```

### The sum of `x - y` and `y - z` is `x - z`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  add-right-subtraction-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ) (right-subtraction-Abᵉ Aᵉ yᵉ zᵉ) ＝ᵉ
    right-subtraction-Abᵉ Aᵉ xᵉ zᵉ
  add-right-subtraction-Abᵉ = mul-right-div-Groupᵉ (group-Abᵉ Aᵉ)
```

### Conjugation is the identity function

**Proof:**ᵉ Considerᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ anᵉ abelianᵉ group.ᵉ Thenᵉ

```text
  (xᵉ +ᵉ yᵉ) -ᵉ xᵉ ＝ᵉ (yᵉ +ᵉ xᵉ) -ᵉ xᵉ ＝ᵉ y,ᵉ
```

where theᵉ lastᵉ stepᵉ holdsᵉ atᵉ onceᵉ sinceᵉ theᵉ functionᵉ `ᵉ_ -ᵉ x`ᵉ isᵉ aᵉ
[retraction](foundation-core.retractions.mdᵉ) ofᵉ theᵉ functionᵉ `ᵉ_ +ᵉ x`.ᵉ

Noteᵉ thatᵉ thisᵉ isᵉ aᵉ fairlyᵉ commonᵉ wayᵉ to makeᵉ quickᵉ calculations.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-identity-conjugation-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → conjugation-Abᵉ Aᵉ xᵉ ~ᵉ idᵉ
  is-identity-conjugation-Abᵉ xᵉ yᵉ =
    ( apᵉ (add-Ab'ᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ)) (commutative-add-Abᵉ Aᵉ xᵉ yᵉ)) ∙ᵉ
    ( is-retraction-right-subtraction-Abᵉ Aᵉ xᵉ yᵉ)
```

### Laws for conjugation and addition

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  htpy-conjugation-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) →
    conjugation-Ab'ᵉ Aᵉ xᵉ ~ᵉ conjugation-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ)
  htpy-conjugation-Abᵉ = htpy-conjugation-Groupᵉ (group-Abᵉ Aᵉ)

  htpy-conjugation-Ab'ᵉ :
    (xᵉ : type-Abᵉ Aᵉ) →
    conjugation-Abᵉ Aᵉ xᵉ ~ᵉ conjugation-Ab'ᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ)
  htpy-conjugation-Ab'ᵉ = htpy-conjugation-Group'ᵉ (group-Abᵉ Aᵉ)

  conjugation-zero-Abᵉ :
    (xᵉ : type-Abᵉ Aᵉ) → conjugation-Abᵉ Aᵉ xᵉ (zero-Abᵉ Aᵉ) ＝ᵉ zero-Abᵉ Aᵉ
  conjugation-zero-Abᵉ = conjugation-unit-Groupᵉ (group-Abᵉ Aᵉ)

  right-conjugation-law-add-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ (neg-Abᵉ Aᵉ xᵉ) (conjugation-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    right-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  right-conjugation-law-add-Abᵉ =
    right-conjugation-law-mul-Groupᵉ (group-Abᵉ Aᵉ)

  right-conjugation-law-add-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ xᵉ (conjugation-Ab'ᵉ Aᵉ xᵉ yᵉ) ＝ᵉ add-Abᵉ Aᵉ yᵉ xᵉ
  right-conjugation-law-add-Ab'ᵉ =
    right-conjugation-law-mul-Group'ᵉ (group-Abᵉ Aᵉ)

  left-conjugation-law-add-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ (conjugation-Abᵉ Aᵉ xᵉ yᵉ) xᵉ ＝ᵉ add-Abᵉ Aᵉ xᵉ yᵉ
  left-conjugation-law-add-Abᵉ =
    left-conjugation-law-mul-Groupᵉ (group-Abᵉ Aᵉ)

  left-conjugation-law-add-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    add-Abᵉ Aᵉ (conjugation-Ab'ᵉ Aᵉ xᵉ yᵉ) (neg-Abᵉ Aᵉ xᵉ) ＝ᵉ
    left-subtraction-Abᵉ Aᵉ xᵉ yᵉ
  left-conjugation-law-add-Ab'ᵉ =
    left-conjugation-law-mul-Group'ᵉ (group-Abᵉ Aᵉ)

  distributive-conjugation-add-Abᵉ :
    (xᵉ yᵉ zᵉ : type-Abᵉ Aᵉ) →
    conjugation-Abᵉ Aᵉ xᵉ (add-Abᵉ Aᵉ yᵉ zᵉ) ＝ᵉ
    add-Abᵉ Aᵉ (conjugation-Abᵉ Aᵉ xᵉ yᵉ) (conjugation-Abᵉ Aᵉ xᵉ zᵉ)
  distributive-conjugation-add-Abᵉ =
    distributive-conjugation-mul-Groupᵉ (group-Abᵉ Aᵉ)

  conjugation-neg-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Abᵉ Aᵉ xᵉ (neg-Abᵉ Aᵉ yᵉ) ＝ᵉ neg-Abᵉ Aᵉ (conjugation-Abᵉ Aᵉ xᵉ yᵉ)
  conjugation-neg-Abᵉ = conjugation-inv-Groupᵉ (group-Abᵉ Aᵉ)

  conjugation-neg-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Ab'ᵉ Aᵉ xᵉ (neg-Abᵉ Aᵉ yᵉ) ＝ᵉ
    neg-Abᵉ Aᵉ (conjugation-Ab'ᵉ Aᵉ xᵉ yᵉ)
  conjugation-neg-Ab'ᵉ = conjugation-inv-Group'ᵉ (group-Abᵉ Aᵉ)

  conjugation-left-subtraction-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Abᵉ Aᵉ xᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    right-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  conjugation-left-subtraction-Abᵉ =
    conjugation-left-div-Groupᵉ (group-Abᵉ Aᵉ)

  conjugation-left-subtraction-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Abᵉ Aᵉ yᵉ (left-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    right-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  conjugation-left-subtraction-Ab'ᵉ =
    conjugation-left-div-Group'ᵉ (group-Abᵉ Aᵉ)

  conjugation-right-subtraction-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Ab'ᵉ Aᵉ yᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    left-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  conjugation-right-subtraction-Abᵉ =
    conjugation-right-div-Groupᵉ (group-Abᵉ Aᵉ)

  conjugation-right-subtraction-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    conjugation-Ab'ᵉ Aᵉ xᵉ (right-subtraction-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    left-subtraction-Abᵉ Aᵉ yᵉ xᵉ
  conjugation-right-subtraction-Ab'ᵉ =
    conjugation-right-div-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  add-list-Abᵉ : listᵉ (type-Abᵉ Aᵉ) → type-Abᵉ Aᵉ
  add-list-Abᵉ = mul-list-Groupᵉ (group-Abᵉ Aᵉ)

  preserves-concat-add-list-Abᵉ :
    (l1ᵉ l2ᵉ : listᵉ (type-Abᵉ Aᵉ)) →
    Idᵉ
      ( add-list-Abᵉ (concat-listᵉ l1ᵉ l2ᵉ))
      ( add-Abᵉ Aᵉ (add-list-Abᵉ l1ᵉ) (add-list-Abᵉ l2ᵉ))
  preserves-concat-add-list-Abᵉ =
    preserves-concat-mul-list-Groupᵉ (group-Abᵉ Aᵉ)
```

### A group is abelian if and only if every element is central

**Proof:**ᵉ Theseᵉ twoᵉ conditionsᵉ areᵉ theᵉ sameᵉ onᵉ theᵉ nose.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-abelian-every-element-central-Groupᵉ :
    ((xᵉ : type-Groupᵉ Gᵉ) → is-central-element-Groupᵉ Gᵉ xᵉ) → is-abelian-Groupᵉ Gᵉ
  is-abelian-every-element-central-Groupᵉ = idᵉ

  every-element-central-is-abelian-Groupᵉ :
    is-abelian-Groupᵉ Gᵉ → ((xᵉ : type-Groupᵉ Gᵉ) → is-central-element-Groupᵉ Gᵉ xᵉ)
  every-element-central-is-abelian-Groupᵉ = idᵉ
```

### A group is abelian if and only if every commutator is equal to the unit

**Proof:**ᵉ Forᵉ anyᵉ twoᵉ elementsᵉ `u`ᵉ andᵉ `v`ᵉ in aᵉ groupᵉ weᵉ haveᵉ theᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (uv⁻¹ᵉ ＝ᵉ 1ᵉ) ↔ᵉ (uᵉ ＝ᵉ v).ᵉ
```

Sinceᵉ theᵉ [commutator](group-theory.commutators-of-elements-groups.mdᵉ) ofᵉ `x`ᵉ
andᵉ `y`ᵉ isᵉ definedᵉ asᵉ `[x,yᵉ] :=ᵉ (xy)(yx)⁻¹`,ᵉ weᵉ seeᵉ thatᵉ theᵉ claimᵉ isᵉ aᵉ directᵉ
consequenceᵉ ofᵉ thisᵉ logicalᵉ equivalence.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-abelian-is-unit-commutator-Groupᵉ :
    ((xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-unit-Groupᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)) →
    is-abelian-Groupᵉ Gᵉ
  is-abelian-is-unit-commutator-Groupᵉ Hᵉ xᵉ yᵉ =
    eq-is-unit-right-div-Groupᵉ Gᵉ (Hᵉ xᵉ yᵉ)

  is-abelian-is-unit-commutator-Group'ᵉ :
    ((xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-unit-Group'ᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)) →
    is-abelian-Groupᵉ Gᵉ
  is-abelian-is-unit-commutator-Group'ᵉ Hᵉ xᵉ yᵉ =
    eq-is-unit-right-div-Groupᵉ Gᵉ (invᵉ (Hᵉ xᵉ yᵉ))

  is-unit-commutator-is-abelian-Groupᵉ :
    is-abelian-Groupᵉ Gᵉ →
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-unit-Groupᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)
  is-unit-commutator-is-abelian-Groupᵉ Hᵉ xᵉ yᵉ =
    is-unit-right-div-eq-Groupᵉ Gᵉ (Hᵉ xᵉ yᵉ)

  is-unit-commutator-is-abelian-Group'ᵉ :
    is-abelian-Groupᵉ Gᵉ →
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-unit-Group'ᵉ Gᵉ (commutator-Groupᵉ Gᵉ xᵉ yᵉ)
  is-unit-commutator-is-abelian-Group'ᵉ Hᵉ xᵉ yᵉ =
    invᵉ (is-unit-right-div-eq-Groupᵉ Gᵉ (Hᵉ xᵉ yᵉ))

module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-zero-commutator-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → is-zero-Abᵉ Aᵉ (commutator-Abᵉ Aᵉ xᵉ yᵉ)
  is-zero-commutator-Abᵉ =
    is-unit-commutator-is-abelian-Groupᵉ (group-Abᵉ Aᵉ) (commutative-add-Abᵉ Aᵉ)

  is-zero-commutator-Ab'ᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → is-zero-Ab'ᵉ Aᵉ (commutator-Abᵉ Aᵉ xᵉ yᵉ)
  is-zero-commutator-Ab'ᵉ =
    is-unit-commutator-is-abelian-Group'ᵉ (group-Abᵉ Aᵉ) (commutative-add-Abᵉ Aᵉ)
```

### A group is abelian if and only if its commutator subgroup is trivial

**Proof:**ᵉ Weᵉ sawᵉ aboveᵉ thatᵉ aᵉ groupᵉ isᵉ abelianᵉ ifᵉ andᵉ onlyᵉ ifᵉ everyᵉ commutatorᵉ
isᵉ theᵉ unitᵉ element.ᵉ Theᵉ latterᵉ conditionᵉ holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ
[subgroupᵉ generatedᵉ by](group-theory.subgroups-generated-by-families-of-elements-groups.mdᵉ)
theᵉ commutators,ᵉ i.e.,ᵉ theᵉ commutatorᵉ subgroup,ᵉ isᵉ
[trivial](group-theory.trivial-subgroups.md).ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-abelian-is-trivial-commutator-subgroup-Groupᵉ :
    is-trivial-Subgroupᵉ Gᵉ (commutator-subgroup-Groupᵉ Gᵉ) →
    is-abelian-Groupᵉ Gᵉ
  is-abelian-is-trivial-commutator-subgroup-Groupᵉ Hᵉ =
    is-abelian-is-unit-commutator-Group'ᵉ Gᵉ
      ( λ xᵉ yᵉ →
        is-family-of-units-is-trivial-subgroup-family-of-elements-Groupᵉ Gᵉ
          ( family-of-commutators-Groupᵉ Gᵉ)
          ( Hᵉ)
          ( xᵉ ,ᵉ yᵉ))

module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  abstract
    is-trivial-commutator-subgroup-Abᵉ :
      is-trivial-Subgroupᵉ (group-Abᵉ Aᵉ) (commutator-subgroup-Abᵉ Aᵉ)
    is-trivial-commutator-subgroup-Abᵉ =
      is-trivial-subgroup-family-of-elements-Groupᵉ
        ( group-Abᵉ Aᵉ)
        ( family-of-commutators-Abᵉ Aᵉ)
        ( λ (xᵉ ,ᵉ yᵉ) → is-zero-commutator-Ab'ᵉ Aᵉ xᵉ yᵉ)
```

### Every group homomorphism into an abelian group nullifies the commutator subgroup

**Proof:**ᵉ Considerᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → A`ᵉ intoᵉ anᵉ abelianᵉ groupᵉ `A`.ᵉ Ourᵉ goalᵉ isᵉ to showᵉ thatᵉ `f`ᵉ
[nullifies](group-theory.nullifying-group-homomorphisms.mdᵉ) theᵉ commutatorᵉ
subgroupᵉ `[G,G]`,ᵉ i.e.,ᵉ thatᵉ `[G,G]`ᵉ isᵉ containedᵉ in theᵉ
[kernel](group-theory.kernels-homomorphisms-groups.mdᵉ) ofᵉ `f`.ᵉ

Sinceᵉ `A`ᵉ isᵉ abelianᵉ itᵉ followsᵉ thatᵉ theᵉ commutatorᵉ subgroupᵉ ofᵉ `A`ᵉ isᵉ
[trivial](group-theory.trivial-subgroups.md).ᵉ Furthermore,ᵉ anyᵉ groupᵉ
homomorphismᵉ mapsᵉ theᵉ commutatorᵉ subgroupᵉ to theᵉ commutatorᵉ subgroup,ᵉ i.e.,ᵉ weᵉ
haveᵉ `fᵉ [G,Gᵉ] ⊆ᵉ [A,A]`.ᵉ Sinceᵉ theᵉ commutatorᵉ subgroupᵉ `[A,A]`ᵉ isᵉ trivial,ᵉ thisᵉ
meansᵉ thatᵉ `f`ᵉ nullifiesᵉ theᵉ commutatorᵉ subgroupᵉ ofᵉ `G`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Aᵉ : Abᵉ l2ᵉ)
  where

  nullifies-commutator-normal-subgroup-hom-group-Abᵉ :
    (fᵉ : hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ)) →
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ
      ( group-Abᵉ Aᵉ)
      ( fᵉ)
      ( commutator-normal-subgroup-Groupᵉ Gᵉ)
  nullifies-commutator-normal-subgroup-hom-group-Abᵉ fᵉ =
    transitive-leq-Subgroupᵉ Gᵉ
      ( commutator-subgroup-Groupᵉ Gᵉ)
      ( pullback-Subgroupᵉ Gᵉ
        ( group-Abᵉ Aᵉ)
        ( fᵉ)
        ( commutator-subgroup-Groupᵉ (group-Abᵉ Aᵉ)))
      ( pullback-Subgroupᵉ Gᵉ (group-Abᵉ Aᵉ) fᵉ (trivial-Subgroupᵉ (group-Abᵉ Aᵉ)))
      ( λ xᵉ → is-trivial-commutator-subgroup-Abᵉ Aᵉ _)
      ( preserves-commutator-subgroup-hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ) fᵉ)

  is-equiv-hom-nullifying-hom-group-Abᵉ :
    is-equivᵉ
      ( hom-nullifying-hom-Groupᵉ Gᵉ
        ( group-Abᵉ Aᵉ)
        ( commutator-normal-subgroup-Groupᵉ Gᵉ))
  is-equiv-hom-nullifying-hom-group-Abᵉ =
    is-equiv-inclusion-is-full-subtypeᵉ
      ( λ fᵉ →
        nullifies-normal-subgroup-prop-hom-Groupᵉ Gᵉ
          ( group-Abᵉ Aᵉ)
          ( fᵉ)
          ( commutator-normal-subgroup-Groupᵉ Gᵉ))
      ( nullifies-commutator-normal-subgroup-hom-group-Abᵉ)

  compute-nullifying-hom-group-Abᵉ :
    nullifying-hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ) (commutator-normal-subgroup-Groupᵉ Gᵉ) ≃ᵉ
    hom-Groupᵉ Gᵉ (group-Abᵉ Aᵉ)
  compute-nullifying-hom-group-Abᵉ =
    equiv-inclusion-is-full-subtypeᵉ
      ( λ fᵉ →
        nullifies-normal-subgroup-prop-hom-Groupᵉ Gᵉ
          ( group-Abᵉ Aᵉ)
          ( fᵉ)
          ( commutator-normal-subgroup-Groupᵉ Gᵉ))
      ( nullifies-commutator-normal-subgroup-hom-group-Abᵉ)
```