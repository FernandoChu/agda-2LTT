# Abelian groups

```agda
module finite-group-theory.finite-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-groupsᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Abelianᵉ groupsᵉ areᵉ groupsᵉ ofᵉ whichᵉ theᵉ groupᵉ operationᵉ isᵉ commutativeᵉ

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Group-𝔽ᵉ : {lᵉ : Level} → Group-𝔽ᵉ lᵉ → Propᵉ lᵉ
is-abelian-prop-Group-𝔽ᵉ Gᵉ = is-abelian-prop-Groupᵉ (group-Group-𝔽ᵉ Gᵉ)

is-abelian-Group-𝔽ᵉ : {lᵉ : Level} → Group-𝔽ᵉ lᵉ → UUᵉ lᵉ
is-abelian-Group-𝔽ᵉ Gᵉ = type-Propᵉ (is-abelian-prop-Group-𝔽ᵉ Gᵉ)

is-prop-is-abelian-Group-𝔽ᵉ :
  {lᵉ : Level} (Gᵉ : Group-𝔽ᵉ lᵉ) → is-propᵉ (is-abelian-Group-𝔽ᵉ Gᵉ)
is-prop-is-abelian-Group-𝔽ᵉ Gᵉ =
  is-prop-type-Propᵉ (is-abelian-prop-Group-𝔽ᵉ Gᵉ)
```

### The type of abelian groups

```agda
Ab-𝔽ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Ab-𝔽ᵉ lᵉ = Σᵉ (Group-𝔽ᵉ lᵉ) is-abelian-Group-𝔽ᵉ

finite-abelian-group-is-finite-Abᵉ :
  {lᵉ : Level} → (Aᵉ : Abᵉ lᵉ) → is-finiteᵉ (type-Abᵉ Aᵉ) → Ab-𝔽ᵉ lᵉ
pr1ᵉ (finite-abelian-group-is-finite-Abᵉ Aᵉ fᵉ) =
  finite-group-is-finite-Groupᵉ (group-Abᵉ Aᵉ) fᵉ
pr2ᵉ (finite-abelian-group-is-finite-Abᵉ Aᵉ fᵉ) = pr2ᵉ Aᵉ

module _
  {lᵉ : Level} (Aᵉ : Ab-𝔽ᵉ lᵉ)
  where

  finite-group-Ab-𝔽ᵉ : Group-𝔽ᵉ lᵉ
  finite-group-Ab-𝔽ᵉ = pr1ᵉ Aᵉ

  group-Ab-𝔽ᵉ : Groupᵉ lᵉ
  group-Ab-𝔽ᵉ = group-Group-𝔽ᵉ finite-group-Ab-𝔽ᵉ

  finite-type-Ab-𝔽ᵉ : 𝔽ᵉ lᵉ
  finite-type-Ab-𝔽ᵉ = finite-type-Group-𝔽ᵉ finite-group-Ab-𝔽ᵉ

  type-Ab-𝔽ᵉ : UUᵉ lᵉ
  type-Ab-𝔽ᵉ = type-Group-𝔽ᵉ finite-group-Ab-𝔽ᵉ

  is-finite-type-Ab-𝔽ᵉ : is-finiteᵉ type-Ab-𝔽ᵉ
  is-finite-type-Ab-𝔽ᵉ = is-finite-type-Group-𝔽ᵉ finite-group-Ab-𝔽ᵉ

  set-Ab-𝔽ᵉ : Setᵉ lᵉ
  set-Ab-𝔽ᵉ = set-Groupᵉ group-Ab-𝔽ᵉ

  is-set-type-Ab-𝔽ᵉ : is-setᵉ type-Ab-𝔽ᵉ
  is-set-type-Ab-𝔽ᵉ = is-set-type-Groupᵉ group-Ab-𝔽ᵉ

  has-associative-add-Ab-𝔽ᵉ : has-associative-mul-Setᵉ set-Ab-𝔽ᵉ
  has-associative-add-Ab-𝔽ᵉ = has-associative-mul-Groupᵉ group-Ab-𝔽ᵉ

  add-Ab-𝔽ᵉ : type-Ab-𝔽ᵉ → type-Ab-𝔽ᵉ → type-Ab-𝔽ᵉ
  add-Ab-𝔽ᵉ = mul-Groupᵉ group-Ab-𝔽ᵉ

  add-Ab-𝔽'ᵉ : type-Ab-𝔽ᵉ → type-Ab-𝔽ᵉ → type-Ab-𝔽ᵉ
  add-Ab-𝔽'ᵉ = mul-Group'ᵉ group-Ab-𝔽ᵉ

  commutative-add-Ab-𝔽ᵉ : (xᵉ yᵉ : type-Ab-𝔽ᵉ) → Idᵉ (add-Ab-𝔽ᵉ xᵉ yᵉ) (add-Ab-𝔽ᵉ yᵉ xᵉ)
  commutative-add-Ab-𝔽ᵉ = pr2ᵉ Aᵉ

  ab-Ab-𝔽ᵉ : Abᵉ lᵉ
  pr1ᵉ ab-Ab-𝔽ᵉ = group-Ab-𝔽ᵉ
  pr2ᵉ ab-Ab-𝔽ᵉ = commutative-add-Ab-𝔽ᵉ

  ap-add-Ab-𝔽ᵉ :
    {xᵉ yᵉ x'ᵉ y'ᵉ : type-Ab-𝔽ᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → add-Ab-𝔽ᵉ xᵉ yᵉ ＝ᵉ add-Ab-𝔽ᵉ x'ᵉ y'ᵉ
  ap-add-Ab-𝔽ᵉ = ap-add-Abᵉ ab-Ab-𝔽ᵉ

  associative-add-Ab-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Ab-𝔽ᵉ xᵉ (add-Ab-𝔽ᵉ yᵉ zᵉ)
  associative-add-Ab-𝔽ᵉ = associative-mul-Groupᵉ group-Ab-𝔽ᵉ

  semigroup-Ab-𝔽ᵉ : Semigroupᵉ lᵉ
  semigroup-Ab-𝔽ᵉ = semigroup-Groupᵉ group-Ab-𝔽ᵉ

  is-group-Ab-𝔽ᵉ : is-group-Semigroupᵉ semigroup-Ab-𝔽ᵉ
  is-group-Ab-𝔽ᵉ = is-group-Groupᵉ group-Ab-𝔽ᵉ

  has-zero-Ab-𝔽ᵉ : is-unital-Semigroupᵉ semigroup-Ab-𝔽ᵉ
  has-zero-Ab-𝔽ᵉ = is-unital-Groupᵉ group-Ab-𝔽ᵉ

  zero-Ab-𝔽ᵉ : type-Ab-𝔽ᵉ
  zero-Ab-𝔽ᵉ = unit-Groupᵉ group-Ab-𝔽ᵉ

  is-zero-Ab-𝔽ᵉ : type-Ab-𝔽ᵉ → UUᵉ lᵉ
  is-zero-Ab-𝔽ᵉ = is-unit-Groupᵉ group-Ab-𝔽ᵉ

  is-prop-is-zero-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ) → is-propᵉ (is-zero-Ab-𝔽ᵉ xᵉ)
  is-prop-is-zero-Ab-𝔽ᵉ = is-prop-is-unit-Groupᵉ group-Ab-𝔽ᵉ

  is-zero-prop-Ab-𝔽ᵉ : type-Ab-𝔽ᵉ → Propᵉ lᵉ
  is-zero-prop-Ab-𝔽ᵉ = is-unit-prop-Groupᵉ group-Ab-𝔽ᵉ

  left-unit-law-add-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ zero-Ab-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Ab-𝔽ᵉ = left-unit-law-mul-Groupᵉ group-Ab-𝔽ᵉ

  right-unit-law-add-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ xᵉ zero-Ab-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-add-Ab-𝔽ᵉ = right-unit-law-mul-Groupᵉ group-Ab-𝔽ᵉ

  has-negatives-Ab-𝔽ᵉ : is-group-is-unital-Semigroupᵉ semigroup-Ab-𝔽ᵉ has-zero-Ab-𝔽ᵉ
  has-negatives-Ab-𝔽ᵉ = has-inverses-Groupᵉ group-Ab-𝔽ᵉ

  neg-Ab-𝔽ᵉ : type-Ab-𝔽ᵉ → type-Ab-𝔽ᵉ
  neg-Ab-𝔽ᵉ = inv-Groupᵉ group-Ab-𝔽ᵉ

  left-inverse-law-add-Ab-𝔽ᵉ :
    (xᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ (neg-Ab-𝔽ᵉ xᵉ) xᵉ ＝ᵉ zero-Ab-𝔽ᵉ
  left-inverse-law-add-Ab-𝔽ᵉ = left-inverse-law-mul-Groupᵉ group-Ab-𝔽ᵉ

  right-inverse-law-add-Ab-𝔽ᵉ :
    (xᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ xᵉ (neg-Ab-𝔽ᵉ xᵉ) ＝ᵉ zero-Ab-𝔽ᵉ
  right-inverse-law-add-Ab-𝔽ᵉ = right-inverse-law-mul-Groupᵉ group-Ab-𝔽ᵉ

  interchange-add-add-Ab-𝔽ᵉ :
    (aᵉ bᵉ cᵉ dᵉ : type-Ab-𝔽ᵉ) →
    add-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ aᵉ bᵉ) (add-Ab-𝔽ᵉ cᵉ dᵉ) ＝ᵉ
    add-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ aᵉ cᵉ) (add-Ab-𝔽ᵉ bᵉ dᵉ)
  interchange-add-add-Ab-𝔽ᵉ =
    interchange-law-commutative-and-associativeᵉ
      add-Ab-𝔽ᵉ
      commutative-add-Ab-𝔽ᵉ
      associative-add-Ab-𝔽ᵉ

  right-swap-add-Ab-𝔽ᵉ :
    (aᵉ bᵉ cᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ aᵉ bᵉ) cᵉ ＝ᵉ add-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ aᵉ cᵉ) bᵉ
  right-swap-add-Ab-𝔽ᵉ = right-swap-add-Abᵉ ab-Ab-𝔽ᵉ

  left-swap-add-Ab-𝔽ᵉ :
    (aᵉ bᵉ cᵉ : type-Ab-𝔽ᵉ) → add-Ab-𝔽ᵉ aᵉ (add-Ab-𝔽ᵉ bᵉ cᵉ) ＝ᵉ add-Ab-𝔽ᵉ bᵉ (add-Ab-𝔽ᵉ aᵉ cᵉ)
  left-swap-add-Ab-𝔽ᵉ = left-swap-add-Abᵉ ab-Ab-𝔽ᵉ

  distributive-neg-add-Ab-𝔽ᵉ :
    (xᵉ yᵉ : type-Ab-𝔽ᵉ) →
    neg-Ab-𝔽ᵉ (add-Ab-𝔽ᵉ xᵉ yᵉ) ＝ᵉ add-Ab-𝔽ᵉ (neg-Ab-𝔽ᵉ xᵉ) (neg-Ab-𝔽ᵉ yᵉ)
  distributive-neg-add-Ab-𝔽ᵉ = distributive-neg-add-Abᵉ ab-Ab-𝔽ᵉ

  neg-neg-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ) → neg-Ab-𝔽ᵉ (neg-Ab-𝔽ᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-Ab-𝔽ᵉ = neg-neg-Abᵉ ab-Ab-𝔽ᵉ

  neg-zero-Ab-𝔽ᵉ : neg-Ab-𝔽ᵉ zero-Ab-𝔽ᵉ ＝ᵉ zero-Ab-𝔽ᵉ
  neg-zero-Ab-𝔽ᵉ = neg-zero-Abᵉ ab-Ab-𝔽ᵉ
```

### Conjugation in an abelian group

```agda
module _
  {lᵉ : Level} (Aᵉ : Ab-𝔽ᵉ lᵉ)
  where

  equiv-conjugation-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ Aᵉ) → type-Ab-𝔽ᵉ Aᵉ ≃ᵉ type-Ab-𝔽ᵉ Aᵉ
  equiv-conjugation-Ab-𝔽ᵉ = equiv-conjugation-Groupᵉ (group-Ab-𝔽ᵉ Aᵉ)

  conjugation-Ab-𝔽ᵉ : (xᵉ : type-Ab-𝔽ᵉ Aᵉ) → type-Ab-𝔽ᵉ Aᵉ → type-Ab-𝔽ᵉ Aᵉ
  conjugation-Ab-𝔽ᵉ = conjugation-Groupᵉ (group-Ab-𝔽ᵉ Aᵉ)

  equiv-conjugation-Ab-𝔽'ᵉ : (xᵉ : type-Ab-𝔽ᵉ Aᵉ) → type-Ab-𝔽ᵉ Aᵉ ≃ᵉ type-Ab-𝔽ᵉ Aᵉ
  equiv-conjugation-Ab-𝔽'ᵉ = equiv-conjugation-Group'ᵉ (group-Ab-𝔽ᵉ Aᵉ)

  conjugation-Ab-𝔽'ᵉ : (xᵉ : type-Ab-𝔽ᵉ Aᵉ) → type-Ab-𝔽ᵉ Aᵉ → type-Ab-𝔽ᵉ Aᵉ
  conjugation-Ab-𝔽'ᵉ = conjugation-Group'ᵉ (group-Ab-𝔽ᵉ Aᵉ)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of an abelian group

```agda
module _
  {lᵉ : Level}
  (Xᵉ : 𝔽ᵉ lᵉ)
  where

  structure-abelian-group-𝔽ᵉ : UUᵉ lᵉ
  structure-abelian-group-𝔽ᵉ =
    Σᵉ ( structure-group-𝔽ᵉ Xᵉ)
      ( λ gᵉ → is-abelian-Group-𝔽ᵉ (finite-group-structure-group-𝔽ᵉ Xᵉ gᵉ))

  finite-abelian-group-structure-abelian-group-𝔽ᵉ :
    structure-abelian-group-𝔽ᵉ → Ab-𝔽ᵉ lᵉ
  pr1ᵉ (finite-abelian-group-structure-abelian-group-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) =
    finite-group-structure-group-𝔽ᵉ Xᵉ mᵉ
  pr2ᵉ (finite-abelian-group-structure-abelian-group-𝔽ᵉ (mᵉ ,ᵉ cᵉ)) = cᵉ

  is-finite-structure-abelian-group-𝔽ᵉ :
    is-finiteᵉ structure-abelian-group-𝔽ᵉ
  is-finite-structure-abelian-group-𝔽ᵉ =
    is-finite-Σᵉ
      ( is-finite-structure-group-𝔽ᵉ Xᵉ)
      ( λ gᵉ →
        is-finite-Πᵉ
          ( is-finite-type-𝔽ᵉ Xᵉ)
          ( λ xᵉ →
            is-finite-Πᵉ
              ( is-finite-type-𝔽ᵉ Xᵉ)
              ( λ yᵉ → is-finite-eq-𝔽ᵉ Xᵉ)))
```