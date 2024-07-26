# Submonoids of commutative monoids

```agda
module group-theory.submonoids-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ
open import group-theory.subsets-commutative-monoidsᵉ
```

</details>

## Idea

Aᵉ submonoidᵉ ofᵉ aᵉ commutativeᵉ monoidᵉ `M`ᵉ isᵉ aᵉ subsetᵉ ofᵉ `M`ᵉ thatᵉ containsᵉ theᵉ
unitᵉ ofᵉ `M`ᵉ andᵉ isᵉ closedᵉ underᵉ multiplication.ᵉ

## Definitions

### Submonoids of commutative monoids

```agda
is-submonoid-prop-subset-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Pᵉ : subset-Commutative-Monoidᵉ l2ᵉ Mᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-submonoid-prop-subset-Commutative-Monoidᵉ Mᵉ =
  is-submonoid-prop-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

is-submonoid-subset-Commutative-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Pᵉ : subset-Commutative-Monoidᵉ l2ᵉ Mᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-submonoid-subset-Commutative-Monoidᵉ Mᵉ =
  is-submonoid-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

Commutative-Submonoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Commutative-Submonoidᵉ l2ᵉ Mᵉ =
  Submonoidᵉ l2ᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Pᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  subset-Commutative-Submonoidᵉ : subtypeᵉ l2ᵉ (type-Commutative-Monoidᵉ Mᵉ)
  subset-Commutative-Submonoidᵉ =
    subset-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-submonoid-Commutative-Submonoidᵉ :
    is-submonoid-subset-Commutative-Monoidᵉ Mᵉ subset-Commutative-Submonoidᵉ
  is-submonoid-Commutative-Submonoidᵉ =
    is-submonoid-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-in-Commutative-Submonoidᵉ : type-Commutative-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-Commutative-Submonoidᵉ =
    is-in-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-prop-is-in-Commutative-Submonoidᵉ :
    (xᵉ : type-Commutative-Monoidᵉ Mᵉ) → is-propᵉ (is-in-Commutative-Submonoidᵉ xᵉ)
  is-prop-is-in-Commutative-Submonoidᵉ =
    is-prop-is-in-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-closed-under-eq-Commutative-Submonoidᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    is-in-Commutative-Submonoidᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Commutative-Submonoidᵉ yᵉ
  is-closed-under-eq-Commutative-Submonoidᵉ =
    is-closed-under-eq-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-closed-under-eq-Commutative-Submonoid'ᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    is-in-Commutative-Submonoidᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-Commutative-Submonoidᵉ xᵉ
  is-closed-under-eq-Commutative-Submonoid'ᵉ =
    is-closed-under-eq-Submonoid'ᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  type-Commutative-Submonoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Commutative-Submonoidᵉ =
    type-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-set-type-Commutative-Submonoidᵉ : is-setᵉ type-Commutative-Submonoidᵉ
  is-set-type-Commutative-Submonoidᵉ =
    is-set-type-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  set-Commutative-Submonoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Commutative-Submonoidᵉ = set-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  inclusion-Commutative-Submonoidᵉ :
    type-Commutative-Submonoidᵉ → type-Commutative-Monoidᵉ Mᵉ
  inclusion-Commutative-Submonoidᵉ =
    inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  ap-inclusion-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Commutative-Submonoidᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-Commutative-Submonoidᵉ xᵉ ＝ᵉ inclusion-Commutative-Submonoidᵉ yᵉ
  ap-inclusion-Commutative-Submonoidᵉ =
    ap-inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-in-submonoid-inclusion-Commutative-Submonoidᵉ :
    (xᵉ : type-Commutative-Submonoidᵉ) →
    is-in-Commutative-Submonoidᵉ (inclusion-Commutative-Submonoidᵉ xᵉ)
  is-in-submonoid-inclusion-Commutative-Submonoidᵉ =
    is-in-submonoid-inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  contains-unit-Commutative-Submonoidᵉ :
    is-in-Commutative-Submonoidᵉ (unit-Commutative-Monoidᵉ Mᵉ)
  contains-unit-Commutative-Submonoidᵉ =
    contains-unit-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  unit-Commutative-Submonoidᵉ : type-Commutative-Submonoidᵉ
  unit-Commutative-Submonoidᵉ =
    unit-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-closed-under-multiplication-Commutative-Submonoidᵉ :
    {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    is-in-Commutative-Submonoidᵉ xᵉ → is-in-Commutative-Submonoidᵉ yᵉ →
    is-in-Commutative-Submonoidᵉ (mul-Commutative-Monoidᵉ Mᵉ xᵉ yᵉ)
  is-closed-under-multiplication-Commutative-Submonoidᵉ =
    is-closed-under-multiplication-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  mul-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Commutative-Submonoidᵉ) → type-Commutative-Submonoidᵉ
  mul-Commutative-Submonoidᵉ = mul-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  associative-mul-Commutative-Submonoidᵉ :
    (xᵉ yᵉ zᵉ : type-Commutative-Submonoidᵉ) →
    (mul-Commutative-Submonoidᵉ (mul-Commutative-Submonoidᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
    (mul-Commutative-Submonoidᵉ xᵉ (mul-Commutative-Submonoidᵉ yᵉ zᵉ))
  associative-mul-Commutative-Submonoidᵉ =
    associative-mul-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  semigroup-Commutative-Submonoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Commutative-Submonoidᵉ =
    semigroup-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  left-unit-law-mul-Commutative-Submonoidᵉ :
    (xᵉ : type-Commutative-Submonoidᵉ) →
    mul-Commutative-Submonoidᵉ unit-Commutative-Submonoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Commutative-Submonoidᵉ =
    left-unit-law-mul-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  right-unit-law-mul-Commutative-Submonoidᵉ :
    (xᵉ : type-Commutative-Submonoidᵉ) →
    mul-Commutative-Submonoidᵉ xᵉ unit-Commutative-Submonoidᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Commutative-Submonoidᵉ =
    right-unit-law-mul-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  commutative-mul-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Commutative-Submonoidᵉ) →
    mul-Commutative-Submonoidᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Submonoidᵉ yᵉ xᵉ
  commutative-mul-Commutative-Submonoidᵉ xᵉ yᵉ =
    eq-type-subtypeᵉ
      ( subset-Commutative-Submonoidᵉ)
      ( commutative-mul-Commutative-Monoidᵉ Mᵉ
        ( inclusion-Commutative-Submonoidᵉ xᵉ)
        ( inclusion-Commutative-Submonoidᵉ yᵉ))

  monoid-Commutative-Submonoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-Commutative-Submonoidᵉ =
    monoid-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  commutative-monoid-Commutative-Submonoidᵉ : Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ commutative-monoid-Commutative-Submonoidᵉ =
    monoid-Commutative-Submonoidᵉ
  pr2ᵉ commutative-monoid-Commutative-Submonoidᵉ =
    commutative-mul-Commutative-Submonoidᵉ

  preserves-unit-inclusion-Commutative-Submonoidᵉ :
    inclusion-Commutative-Submonoidᵉ unit-Commutative-Submonoidᵉ ＝ᵉ
    unit-Commutative-Monoidᵉ Mᵉ
  preserves-unit-inclusion-Commutative-Submonoidᵉ =
    preserves-unit-inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  preserves-mul-inclusion-Commutative-Submonoidᵉ :
    (xᵉ yᵉ : type-Commutative-Submonoidᵉ) →
    inclusion-Commutative-Submonoidᵉ (mul-Commutative-Submonoidᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Monoidᵉ Mᵉ
      ( inclusion-Commutative-Submonoidᵉ xᵉ)
      ( inclusion-Commutative-Submonoidᵉ yᵉ)
  preserves-mul-inclusion-Commutative-Submonoidᵉ xᵉ yᵉ =
    preserves-mul-inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ {xᵉ} {yᵉ}

  hom-inclusion-Commutative-Submonoidᵉ :
    hom-Commutative-Monoidᵉ commutative-monoid-Commutative-Submonoidᵉ Mᵉ
  hom-inclusion-Commutative-Submonoidᵉ =
    hom-inclusion-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ
```

## Properties

### Extensionality of the type of all submonoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Nᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ)
  where

  has-same-elements-Commutative-Submonoidᵉ :
    {l3ᵉ : Level} → Commutative-Submonoidᵉ l3ᵉ Mᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-Commutative-Submonoidᵉ =
    has-same-elements-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Nᵉ

  extensionality-Commutative-Submonoidᵉ :
    (Kᵉ : Commutative-Submonoidᵉ l2ᵉ Mᵉ) →
    (Nᵉ ＝ᵉ Kᵉ) ≃ᵉ has-same-elements-Commutative-Submonoidᵉ Kᵉ
  extensionality-Commutative-Submonoidᵉ =
    extensionality-Submonoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Nᵉ
```