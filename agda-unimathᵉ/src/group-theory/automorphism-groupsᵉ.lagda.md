# Automorphism groups

```agda
module group-theory.automorphism-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.1-typesᵉ
open import foundation.connected-componentsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-concrete-groupsᵉ

open import higher-group-theory.equivalences-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Theᵉ **automorphimᵉ group**ᵉ ofᵉ `aᵉ : A`ᵉ isᵉ theᵉ [group](group-theory.groups.mdᵉ) ofᵉ
symmetriesᵉ ofᵉ `a`ᵉ in `A`.ᵉ

## Definitions

### Automorphism ∞-groups of a type

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) (aᵉ : Aᵉ)
  where

  classifying-type-Automorphism-∞-Groupᵉ : UUᵉ lᵉ
  classifying-type-Automorphism-∞-Groupᵉ = connected-componentᵉ Aᵉ aᵉ

  shape-Automorphism-∞-Groupᵉ : classifying-type-Automorphism-∞-Groupᵉ
  pr1ᵉ shape-Automorphism-∞-Groupᵉ = aᵉ
  pr2ᵉ shape-Automorphism-∞-Groupᵉ = unit-trunc-Propᵉ reflᵉ

  classifying-pointed-type-Automorphism-∞-Groupᵉ : Pointed-Typeᵉ lᵉ
  pr1ᵉ classifying-pointed-type-Automorphism-∞-Groupᵉ =
    classifying-type-Automorphism-∞-Groupᵉ
  pr2ᵉ classifying-pointed-type-Automorphism-∞-Groupᵉ =
    shape-Automorphism-∞-Groupᵉ

  is-0-connected-classifying-type-Automorphism-∞-Groupᵉ :
    is-0-connectedᵉ classifying-type-Automorphism-∞-Groupᵉ
  is-0-connected-classifying-type-Automorphism-∞-Groupᵉ =
    is-0-connected-connected-componentᵉ Aᵉ aᵉ

  Automorphism-∞-Groupᵉ : ∞-Groupᵉ lᵉ
  pr1ᵉ Automorphism-∞-Groupᵉ = classifying-pointed-type-Automorphism-∞-Groupᵉ
  pr2ᵉ Automorphism-∞-Groupᵉ =
    is-0-connected-classifying-type-Automorphism-∞-Groupᵉ
```

### Automorphism groups of objects in a 1-type

```agda
module _
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (aᵉ : type-1-Typeᵉ Aᵉ)
  where

  classifying-type-Automorphism-Groupᵉ : UUᵉ lᵉ
  classifying-type-Automorphism-Groupᵉ =
    classifying-type-Automorphism-∞-Groupᵉ (type-1-Typeᵉ Aᵉ) aᵉ

  shape-Automorphism-Groupᵉ : classifying-type-Automorphism-Groupᵉ
  shape-Automorphism-Groupᵉ = shape-Automorphism-∞-Groupᵉ (type-1-Typeᵉ Aᵉ) aᵉ

  Automorphism-Groupᵉ : Concrete-Groupᵉ lᵉ
  pr1ᵉ Automorphism-Groupᵉ = Automorphism-∞-Groupᵉ (type-1-Typeᵉ Aᵉ) aᵉ
  pr2ᵉ Automorphism-Groupᵉ =
    is-trunc-connected-componentᵉ
      ( type-1-Typeᵉ Aᵉ)
      ( aᵉ)
      ( is-1-type-type-1-Typeᵉ Aᵉ)
      ( pairᵉ aᵉ (unit-trunc-Propᵉ reflᵉ))
      ( pairᵉ aᵉ (unit-trunc-Propᵉ reflᵉ))

  ∞-group-Automorphism-Groupᵉ : ∞-Groupᵉ lᵉ
  ∞-group-Automorphism-Groupᵉ = ∞-group-Concrete-Groupᵉ Automorphism-Groupᵉ
```

## Properties

### Characerizing the identity type of `Automorphism-∞-Group`

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ)
  where

  Eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) → UUᵉ lᵉ
  Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ = pr1ᵉ Xᵉ ＝ᵉ pr1ᵉ Yᵉ

  refl-Eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Xᵉ
  refl-Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ = reflᵉ

  is-torsorial-Eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    is-torsorialᵉ (Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ)
  is-torsorial-Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-Idᵉ (pr1ᵉ Xᵉ))
      ( λ aᵉ → is-prop-type-trunc-Propᵉ)
      ( pr1ᵉ Xᵉ)
      ( reflᵉ)
      ( pr2ᵉ Xᵉ)

  Eq-eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ
  Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ .Xᵉ reflᵉ =
    refl-Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ

  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    is-equivᵉ (Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ)
  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ)
      ( Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ)

  extensionality-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ) =
    Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ
  pr2ᵉ (extensionality-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ) =
    is-equiv-Eq-eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ

  eq-Eq-classifying-type-Automorphism-∞-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-∞-Groupᵉ Aᵉ aᵉ) →
    Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-Eq-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-classifying-type-Automorphism-∞-Groupᵉ Xᵉ Yᵉ)
```

### Characerizing the identity type of `Automorphism-Group`

```agda
module _
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) (aᵉ : type-1-Typeᵉ Aᵉ)
  where

  Eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) → UUᵉ lᵉ
  Eq-classifying-type-Automorphism-Groupᵉ =
    Eq-classifying-type-Automorphism-∞-Groupᵉ aᵉ

  refl-Eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    Eq-classifying-type-Automorphism-Groupᵉ Xᵉ Xᵉ
  refl-Eq-classifying-type-Automorphism-Groupᵉ =
    refl-Eq-classifying-type-Automorphism-∞-Groupᵉ aᵉ

  is-torsorial-Eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    is-torsorialᵉ (Eq-classifying-type-Automorphism-Groupᵉ Xᵉ)
  is-torsorial-Eq-classifying-type-Automorphism-Groupᵉ =
    is-torsorial-Eq-classifying-type-Automorphism-∞-Groupᵉ aᵉ

  Eq-eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → Eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ
  Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ .Xᵉ reflᵉ =
    refl-Eq-classifying-type-Automorphism-Groupᵉ Xᵉ

  is-equiv-Eq-eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    is-equivᵉ (Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ)
  is-equiv-Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-classifying-type-Automorphism-Groupᵉ Xᵉ)
      ( Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ)

  extensionality-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ Eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ) =
    Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ
  pr2ᵉ (extensionality-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ) =
    is-equiv-Eq-eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ

  eq-Eq-classifying-type-Automorphism-Groupᵉ :
    (Xᵉ Yᵉ : classifying-type-Automorphism-Groupᵉ Aᵉ aᵉ) →
    Eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-Eq-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-classifying-type-Automorphism-Groupᵉ Xᵉ Yᵉ)
```

### Equal elements have equivalent automorphism ∞-groups

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  equiv-eq-Automorphism-∞-Groupᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    equiv-∞-Groupᵉ (Automorphism-∞-Groupᵉ Aᵉ xᵉ) (Automorphism-∞-Groupᵉ Aᵉ yᵉ)
  equiv-eq-Automorphism-∞-Groupᵉ reflᵉ =
    id-equiv-∞-Groupᵉ (Automorphism-∞-Groupᵉ Aᵉ _)
```

### Equal elements in a 1-type have isomorphic automorphism groups

```agda
module _
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ)
  where

  equiv-eq-Automorphism-Groupᵉ :
    {xᵉ yᵉ : type-1-Typeᵉ Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    equiv-Concrete-Groupᵉ (Automorphism-Groupᵉ Aᵉ xᵉ) (Automorphism-Groupᵉ Aᵉ yᵉ)
  equiv-eq-Automorphism-Groupᵉ reflᵉ =
    id-equiv-Concrete-Groupᵉ (Automorphism-Groupᵉ Aᵉ _)
```