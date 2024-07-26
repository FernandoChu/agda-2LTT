# Equivalences of higher groups

```agda
module higher-group-theory.equivalences-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.homomorphisms-higher-groupsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-isomorphismsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
```

</details>

## Definitions

### Equivalences of higher groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ)
  where

  equiv-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-∞-Groupᵉ =
    classifying-pointed-type-∞-Groupᵉ Gᵉ ≃∗ᵉ classifying-pointed-type-∞-Groupᵉ Hᵉ

  module _
    (eᵉ : equiv-∞-Groupᵉ)
    where

    hom-equiv-∞-Groupᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ
    hom-equiv-∞-Groupᵉ = pointed-map-pointed-equivᵉ eᵉ

    map-equiv-∞-Groupᵉ : type-∞-Groupᵉ Gᵉ → type-∞-Groupᵉ Hᵉ
    map-equiv-∞-Groupᵉ = map-hom-∞-Groupᵉ Gᵉ Hᵉ hom-equiv-∞-Groupᵉ

    pointed-equiv-equiv-∞-Groupᵉ :
      pointed-type-∞-Groupᵉ Gᵉ ≃∗ᵉ pointed-type-∞-Groupᵉ Hᵉ
    pointed-equiv-equiv-∞-Groupᵉ = pointed-equiv-Ω-pointed-equivᵉ eᵉ

    equiv-equiv-∞-Groupᵉ : type-∞-Groupᵉ Gᵉ ≃ᵉ type-∞-Groupᵉ Hᵉ
    equiv-equiv-∞-Groupᵉ = equiv-map-Ω-pointed-equivᵉ eᵉ
```

### The identity equivalence of higher groups

```agda
id-equiv-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) → equiv-∞-Groupᵉ Gᵉ Gᵉ
id-equiv-∞-Groupᵉ Gᵉ = id-pointed-equivᵉ
```

### Isomorphisms of ∞-groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ)
  where

  is-iso-∞-Groupᵉ : hom-∞-Groupᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-∞-Groupᵉ = is-pointed-isoᵉ
```

## Properties

### The total space of equivalences of higher groups is contractible

```agda
is-torsorial-equiv-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) →
  is-torsorialᵉ (λ (Hᵉ : ∞-Groupᵉ l1ᵉ) → equiv-∞-Groupᵉ Gᵉ Hᵉ)
is-torsorial-equiv-∞-Groupᵉ Gᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( is-torsorial-pointed-equivᵉ (classifying-pointed-type-∞-Groupᵉ Gᵉ))
    ( λ Xᵉ → is-prop-is-0-connectedᵉ (type-Pointed-Typeᵉ Xᵉ))
    ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
    ( id-pointed-equivᵉ)
    ( is-0-connected-classifying-type-∞-Groupᵉ Gᵉ)

equiv-eq-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ Hᵉ : ∞-Groupᵉ l1ᵉ) → (Gᵉ ＝ᵉ Hᵉ) → equiv-∞-Groupᵉ Gᵉ Hᵉ
equiv-eq-∞-Groupᵉ Gᵉ .Gᵉ reflᵉ = id-equiv-∞-Groupᵉ Gᵉ

is-equiv-equiv-eq-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ Hᵉ : ∞-Groupᵉ l1ᵉ) → is-equivᵉ (equiv-eq-∞-Groupᵉ Gᵉ Hᵉ)
is-equiv-equiv-eq-∞-Groupᵉ Gᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-equiv-∞-Groupᵉ Gᵉ)
    ( equiv-eq-∞-Groupᵉ Gᵉ)

extensionality-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ Hᵉ : ∞-Groupᵉ l1ᵉ) → (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ equiv-∞-Groupᵉ Gᵉ Hᵉ
pr1ᵉ (extensionality-∞-Groupᵉ Gᵉ Hᵉ) = equiv-eq-∞-Groupᵉ Gᵉ Hᵉ
pr2ᵉ (extensionality-∞-Groupᵉ Gᵉ Hᵉ) = is-equiv-equiv-eq-∞-Groupᵉ Gᵉ Hᵉ

eq-equiv-∞-Groupᵉ :
  {l1ᵉ : Level} (Gᵉ Hᵉ : ∞-Groupᵉ l1ᵉ) → equiv-∞-Groupᵉ Gᵉ Hᵉ → Gᵉ ＝ᵉ Hᵉ
eq-equiv-∞-Groupᵉ Gᵉ Hᵉ = map-inv-equivᵉ (extensionality-∞-Groupᵉ Gᵉ Hᵉ)
```