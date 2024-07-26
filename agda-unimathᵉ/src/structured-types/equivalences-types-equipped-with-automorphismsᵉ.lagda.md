# Equivalences of types equipped with automorphisms

```agda
module structured-types.equivalences-types-equipped-with-automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import structured-types.equivalences-types-equipped-with-endomorphismsᵉ
open import structured-types.morphisms-types-equipped-with-automorphismsᵉ
open import structured-types.types-equipped-with-automorphismsᵉ
```

</details>

## Definition

### The predicate of being an equivalence of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  is-equiv-hom-Type-With-Automorphismᵉ :
    (hᵉ : hom-Type-With-Automorphismᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equiv-hom-Type-With-Automorphismᵉ =
    is-equiv-hom-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

### Equivalences of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  equiv-Type-With-Automorphismᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Type-With-Automorphismᵉ =
    equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  equiv-Type-With-Automorphism'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-Type-With-Automorphism'ᵉ =
    equiv-Type-With-Endomorphism'ᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  compute-equiv-Type-With-Automorphismᵉ :
    equiv-Type-With-Automorphism'ᵉ ≃ᵉ equiv-Type-With-Automorphismᵉ
  compute-equiv-Type-With-Automorphismᵉ =
    compute-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  equiv-equiv-Type-With-Automorphismᵉ :
    equiv-Type-With-Automorphismᵉ →
    type-Type-With-Automorphismᵉ Xᵉ ≃ᵉ type-Type-With-Automorphismᵉ Yᵉ
  equiv-equiv-Type-With-Automorphismᵉ =
    equiv-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  map-equiv-Type-With-Automorphismᵉ :
    equiv-Type-With-Automorphismᵉ →
    type-Type-With-Automorphismᵉ Xᵉ → type-Type-With-Automorphismᵉ Yᵉ
  map-equiv-Type-With-Automorphismᵉ =
    map-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  coherence-square-equiv-Type-With-Automorphismᵉ :
    (eᵉ : equiv-Type-With-Automorphismᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-Type-With-Automorphismᵉ eᵉ)
      ( map-Type-With-Automorphismᵉ Xᵉ)
      ( map-Type-With-Automorphismᵉ Yᵉ)
      ( map-equiv-Type-With-Automorphismᵉ eᵉ)
  coherence-square-equiv-Type-With-Automorphismᵉ =
    coherence-square-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  hom-equiv-Type-With-Automorphismᵉ :
    equiv-Type-With-Automorphismᵉ → hom-Type-With-Automorphismᵉ Xᵉ Yᵉ
  hom-equiv-Type-With-Automorphismᵉ =
    hom-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  is-equiv-equiv-Type-With-Automorphismᵉ :
    (eᵉ : equiv-Type-With-Automorphismᵉ) →
    is-equiv-hom-Type-With-Automorphismᵉ Xᵉ Yᵉ (hom-equiv-Type-With-Automorphismᵉ eᵉ)
  is-equiv-equiv-Type-With-Automorphismᵉ =
    is-equiv-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

### The identity equivalence

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  where

  id-equiv-Type-With-Automorphismᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Xᵉ
  id-equiv-Type-With-Automorphismᵉ =
    id-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
```

### Composition for equivalences of types equipped with automorphisms

```agda
comp-equiv-Type-With-Automorphismᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  (Zᵉ : Type-With-Automorphismᵉ l3ᵉ) →
  equiv-Type-With-Automorphismᵉ Yᵉ Zᵉ →
  equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ →
  equiv-Type-With-Automorphismᵉ Xᵉ Zᵉ
comp-equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ Zᵉ =
  comp-equiv-Type-With-Endomorphismᵉ
    ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
    ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
    ( type-with-endomorphism-Type-With-Automorphismᵉ Zᵉ)
```

### Inverses of equivalences of types equipped with automorphisms

```agda
inv-equiv-Type-With-Automorphismᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ) →
  equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ → equiv-Type-With-Automorphismᵉ Yᵉ Xᵉ
inv-equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ =
  inv-equiv-Type-With-Endomorphismᵉ
    ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
    ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

### Homotopies of equivalences of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  htpy-equiv-Type-With-Automorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-equiv-Type-With-Automorphismᵉ =
    htpy-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  refl-htpy-equiv-Type-With-Automorphismᵉ :
    ( eᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    htpy-equiv-Type-With-Automorphismᵉ eᵉ eᵉ
  refl-htpy-equiv-Type-With-Automorphismᵉ =
    refl-htpy-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  htpy-eq-equiv-Type-With-Automorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    eᵉ ＝ᵉ fᵉ → htpy-equiv-Type-With-Automorphismᵉ eᵉ fᵉ
  htpy-eq-equiv-Type-With-Automorphismᵉ =
    htpy-eq-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  is-torsorial-htpy-equiv-Type-With-Automorphismᵉ :
    (eᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    is-torsorialᵉ (htpy-equiv-Type-With-Automorphismᵉ eᵉ)
  is-torsorial-htpy-equiv-Type-With-Automorphismᵉ =
    is-torsorial-htpy-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  is-equiv-htpy-eq-equiv-Type-With-Automorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-equiv-Type-With-Automorphismᵉ eᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Type-With-Automorphismᵉ =
    is-equiv-htpy-eq-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  extensionality-equiv-Type-With-Automorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Type-With-Automorphismᵉ eᵉ fᵉ
  extensionality-equiv-Type-With-Automorphismᵉ =
    extensionality-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  eq-htpy-equiv-Type-With-Automorphismᵉ :
    (eᵉ fᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    htpy-equiv-Type-With-Automorphismᵉ eᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Type-With-Automorphismᵉ =
    eq-htpy-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

## Properties

### Unit laws for composition of equivalences of types equipped with automorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  (Yᵉ : Type-With-Automorphismᵉ l2ᵉ)
  where

  left-unit-law-comp-equiv-Type-With-Automorphismᵉ :
    (eᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    comp-equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ Yᵉ
      ( id-equiv-Type-With-Automorphismᵉ Yᵉ) eᵉ ＝ᵉ
    eᵉ
  left-unit-law-comp-equiv-Type-With-Automorphismᵉ =
    left-unit-law-comp-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)

  right-unit-law-comp-equiv-Type-With-Automorphismᵉ :
    (eᵉ : equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ) →
    comp-equiv-Type-With-Automorphismᵉ Xᵉ Xᵉ Yᵉ eᵉ
      ( id-equiv-Type-With-Automorphismᵉ Xᵉ) ＝ᵉ
    eᵉ
  right-unit-law-comp-equiv-Type-With-Automorphismᵉ =
    right-unit-law-comp-equiv-Type-With-Endomorphismᵉ
      ( type-with-endomorphism-Type-With-Automorphismᵉ Xᵉ)
      ( type-with-endomorphism-Type-With-Automorphismᵉ Yᵉ)
```

### Extensionality of types equipped with automorphisms

```agda
module _
  {l1ᵉ : Level} (Xᵉ : Type-With-Automorphismᵉ l1ᵉ)
  where

  equiv-eq-Type-With-Automorphismᵉ :
    ( Yᵉ : Type-With-Automorphismᵉ l1ᵉ) →
    Xᵉ ＝ᵉ Yᵉ → equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ
  equiv-eq-Type-With-Automorphismᵉ .Xᵉ reflᵉ =
    id-equiv-Type-With-Automorphismᵉ Xᵉ

  is-torsorial-equiv-Type-With-Automorphismᵉ :
    is-torsorialᵉ (equiv-Type-With-Automorphismᵉ Xᵉ)
  is-torsorial-equiv-Type-With-Automorphismᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (type-Type-With-Automorphismᵉ Xᵉ))
      ( type-Type-With-Automorphismᵉ Xᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-htpy-equivᵉ (automorphism-Type-With-Automorphismᵉ Xᵉ))

  is-equiv-equiv-eq-Type-With-Automorphismᵉ :
    ( Yᵉ : Type-With-Automorphismᵉ l1ᵉ) →
    is-equivᵉ (equiv-eq-Type-With-Automorphismᵉ Yᵉ)
  is-equiv-equiv-eq-Type-With-Automorphismᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Type-With-Automorphismᵉ
      equiv-eq-Type-With-Automorphismᵉ

  extensionality-Type-With-Automorphismᵉ :
    (Yᵉ : Type-With-Automorphismᵉ l1ᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Type-With-Automorphismᵉ Yᵉ) =
    equiv-eq-Type-With-Automorphismᵉ Yᵉ
  pr2ᵉ (extensionality-Type-With-Automorphismᵉ Yᵉ) =
    is-equiv-equiv-eq-Type-With-Automorphismᵉ Yᵉ

  eq-equiv-Type-With-Automorphismᵉ :
    (Yᵉ : Type-With-Automorphismᵉ l1ᵉ) → equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-Type-With-Automorphismᵉ Yᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Type-With-Automorphismᵉ Yᵉ)

module _
  {lᵉ : Level}
  (Xᵉ : Type-With-Automorphismᵉ lᵉ)
  (Yᵉ : Type-With-Automorphismᵉ lᵉ)
  (Zᵉ : Type-With-Automorphismᵉ lᵉ)
  where

  preserves-concat-equiv-eq-Type-With-Automorphismᵉ :
    (pᵉ : Xᵉ ＝ᵉ Yᵉ) (qᵉ : Yᵉ ＝ᵉ Zᵉ) →
    ( equiv-eq-Type-With-Automorphismᵉ Xᵉ Zᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ
    ( comp-equiv-Type-With-Automorphismᵉ Xᵉ Yᵉ Zᵉ
      ( equiv-eq-Type-With-Automorphismᵉ Yᵉ Zᵉ qᵉ)
      ( equiv-eq-Type-With-Automorphismᵉ Xᵉ Yᵉ pᵉ))
  preserves-concat-equiv-eq-Type-With-Automorphismᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-equiv-Type-With-Automorphismᵉ Xᵉ Zᵉ
        ( equiv-eq-Type-With-Automorphismᵉ Xᵉ Zᵉ qᵉ))
```