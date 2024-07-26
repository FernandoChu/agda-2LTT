# Unordered tuples of types

```agda
module foundation.unordered-tuples-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-tuplesᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Anᵉ unorderedᵉ tupleᵉ ofᵉ typesᵉ isᵉ anᵉ unorderedᵉ tupleᵉ ofᵉ elementsᵉ in aᵉ universeᵉ

## Definitions

### Unordered tuple of types

```agda
unordered-tuple-typesᵉ : (lᵉ : Level) → ℕᵉ → UUᵉ (lsuc lᵉ)
unordered-tuple-typesᵉ lᵉ nᵉ = unordered-tupleᵉ nᵉ (UUᵉ lᵉ)
```

### Equivalences of unordered pairs of types

```agda
equiv-unordered-tuple-typesᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) →
  unordered-tuple-typesᵉ l1ᵉ nᵉ → unordered-tuple-typesᵉ l2ᵉ nᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ =
  Σᵉ ( type-unordered-tupleᵉ nᵉ Aᵉ ≃ᵉ type-unordered-tupleᵉ nᵉ Bᵉ)
    ( λ eᵉ →
      (iᵉ : type-unordered-tupleᵉ nᵉ Aᵉ) →
      element-unordered-tupleᵉ nᵉ Aᵉ iᵉ ≃ᵉ
      element-unordered-tupleᵉ nᵉ Bᵉ (map-equivᵉ eᵉ iᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ)
  (Aᵉ : unordered-tuple-typesᵉ l1ᵉ nᵉ) (Bᵉ : unordered-tuple-typesᵉ l2ᵉ nᵉ)
  (eᵉ : equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ)
  where

  equiv-type-equiv-unordered-tuple-typesᵉ :
    type-unordered-tupleᵉ nᵉ Aᵉ ≃ᵉ type-unordered-tupleᵉ nᵉ Bᵉ
  equiv-type-equiv-unordered-tuple-typesᵉ = pr1ᵉ eᵉ

  map-equiv-type-equiv-unordered-tuple-typesᵉ :
    type-unordered-tupleᵉ nᵉ Aᵉ → type-unordered-tupleᵉ nᵉ Bᵉ
  map-equiv-type-equiv-unordered-tuple-typesᵉ =
    map-equivᵉ equiv-type-equiv-unordered-tuple-typesᵉ

  equiv-element-equiv-unordered-tuple-typesᵉ :
    (iᵉ : type-unordered-tupleᵉ nᵉ Aᵉ) →
    ( element-unordered-tupleᵉ nᵉ Aᵉ iᵉ) ≃ᵉ
    ( element-unordered-tupleᵉ nᵉ Bᵉ
      ( map-equiv-type-equiv-unordered-tuple-typesᵉ iᵉ))
  equiv-element-equiv-unordered-tuple-typesᵉ = pr2ᵉ eᵉ
```

## Properties

### Univalence for unordered pairs of types

```agda
module _
  {lᵉ : Level} {nᵉ : ℕᵉ} (Aᵉ : unordered-tuple-typesᵉ lᵉ nᵉ)
  where

  id-equiv-unordered-tuple-typesᵉ : equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Aᵉ
  pr1ᵉ id-equiv-unordered-tuple-typesᵉ = id-equivᵉ
  pr2ᵉ id-equiv-unordered-tuple-typesᵉ iᵉ = id-equivᵉ

  equiv-eq-unordered-tuple-typesᵉ :
    (Bᵉ : unordered-tuple-typesᵉ lᵉ nᵉ) → Aᵉ ＝ᵉ Bᵉ → equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ
  equiv-eq-unordered-tuple-typesᵉ .Aᵉ reflᵉ = id-equiv-unordered-tuple-typesᵉ

  is-torsorial-equiv-unordered-tuple-typesᵉ :
    is-torsorialᵉ (equiv-unordered-tuple-typesᵉ nᵉ Aᵉ)
  is-torsorial-equiv-unordered-tuple-typesᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-UU-Finᵉ {kᵉ = nᵉ} (type-unordered-tuple-UU-Finᵉ nᵉ Aᵉ))
      ( pairᵉ (type-unordered-tuple-UU-Finᵉ nᵉ Aᵉ) id-equivᵉ)
      ( is-torsorial-equiv-famᵉ (element-unordered-tupleᵉ nᵉ Aᵉ))

  is-equiv-equiv-eq-unordered-tuple-typesᵉ :
    (Bᵉ : unordered-tuple-typesᵉ lᵉ nᵉ) →
    is-equivᵉ (equiv-eq-unordered-tuple-typesᵉ Bᵉ)
  is-equiv-equiv-eq-unordered-tuple-typesᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-unordered-tuple-typesᵉ
      equiv-eq-unordered-tuple-typesᵉ

  extensionality-unordered-tuple-typesᵉ :
    (Bᵉ : unordered-tuple-typesᵉ lᵉ nᵉ) →
    (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ equiv-unordered-tuple-typesᵉ nᵉ Aᵉ Bᵉ
  pr1ᵉ (extensionality-unordered-tuple-typesᵉ Bᵉ) =
    equiv-eq-unordered-tuple-typesᵉ Bᵉ
  pr2ᵉ (extensionality-unordered-tuple-typesᵉ Bᵉ) =
    is-equiv-equiv-eq-unordered-tuple-typesᵉ Bᵉ
```