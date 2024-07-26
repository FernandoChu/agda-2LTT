# Unordered pairs of types

```agda
module foundation.unordered-pairs-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.2-element-typesᵉ
```

</details>

## Idea

Anᵉ unorderedᵉ pairᵉ ofᵉ typesᵉ isᵉ anᵉ unorderedᵉ pairᵉ ofᵉ elementsᵉ in aᵉ universeᵉ

## Definitions

### Unordered pairs of types

```agda
unordered-pair-typesᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
unordered-pair-typesᵉ lᵉ = unordered-pairᵉ (UUᵉ lᵉ)
```

### Equivalences of unordered pairs of types

```agda
equiv-unordered-pair-typesᵉ :
  {l1ᵉ l2ᵉ : Level} →
  unordered-pair-typesᵉ l1ᵉ → unordered-pair-typesᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
equiv-unordered-pair-typesᵉ Aᵉ Bᵉ =
  Σᵉ ( type-unordered-pairᵉ Aᵉ ≃ᵉ type-unordered-pairᵉ Bᵉ)
    ( λ eᵉ →
      (iᵉ : type-unordered-pairᵉ Aᵉ) →
      element-unordered-pairᵉ Aᵉ iᵉ ≃ᵉ element-unordered-pairᵉ Bᵉ (map-equivᵉ eᵉ iᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : unordered-pair-typesᵉ l1ᵉ) (Bᵉ : unordered-pair-typesᵉ l2ᵉ)
  (eᵉ : equiv-unordered-pair-typesᵉ Aᵉ Bᵉ)
  where

  equiv-type-equiv-unordered-pair-typesᵉ :
    type-unordered-pairᵉ Aᵉ ≃ᵉ type-unordered-pairᵉ Bᵉ
  equiv-type-equiv-unordered-pair-typesᵉ = pr1ᵉ eᵉ

  map-equiv-type-equiv-unordered-pair-typesᵉ :
    type-unordered-pairᵉ Aᵉ → type-unordered-pairᵉ Bᵉ
  map-equiv-type-equiv-unordered-pair-typesᵉ =
    map-equivᵉ equiv-type-equiv-unordered-pair-typesᵉ

  equiv-element-equiv-unordered-pair-typesᵉ :
    (iᵉ : type-unordered-pairᵉ Aᵉ) →
    ( element-unordered-pairᵉ Aᵉ iᵉ) ≃ᵉ
    ( element-unordered-pairᵉ Bᵉ (map-equiv-type-equiv-unordered-pair-typesᵉ iᵉ))
  equiv-element-equiv-unordered-pair-typesᵉ = pr2ᵉ eᵉ
```

## Properties

### Extensionality of unordered pairs of types

```agda
module _
  {lᵉ : Level} (Aᵉ : unordered-pair-typesᵉ lᵉ)
  where

  id-equiv-unordered-pair-typesᵉ : equiv-unordered-pair-typesᵉ Aᵉ Aᵉ
  pr1ᵉ id-equiv-unordered-pair-typesᵉ = id-equivᵉ
  pr2ᵉ id-equiv-unordered-pair-typesᵉ iᵉ = id-equivᵉ

  equiv-eq-unordered-pair-typesᵉ :
    (Bᵉ : unordered-pair-typesᵉ lᵉ) → Aᵉ ＝ᵉ Bᵉ → equiv-unordered-pair-typesᵉ Aᵉ Bᵉ
  equiv-eq-unordered-pair-typesᵉ .Aᵉ reflᵉ = id-equiv-unordered-pair-typesᵉ

  is-torsorial-equiv-unordered-pair-typesᵉ :
    is-torsorialᵉ (equiv-unordered-pair-typesᵉ Aᵉ)
  is-torsorial-equiv-unordered-pair-typesᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-2-Element-Typeᵉ (2-element-type-unordered-pairᵉ Aᵉ))
      ( pairᵉ (2-element-type-unordered-pairᵉ Aᵉ) id-equivᵉ)
      ( is-torsorial-equiv-famᵉ (element-unordered-pairᵉ Aᵉ))

  is-equiv-equiv-eq-unordered-pair-typesᵉ :
    (Bᵉ : unordered-pair-typesᵉ lᵉ) → is-equivᵉ (equiv-eq-unordered-pair-typesᵉ Bᵉ)
  is-equiv-equiv-eq-unordered-pair-typesᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-unordered-pair-typesᵉ
      equiv-eq-unordered-pair-typesᵉ

  extensionality-unordered-pair-typesᵉ :
    (Bᵉ : unordered-pair-typesᵉ lᵉ) → (Aᵉ ＝ᵉ Bᵉ) ≃ᵉ equiv-unordered-pair-typesᵉ Aᵉ Bᵉ
  pr1ᵉ (extensionality-unordered-pair-typesᵉ Bᵉ) =
    equiv-eq-unordered-pair-typesᵉ Bᵉ
  pr2ᵉ (extensionality-unordered-pair-typesᵉ Bᵉ) =
    is-equiv-equiv-eq-unordered-pair-typesᵉ Bᵉ
```