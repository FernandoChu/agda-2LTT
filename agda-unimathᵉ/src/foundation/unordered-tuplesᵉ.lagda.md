# Unordered `n`-tuples of elements in a type

```agda
module foundation.unordered-tuplesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.setsᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.complements-isolated-elementsᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ **unorderedᵉ `n`-tuple**ᵉ ofᵉ elementsᵉ ofᵉ aᵉ typeᵉ `A`ᵉ consistsᵉ ofᵉ anᵉ `n`-elementᵉ
setᵉ `X`ᵉ equippedᵉ with aᵉ mapᵉ `Xᵉ → A`.ᵉ

## Definition

```agda
unordered-tupleᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) (Aᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
unordered-tupleᵉ nᵉ Aᵉ = Σᵉ (UU-Finᵉ lzero nᵉ) (λ Xᵉ → type-UU-Finᵉ nᵉ Xᵉ → Aᵉ)

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} (tᵉ : unordered-tupleᵉ nᵉ Aᵉ)
  where

  type-unordered-tuple-UU-Finᵉ : UU-Finᵉ lzero nᵉ
  type-unordered-tuple-UU-Finᵉ = pr1ᵉ tᵉ

  type-unordered-tupleᵉ : UUᵉ lzero
  type-unordered-tupleᵉ = type-UU-Finᵉ nᵉ type-unordered-tuple-UU-Finᵉ

  has-cardinality-type-unordered-tupleᵉ : has-cardinalityᵉ nᵉ type-unordered-tupleᵉ
  has-cardinality-type-unordered-tupleᵉ =
    has-cardinality-type-UU-Finᵉ nᵉ type-unordered-tuple-UU-Finᵉ

  is-set-type-unordered-tupleᵉ : is-setᵉ type-unordered-tupleᵉ
  is-set-type-unordered-tupleᵉ =
    is-set-has-cardinalityᵉ nᵉ has-cardinality-type-unordered-tupleᵉ

  has-decidable-equality-type-unordered-tupleᵉ :
    has-decidable-equalityᵉ type-unordered-tupleᵉ
  has-decidable-equality-type-unordered-tupleᵉ =
    has-decidable-equality-has-cardinalityᵉ nᵉ
      has-cardinality-type-unordered-tupleᵉ

  element-unordered-tupleᵉ : type-unordered-tupleᵉ → Aᵉ
  element-unordered-tupleᵉ = pr2ᵉ tᵉ
```

### Unordered tuples away from an index

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} (tᵉ : unordered-tupleᵉ (succ-ℕᵉ nᵉ) Aᵉ)
  (iᵉ : type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) tᵉ)
  where

  type-complement-point-unordered-tuple-UU-Finᵉ : UU-Finᵉ lzero nᵉ
  type-complement-point-unordered-tuple-UU-Finᵉ =
    complement-element-UU-Finᵉ nᵉ
      ( pairᵉ (type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) tᵉ) iᵉ)

  type-complement-point-unordered-tupleᵉ : UUᵉ lzero
  type-complement-point-unordered-tupleᵉ =
    type-UU-Finᵉ nᵉ type-complement-point-unordered-tuple-UU-Finᵉ

  inclusion-complement-point-unordered-tupleᵉ :
    type-complement-point-unordered-tupleᵉ → type-unordered-tupleᵉ (succ-ℕᵉ nᵉ) tᵉ
  inclusion-complement-point-unordered-tupleᵉ =
    inclusion-complement-element-UU-Finᵉ nᵉ
      ( pairᵉ (type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) tᵉ) iᵉ)

  unordered-tuple-complement-point-type-unordered-tupleᵉ :
    unordered-tupleᵉ nᵉ Aᵉ
  pr1ᵉ unordered-tuple-complement-point-type-unordered-tupleᵉ =
    complement-element-UU-Finᵉ nᵉ
      ( pairᵉ (type-unordered-tuple-UU-Finᵉ (succ-ℕᵉ nᵉ) tᵉ) iᵉ)
  pr2ᵉ unordered-tuple-complement-point-type-unordered-tupleᵉ =
    ( element-unordered-tupleᵉ (succ-ℕᵉ nᵉ) tᵉ) ∘ᵉ
    ( inclusion-complement-point-unordered-tupleᵉ)
```

### Standard unordered tuples

```agda
standard-unordered-tupleᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ} (fᵉ : Finᵉ nᵉ → Aᵉ) → unordered-tupleᵉ nᵉ Aᵉ
pr1ᵉ (standard-unordered-tupleᵉ nᵉ fᵉ) = Fin-UU-Fin'ᵉ nᵉ
pr2ᵉ (standard-unordered-tupleᵉ nᵉ fᵉ) = fᵉ
```

## Properties

### Equality of unordered tuples

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ lᵉ}
  where

  Eq-unordered-tupleᵉ : unordered-tupleᵉ nᵉ Aᵉ → unordered-tupleᵉ nᵉ Aᵉ → UUᵉ lᵉ
  Eq-unordered-tupleᵉ xᵉ yᵉ =
    Σᵉ ( type-unordered-tupleᵉ nᵉ xᵉ ≃ᵉ type-unordered-tupleᵉ nᵉ yᵉ)
      ( λ eᵉ →
        ( element-unordered-tupleᵉ nᵉ xᵉ) ~ᵉ
        ( element-unordered-tupleᵉ nᵉ yᵉ ∘ᵉ map-equivᵉ eᵉ))

  refl-Eq-unordered-tupleᵉ :
    (xᵉ : unordered-tupleᵉ nᵉ Aᵉ) → Eq-unordered-tupleᵉ xᵉ xᵉ
  pr1ᵉ (refl-Eq-unordered-tupleᵉ xᵉ) = id-equivᵉ
  pr2ᵉ (refl-Eq-unordered-tupleᵉ xᵉ) = refl-htpyᵉ

  Eq-eq-unordered-tupleᵉ :
    (xᵉ yᵉ : unordered-tupleᵉ nᵉ Aᵉ) → xᵉ ＝ᵉ yᵉ → Eq-unordered-tupleᵉ xᵉ yᵉ
  Eq-eq-unordered-tupleᵉ xᵉ .xᵉ reflᵉ = refl-Eq-unordered-tupleᵉ xᵉ

  is-torsorial-Eq-unordered-tupleᵉ :
    (xᵉ : unordered-tupleᵉ nᵉ Aᵉ) → is-torsorialᵉ (Eq-unordered-tupleᵉ xᵉ)
  is-torsorial-Eq-unordered-tupleᵉ xᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-UU-Finᵉ {kᵉ = nᵉ} (type-unordered-tuple-UU-Finᵉ nᵉ xᵉ))
      ( pairᵉ (type-unordered-tuple-UU-Finᵉ nᵉ xᵉ) id-equivᵉ)
      ( is-torsorial-htpyᵉ (element-unordered-tupleᵉ nᵉ xᵉ))

  is-equiv-Eq-eq-unordered-tupleᵉ :
    (xᵉ yᵉ : unordered-tupleᵉ nᵉ Aᵉ) → is-equivᵉ (Eq-eq-unordered-tupleᵉ xᵉ yᵉ)
  is-equiv-Eq-eq-unordered-tupleᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-unordered-tupleᵉ xᵉ)
      ( Eq-eq-unordered-tupleᵉ xᵉ)

  extensionality-unordered-tupleᵉ :
    (xᵉ yᵉ : unordered-tupleᵉ nᵉ Aᵉ) → (xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-unordered-tupleᵉ xᵉ yᵉ
  pr1ᵉ (extensionality-unordered-tupleᵉ xᵉ yᵉ) = Eq-eq-unordered-tupleᵉ xᵉ yᵉ
  pr2ᵉ (extensionality-unordered-tupleᵉ xᵉ yᵉ) = is-equiv-Eq-eq-unordered-tupleᵉ xᵉ yᵉ

  eq-Eq-unordered-tupleᵉ :
    (xᵉ yᵉ : unordered-tupleᵉ nᵉ Aᵉ) → Eq-unordered-tupleᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-Eq-unordered-tupleᵉ xᵉ yᵉ =
    map-inv-is-equivᵉ (is-equiv-Eq-eq-unordered-tupleᵉ xᵉ yᵉ)

  is-retraction-eq-Eq-unordered-tupleᵉ :
    (xᵉ yᵉ : unordered-tupleᵉ nᵉ Aᵉ) →
    (eq-Eq-unordered-tupleᵉ xᵉ yᵉ ∘ᵉ Eq-eq-unordered-tupleᵉ xᵉ yᵉ) ~ᵉ idᵉ
  is-retraction-eq-Eq-unordered-tupleᵉ xᵉ yᵉ =
    is-retraction-map-inv-is-equivᵉ (is-equiv-Eq-eq-unordered-tupleᵉ xᵉ yᵉ)
```

### Functoriality of unordered tuples

```agda
map-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  unordered-tupleᵉ nᵉ Aᵉ → unordered-tupleᵉ nᵉ Bᵉ
pr1ᵉ (map-unordered-tupleᵉ nᵉ fᵉ tᵉ) = type-unordered-tuple-UU-Finᵉ nᵉ tᵉ
pr2ᵉ (map-unordered-tupleᵉ nᵉ fᵉ tᵉ) = fᵉ ∘ᵉ element-unordered-tupleᵉ nᵉ tᵉ

preserves-comp-map-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
  map-unordered-tupleᵉ nᵉ (gᵉ ∘ᵉ fᵉ) ~ᵉ
  (map-unordered-tupleᵉ nᵉ gᵉ ∘ᵉ map-unordered-tupleᵉ nᵉ fᵉ)
preserves-comp-map-unordered-tupleᵉ nᵉ gᵉ fᵉ pᵉ = reflᵉ

preserves-id-map-unordered-tupleᵉ :
  {l1ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} →
  map-unordered-tupleᵉ nᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
preserves-id-map-unordered-tupleᵉ nᵉ = refl-htpyᵉ

htpy-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
  (fᵉ ~ᵉ gᵉ) → (map-unordered-tupleᵉ nᵉ fᵉ ~ᵉ map-unordered-tupleᵉ nᵉ gᵉ)
htpy-unordered-tupleᵉ nᵉ {fᵉ = fᵉ} {gᵉ = gᵉ} Hᵉ tᵉ =
  eq-Eq-unordered-tupleᵉ nᵉ
    ( map-unordered-tupleᵉ nᵉ fᵉ tᵉ)
    ( map-unordered-tupleᵉ nᵉ gᵉ tᵉ)
    ( pairᵉ id-equivᵉ (Hᵉ ·rᵉ element-unordered-tupleᵉ nᵉ tᵉ))

preserves-refl-htpy-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  htpy-unordered-tupleᵉ nᵉ (refl-htpyᵉ {fᵉ = fᵉ}) ~ᵉ refl-htpyᵉ
preserves-refl-htpy-unordered-tupleᵉ nᵉ fᵉ pᵉ =
  is-retraction-eq-Eq-unordered-tupleᵉ nᵉ
    ( map-unordered-tupleᵉ nᵉ fᵉ pᵉ)
    ( map-unordered-tupleᵉ nᵉ fᵉ pᵉ)
    ( reflᵉ)

equiv-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (unordered-tupleᵉ nᵉ Aᵉ ≃ᵉ unordered-tupleᵉ nᵉ Bᵉ)
equiv-unordered-tupleᵉ nᵉ eᵉ = equiv-totᵉ (λ Xᵉ → equiv-postcompᵉ (type-UU-Finᵉ nᵉ Xᵉ) eᵉ)

map-equiv-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (Aᵉ ≃ᵉ Bᵉ) → (unordered-tupleᵉ nᵉ Aᵉ → unordered-tupleᵉ nᵉ Bᵉ)
map-equiv-unordered-tupleᵉ nᵉ eᵉ = map-equivᵉ (equiv-unordered-tupleᵉ nᵉ eᵉ)

is-equiv-map-equiv-unordered-tupleᵉ :
  {l1ᵉ l2ᵉ : Level} (nᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-equivᵉ (map-equiv-unordered-tupleᵉ nᵉ eᵉ)
is-equiv-map-equiv-unordered-tupleᵉ nᵉ eᵉ =
  is-equiv-map-equivᵉ (equiv-unordered-tupleᵉ nᵉ eᵉ)
```