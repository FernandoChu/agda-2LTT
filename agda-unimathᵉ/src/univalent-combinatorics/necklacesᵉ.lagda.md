# Necklaces

```agda
module univalent-combinatorics.necklacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ

open import univalent-combinatorics.cyclic-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **necklace**ᵉ isᵉ anᵉ arrangementᵉ ofᵉ colouredᵉ beads,ᵉ i.e.,ᵉ itᵉ consistsᵉ ofᵉ aᵉ
[cyclicᵉ finiteᵉ type](univalent-combinatorics.cyclic-finite-types.mdᵉ) equippedᵉ
with aᵉ coloringᵉ ofᵉ theᵉ elements.ᵉ Twoᵉ necklacesᵉ areᵉ consideredᵉ theᵉ sameᵉ ifᵉ oneᵉ
canᵉ beᵉ obtainedᵉ fromᵉ theᵉ otherᵉ byᵉ rotating.ᵉ

## Definition

### Necklaces

```agda
necklaceᵉ : (lᵉ : Level) → ℕᵉ → ℕᵉ → UUᵉ (lsuc lᵉ)
necklaceᵉ lᵉ mᵉ nᵉ = Σᵉ (Cyclic-Typeᵉ lᵉ mᵉ) (λ Xᵉ → type-Cyclic-Typeᵉ mᵉ Xᵉ → Finᵉ nᵉ)

module _
  {lᵉ : Level} (mᵉ : ℕᵉ) (nᵉ : ℕᵉ) (Nᵉ : necklaceᵉ lᵉ mᵉ nᵉ)
  where

  cyclic-necklaceᵉ : Cyclic-Typeᵉ lᵉ mᵉ
  cyclic-necklaceᵉ = pr1ᵉ Nᵉ

  endo-necklaceᵉ : Type-With-Endomorphismᵉ lᵉ
  endo-necklaceᵉ = endo-Cyclic-Typeᵉ mᵉ cyclic-necklaceᵉ

  type-necklaceᵉ : UUᵉ lᵉ
  type-necklaceᵉ = type-Cyclic-Typeᵉ mᵉ cyclic-necklaceᵉ

  endomorphism-necklaceᵉ : type-necklaceᵉ → type-necklaceᵉ
  endomorphism-necklaceᵉ = endomorphism-Cyclic-Typeᵉ mᵉ cyclic-necklaceᵉ

  is-cyclic-endo-necklaceᵉ : is-cyclic-Type-With-Endomorphismᵉ mᵉ endo-necklaceᵉ
  is-cyclic-endo-necklaceᵉ = mere-equiv-endo-Cyclic-Typeᵉ mᵉ cyclic-necklaceᵉ

  colouring-necklaceᵉ : type-necklaceᵉ → Finᵉ nᵉ
  colouring-necklaceᵉ = pr2ᵉ Nᵉ
```

### Necklace patterns

```agda
necklace-patternᵉ : (lᵉ : Level) → ℕᵉ → ℕᵉ → UUᵉ (lsuc lᵉ)
necklace-patternᵉ lᵉ mᵉ nᵉ =
  Σᵉ ( Cyclic-Typeᵉ lᵉ mᵉ)
    ( λ Xᵉ → Σᵉ (UU-Finᵉ lzero nᵉ) (λ Cᵉ → type-Cyclic-Typeᵉ mᵉ Xᵉ → type-UU-Finᵉ nᵉ Cᵉ))
```

## Properties

### Characterization of the identity type

```agda
module _
  {l1ᵉ l2ᵉ : Level} (mᵉ nᵉ : ℕᵉ)
  where

  equiv-necklaceᵉ :
    (N1ᵉ : necklaceᵉ l1ᵉ mᵉ nᵉ) (N2ᵉ : necklaceᵉ l2ᵉ mᵉ nᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  equiv-necklaceᵉ N1ᵉ N2ᵉ =
    Σᵉ ( equiv-Cyclic-Typeᵉ mᵉ (cyclic-necklaceᵉ mᵉ nᵉ N1ᵉ) (cyclic-necklaceᵉ mᵉ nᵉ N2ᵉ))
      ( λ eᵉ →
        ( colouring-necklaceᵉ mᵉ nᵉ N1ᵉ) ~ᵉ
        ( ( colouring-necklaceᵉ mᵉ nᵉ N2ᵉ) ∘ᵉ
          ( map-equiv-Cyclic-Typeᵉ mᵉ
            ( cyclic-necklaceᵉ mᵉ nᵉ N1ᵉ)
            ( cyclic-necklaceᵉ mᵉ nᵉ N2ᵉ)
            ( eᵉ))))

module _
  {lᵉ : Level} (mᵉ nᵉ : ℕᵉ)
  where

  id-equiv-necklaceᵉ :
    (Nᵉ : necklaceᵉ lᵉ mᵉ nᵉ) → equiv-necklaceᵉ mᵉ nᵉ Nᵉ Nᵉ
  pr1ᵉ (id-equiv-necklaceᵉ Nᵉ) = id-equiv-Cyclic-Typeᵉ mᵉ (cyclic-necklaceᵉ mᵉ nᵉ Nᵉ)
  pr2ᵉ (id-equiv-necklaceᵉ Nᵉ) = refl-htpyᵉ

module _
  {lᵉ : Level} (mᵉ nᵉ : ℕᵉ)
  where

  extensionality-necklaceᵉ :
    (N1ᵉ N2ᵉ : necklaceᵉ lᵉ mᵉ nᵉ) → Idᵉ N1ᵉ N2ᵉ ≃ᵉ equiv-necklaceᵉ mᵉ nᵉ N1ᵉ N2ᵉ
  extensionality-necklaceᵉ N1ᵉ =
    extensionality-Σᵉ
      ( λ {Xᵉ} fᵉ eᵉ →
        ( colouring-necklaceᵉ mᵉ nᵉ N1ᵉ) ~ᵉ
        ( fᵉ ∘ᵉ map-equiv-Cyclic-Typeᵉ mᵉ (cyclic-necklaceᵉ mᵉ nᵉ N1ᵉ) Xᵉ eᵉ))
      ( id-equiv-Cyclic-Typeᵉ mᵉ (cyclic-necklaceᵉ mᵉ nᵉ N1ᵉ))
      ( refl-htpyᵉ)
      ( extensionality-Cyclic-Typeᵉ mᵉ (cyclic-necklaceᵉ mᵉ nᵉ N1ᵉ))
      ( λ fᵉ → equiv-funextᵉ)

  refl-extensionality-necklaceᵉ :
    (Nᵉ : necklaceᵉ lᵉ mᵉ nᵉ) →
    Idᵉ (map-equivᵉ (extensionality-necklaceᵉ Nᵉ Nᵉ) reflᵉ) (id-equiv-necklaceᵉ mᵉ nᵉ Nᵉ)
  refl-extensionality-necklaceᵉ Nᵉ = reflᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}