# Complements of isolated elements of finite types

```agda
module univalent-combinatorics.complements-isolated-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.identity-typesᵉ
open import foundation.isolated-elementsᵉ
open import foundation.maybeᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Forᵉ anyᵉ elementᵉ `x`ᵉ in aᵉ [finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ)
`X`ᵉ ofᵉ [cardinality](set-theory.cardinalities.mdᵉ) `n+1`,ᵉ weᵉ canᵉ constructᵉ itsᵉ
**complement**,ᵉ whichᵉ isᵉ aᵉ typeᵉ ofᵉ cardinalityᵉ `n`.ᵉ

## Definition

### The complement of a element in a `k`-element type of arbitrary universe level

```agda
isolated-element-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ (succ-ℕᵉ kᵉ)) →
  type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ →
  isolated-elementᵉ (type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ)
pr1ᵉ (isolated-element-UU-Finᵉ kᵉ Xᵉ xᵉ) = xᵉ
pr2ᵉ (isolated-element-UU-Finᵉ kᵉ Xᵉ xᵉ) =
  has-decidable-equality-has-cardinalityᵉ
    ( succ-ℕᵉ kᵉ)
    ( has-cardinality-type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ)
    ( xᵉ)

type-complement-element-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) →
  Σᵉ (UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)) (type-UU-Finᵉ (succ-ℕᵉ kᵉ)) → UUᵉ l1ᵉ
type-complement-element-UU-Finᵉ kᵉ (Xᵉ ,ᵉ xᵉ) =
  complement-isolated-elementᵉ
    ( type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ)
    ( isolated-element-UU-Finᵉ kᵉ Xᵉ xᵉ)

equiv-maybe-structure-element-UU-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Xᵉ : UU-Finᵉ lᵉ (succ-ℕᵉ kᵉ)) →
  (xᵉ : type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ) →
  Maybeᵉ (type-complement-element-UU-Finᵉ kᵉ (pairᵉ Xᵉ xᵉ)) ≃ᵉ
  type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ
equiv-maybe-structure-element-UU-Finᵉ kᵉ Xᵉ xᵉ =
  equiv-maybe-structure-isolated-elementᵉ
    ( type-UU-Finᵉ (succ-ℕᵉ kᵉ) Xᵉ)
    ( isolated-element-UU-Finᵉ kᵉ Xᵉ xᵉ)

has-cardinality-type-complement-element-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ)
  (Xᵉ : Σᵉ (UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)) (type-UU-Finᵉ (succ-ℕᵉ kᵉ))) →
  has-cardinalityᵉ kᵉ (type-complement-element-UU-Finᵉ kᵉ Xᵉ)
has-cardinality-type-complement-element-UU-Finᵉ kᵉ (pairᵉ (pairᵉ Xᵉ Hᵉ) xᵉ) =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( has-cardinality-Propᵉ kᵉ
      ( type-complement-element-UU-Finᵉ kᵉ (pairᵉ (pairᵉ Xᵉ Hᵉ) xᵉ)))
    ( λ eᵉ →
      unit-trunc-Propᵉ
        ( equiv-equiv-Maybeᵉ
          ( ( inv-equivᵉ
              ( equiv-maybe-structure-element-UU-Finᵉ kᵉ (pairᵉ Xᵉ Hᵉ) xᵉ)) ∘eᵉ
            ( eᵉ))))

complement-element-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) →
  Σᵉ (UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)) (type-UU-Finᵉ (succ-ℕᵉ kᵉ)) →
  UU-Finᵉ l1ᵉ kᵉ
pr1ᵉ (complement-element-UU-Finᵉ kᵉ Tᵉ) =
  type-complement-element-UU-Finᵉ kᵉ Tᵉ
pr2ᵉ (complement-element-UU-Finᵉ kᵉ Tᵉ) =
  has-cardinality-type-complement-element-UU-Finᵉ kᵉ Tᵉ

inclusion-complement-element-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ)
  (Xᵉ : Σᵉ (UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)) (type-UU-Finᵉ (succ-ℕᵉ kᵉ))) →
  type-complement-element-UU-Finᵉ kᵉ Xᵉ → type-UU-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ Xᵉ)
inclusion-complement-element-UU-Finᵉ kᵉ Xᵉ xᵉ = pr1ᵉ xᵉ
```

### The action of equivalences on complements of isolated points

```agda
equiv-complement-element-UU-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ)
  (Xᵉ Yᵉ : Σᵉ (UU-Finᵉ l1ᵉ (succ-ℕᵉ kᵉ)) (type-UU-Finᵉ (succ-ℕᵉ kᵉ))) →
  (eᵉ : equiv-UU-Finᵉ (succ-ℕᵉ kᵉ) (pr1ᵉ Xᵉ) (pr1ᵉ Yᵉ))
  (pᵉ : Idᵉ (map-equivᵉ eᵉ (pr2ᵉ Xᵉ)) (pr2ᵉ Yᵉ)) →
  equiv-UU-Finᵉ kᵉ
    ( complement-element-UU-Finᵉ kᵉ Xᵉ)
    ( complement-element-UU-Finᵉ kᵉ Yᵉ)
equiv-complement-element-UU-Finᵉ
  kᵉ Sᵉ Tᵉ eᵉ pᵉ =
  equiv-complement-isolated-elementᵉ eᵉ
    ( pairᵉ xᵉ (λ x'ᵉ → has-decidable-equality-has-cardinalityᵉ (succ-ℕᵉ kᵉ) Hᵉ xᵉ x'ᵉ))
    ( pairᵉ yᵉ (λ y'ᵉ → has-decidable-equality-has-cardinalityᵉ (succ-ℕᵉ kᵉ) Kᵉ yᵉ y'ᵉ))
    ( pᵉ)
  where
  Hᵉ = pr2ᵉ (pr1ᵉ Sᵉ)
  xᵉ = pr2ᵉ Sᵉ
  Kᵉ = pr2ᵉ (pr1ᵉ Tᵉ)
  yᵉ = pr2ᵉ Tᵉ
```

## Properties

### The map from a pointed `k+1`-element type to the complement of the element is an equivalence

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#744](https://github.com/UniMath/agda-unimath/issues/744ᵉ)