# Logical equivalences

```agda
module foundation.logical-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

{{#conceptᵉ "Logicalᵉ equivalences"ᵉ Agda=ᵉ}} betweenᵉ twoᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ consistᵉ
ofᵉ aᵉ mapᵉ `Aᵉ → B`ᵉ andᵉ aᵉ mapᵉ `Bᵉ → A`.ᵉ Theᵉ typeᵉ ofᵉ logicalᵉ equivalencesᵉ betweenᵉ
typesᵉ isᵉ theᵉ Curry-Howardᵉ interpretationᵉ ofᵉ logicalᵉ equivalencesᵉ betweenᵉ
[propositions](foundation-core.propositions.md).ᵉ

## Definition

### The structure on a map of being a logical equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  has-converseᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-converseᵉ fᵉ = Bᵉ → Aᵉ

  is-prop-has-converseᵉ :
    is-propᵉ Aᵉ → (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (has-converseᵉ fᵉ)
  is-prop-has-converseᵉ is-prop-Aᵉ fᵉ = is-prop-function-typeᵉ is-prop-Aᵉ

has-converse-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Propᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} → (type-Propᵉ Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
has-converse-Propᵉ Aᵉ fᵉ =
  ( has-converseᵉ fᵉ ,ᵉ
    is-prop-has-converseᵉ (is-prop-type-Propᵉ Aᵉ) fᵉ)
```

### Logical equivalences between types

```agda
iffᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
iffᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) has-converseᵉ

infix 6 _↔ᵉ_

_↔ᵉ_ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
_↔ᵉ_ = iffᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Hᵉ : Aᵉ ↔ᵉ Bᵉ)
  where

  forward-implicationᵉ : Aᵉ → Bᵉ
  forward-implicationᵉ = pr1ᵉ Hᵉ

  backward-implicationᵉ : Bᵉ → Aᵉ
  backward-implicationᵉ = pr2ᵉ Hᵉ
```

### Logical equivalences between propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  type-iff-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-iff-Propᵉ = type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ

  is-prop-iff-Propᵉ : is-propᵉ type-iff-Propᵉ
  is-prop-iff-Propᵉ =
    is-prop-productᵉ
      ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Qᵉ))
      ( is-prop-function-typeᵉ (is-prop-type-Propᵉ Pᵉ))

  iff-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ iff-Propᵉ = type-iff-Propᵉ
  pr2ᵉ iff-Propᵉ = is-prop-iff-Propᵉ

  infix 6 _⇔ᵉ_

  _⇔ᵉ_ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  _⇔ᵉ_ = iff-Propᵉ
```

### The identity logical equivalence

```agda
id-iffᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → Aᵉ ↔ᵉ Aᵉ
id-iffᵉ = (idᵉ ,ᵉ idᵉ)
```

### Composition of logical equivalences

```agda
infixr 15 _∘iffᵉ_

_∘iffᵉ_ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} →
  (Bᵉ ↔ᵉ Cᵉ) → (Aᵉ ↔ᵉ Bᵉ) → (Aᵉ ↔ᵉ Cᵉ)
pr1ᵉ ((g1ᵉ ,ᵉ g2ᵉ) ∘iffᵉ (f1ᵉ ,ᵉ f2ᵉ)) = g1ᵉ ∘ᵉ f1ᵉ
pr2ᵉ ((g1ᵉ ,ᵉ g2ᵉ) ∘iffᵉ (f1ᵉ ,ᵉ f2ᵉ)) = f2ᵉ ∘ᵉ g2ᵉ
```

### Inverting a logical equivalence

```agda
inv-iffᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ ↔ᵉ Bᵉ) → (Bᵉ ↔ᵉ Aᵉ)
pr1ᵉ (inv-iffᵉ (fᵉ ,ᵉ gᵉ)) = gᵉ
pr2ᵉ (inv-iffᵉ (fᵉ ,ᵉ gᵉ)) = fᵉ
```

## Properties

### Characterizing equality of logical equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  htpy-iffᵉ : (fᵉ gᵉ : Aᵉ ↔ᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-iffᵉ fᵉ gᵉ =
    ( forward-implicationᵉ fᵉ ~ᵉ forward-implicationᵉ gᵉ) ×ᵉ
    ( backward-implicationᵉ fᵉ ~ᵉ backward-implicationᵉ gᵉ)

  ext-iffᵉ : (fᵉ gᵉ : Aᵉ ↔ᵉ Bᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-iffᵉ fᵉ gᵉ
  ext-iffᵉ fᵉ gᵉ = equiv-productᵉ equiv-funextᵉ equiv-funextᵉ ∘eᵉ equiv-pair-eqᵉ fᵉ gᵉ

  refl-htpy-iffᵉ : (fᵉ : Aᵉ ↔ᵉ Bᵉ) → htpy-iffᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-iffᵉ fᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-iffᵉ fᵉ) = refl-htpyᵉ

  htpy-eq-iffᵉ : {fᵉ gᵉ : Aᵉ ↔ᵉ Bᵉ} → fᵉ ＝ᵉ gᵉ → htpy-iffᵉ fᵉ gᵉ
  htpy-eq-iffᵉ {fᵉ} {gᵉ} = map-equivᵉ (ext-iffᵉ fᵉ gᵉ)

  eq-htpy-iffᵉ : (fᵉ gᵉ : Aᵉ ↔ᵉ Bᵉ) → htpy-iffᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-iffᵉ fᵉ gᵉ = map-inv-equivᵉ (ext-iffᵉ fᵉ gᵉ)
```

### Logical equivalences between propositions induce equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  abstract
    is-equiv-has-converse-is-propᵉ :
      is-propᵉ Aᵉ → is-propᵉ Bᵉ → {fᵉ : Aᵉ → Bᵉ} → (Bᵉ → Aᵉ) → is-equivᵉ fᵉ
    is-equiv-has-converse-is-propᵉ is-prop-Aᵉ is-prop-Bᵉ {fᵉ} gᵉ =
      is-equiv-is-invertibleᵉ
        ( gᵉ)
        ( λ yᵉ → eq-is-propᵉ is-prop-Bᵉ)
        ( λ xᵉ → eq-is-propᵉ is-prop-Aᵉ)

  abstract
    equiv-iff-is-propᵉ : is-propᵉ Aᵉ → is-propᵉ Bᵉ → (Aᵉ → Bᵉ) → (Bᵉ → Aᵉ) → Aᵉ ≃ᵉ Bᵉ
    pr1ᵉ (equiv-iff-is-propᵉ is-prop-Aᵉ is-prop-Bᵉ fᵉ gᵉ) = fᵉ
    pr2ᵉ (equiv-iff-is-propᵉ is-prop-Aᵉ is-prop-Bᵉ fᵉ gᵉ) =
      is-equiv-has-converse-is-propᵉ is-prop-Aᵉ is-prop-Bᵉ gᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  abstract
    is-equiv-has-converseᵉ :
      {fᵉ : type-Propᵉ Pᵉ → type-Propᵉ Qᵉ} → (type-Propᵉ Qᵉ → type-Propᵉ Pᵉ) → is-equivᵉ fᵉ
    is-equiv-has-converseᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-prop-type-Propᵉ Pᵉ)
        ( is-prop-type-Propᵉ Qᵉ)

  equiv-iff'ᵉ : type-Propᵉ (Pᵉ ⇔ᵉ Qᵉ) → (type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ)
  pr1ᵉ (equiv-iff'ᵉ tᵉ) = forward-implicationᵉ tᵉ
  pr2ᵉ (equiv-iff'ᵉ tᵉ) =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-Propᵉ Pᵉ)
      ( is-prop-type-Propᵉ Qᵉ)
      ( backward-implicationᵉ tᵉ)

  equiv-iffᵉ :
    (type-Propᵉ Pᵉ → type-Propᵉ Qᵉ) → (type-Propᵉ Qᵉ → type-Propᵉ Pᵉ) →
    type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ
  equiv-iffᵉ fᵉ gᵉ = equiv-iff'ᵉ (fᵉ ,ᵉ gᵉ)
```

### Equivalences are logical equivalences

```agda
iff-equivᵉ : {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ ≃ᵉ Bᵉ) → (Aᵉ ↔ᵉ Bᵉ)
pr1ᵉ (iff-equivᵉ eᵉ) = map-equivᵉ eᵉ
pr2ᵉ (iff-equivᵉ eᵉ) = map-inv-equivᵉ eᵉ

is-injective-iff-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → is-injectiveᵉ (iff-equivᵉ {Aᵉ = Aᵉ} {Bᵉ})
is-injective-iff-equivᵉ pᵉ = eq-htpy-equivᵉ (pr1ᵉ (htpy-eq-iffᵉ pᵉ))

compute-fiber-iff-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} ((fᵉ ,ᵉ gᵉ) : Aᵉ ↔ᵉ Bᵉ) →
  fiberᵉ (iff-equivᵉ) (fᵉ ,ᵉ gᵉ) ≃ᵉ Σᵉ (is-equivᵉ fᵉ) (λ f'ᵉ → map-inv-is-equivᵉ f'ᵉ ~ᵉ gᵉ)
compute-fiber-iff-equivᵉ {Aᵉ = Aᵉ} {Bᵉ} (fᵉ ,ᵉ gᵉ) =
  ( equiv-totᵉ (λ _ → equiv-funextᵉ)) ∘eᵉ
  ( left-unit-law-Σ-is-contrᵉ (is-torsorial-Id'ᵉ fᵉ) (fᵉ ,ᵉ reflᵉ)) ∘eᵉ
  ( inv-associative-Σᵉ (Aᵉ → Bᵉ) (_＝ᵉ fᵉ) _) ∘eᵉ
  ( equiv-totᵉ (λ _ → equiv-left-swap-Σᵉ)) ∘eᵉ
  ( associative-Σᵉ (Aᵉ → Bᵉ) _ _) ∘eᵉ
  ( equiv-totᵉ (λ eᵉ → equiv-pair-eqᵉ (iff-equivᵉ eᵉ) (fᵉ ,ᵉ gᵉ)))
```

### Two equal propositions are logically equivalent

```agda
iff-eqᵉ : {l1ᵉ : Level} {Pᵉ Qᵉ : Propᵉ l1ᵉ} → Pᵉ ＝ᵉ Qᵉ → type-Propᵉ (Pᵉ ⇔ᵉ Qᵉ)
pr1ᵉ (iff-eqᵉ reflᵉ) = idᵉ
pr2ᵉ (iff-eqᵉ reflᵉ) = idᵉ
```

### Logical equivalence of propositions is equivalent to equivalence of propositions

```agda
abstract
  is-equiv-equiv-iffᵉ :
    {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) →
    is-equivᵉ (equiv-iff'ᵉ Pᵉ Qᵉ)
  is-equiv-equiv-iffᵉ Pᵉ Qᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-iff-Propᵉ Pᵉ Qᵉ)
      ( is-prop-type-equiv-Propᵉ Pᵉ Qᵉ)
      ( iff-equivᵉ)

equiv-equiv-iffᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ) →
  (type-Propᵉ Pᵉ ↔ᵉ type-Propᵉ Qᵉ) ≃ᵉ (type-Propᵉ Pᵉ ≃ᵉ type-Propᵉ Qᵉ)
pr1ᵉ (equiv-equiv-iffᵉ Pᵉ Qᵉ) = equiv-iff'ᵉ Pᵉ Qᵉ
pr2ᵉ (equiv-equiv-iffᵉ Pᵉ Qᵉ) = is-equiv-equiv-iffᵉ Pᵉ Qᵉ
```

## Logical equivalences between dependent function types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  where

  iff-Π-iff-familyᵉ : ((iᵉ : Iᵉ) → Aᵉ iᵉ ↔ᵉ Bᵉ iᵉ) → ((iᵉ : Iᵉ) → Aᵉ iᵉ) ↔ᵉ ((iᵉ : Iᵉ) → Bᵉ iᵉ)
  pr1ᵉ (iff-Π-iff-familyᵉ eᵉ) aᵉ iᵉ = forward-implicationᵉ (eᵉ iᵉ) (aᵉ iᵉ)
  pr2ᵉ (iff-Π-iff-familyᵉ eᵉ) bᵉ iᵉ = backward-implicationᵉ (eᵉ iᵉ) (bᵉ iᵉ)
```

## Reasoning with logical equivalences

Logicalᵉ equivalencesᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ in theᵉ followingᵉ
wayᵉ:

```text
logical-equivalence-reasoningᵉ
  Xᵉ ↔ᵉ Yᵉ byᵉ equiv-1ᵉ
    ↔ᵉ Zᵉ byᵉ equiv-2ᵉ
    ↔ᵉ Vᵉ byᵉ equiv-3ᵉ
```

```agda
infixl 1 logical-equivalence-reasoningᵉ_
infixl 0 step-logical-equivalence-reasoningᵉ

logical-equivalence-reasoningᵉ_ :
  {l1ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) → Xᵉ ↔ᵉ Xᵉ
pr1ᵉ (logical-equivalence-reasoningᵉ Xᵉ) = idᵉ
pr2ᵉ (logical-equivalence-reasoningᵉ Xᵉ) = idᵉ

step-logical-equivalence-reasoningᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (Xᵉ ↔ᵉ Yᵉ) → (Zᵉ : UUᵉ l3ᵉ) → (Yᵉ ↔ᵉ Zᵉ) → (Xᵉ ↔ᵉ Zᵉ)
step-logical-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = fᵉ ∘iffᵉ eᵉ

syntax step-logical-equivalence-reasoningᵉ eᵉ Zᵉ fᵉ = eᵉ ↔ᵉ Zᵉ byᵉ fᵉ
```