# The booleans

```agda
module foundation.booleansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.involutionsᵉ
open import foundation.negated-equalityᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ **booleans**ᵉ isᵉ aᵉ
[2-elementᵉ type](univalent-combinatorics.2-element-types.mdᵉ) with elementsᵉ
`trueᵉ falseᵉ : bool`,ᵉ whichᵉ isᵉ usedᵉ forᵉ reasoningᵉ with
[decidableᵉ propositions](foundation-core.decidable-propositions.md).ᵉ

## Definition

### The booleans

```agda
data boolᵉ : UUᵉ lzero where
  trueᵉ falseᵉ : boolᵉ




```

### The induction principle of the booleans

```agda
module _
  {lᵉ : Level} (Pᵉ : boolᵉ → UUᵉ lᵉ)
  where

  ind-boolᵉ : Pᵉ trueᵉ → Pᵉ falseᵉ → (bᵉ : boolᵉ) → Pᵉ bᵉ
  ind-boolᵉ ptᵉ pfᵉ trueᵉ = ptᵉ
  ind-boolᵉ ptᵉ pfᵉ falseᵉ = pfᵉ
```

### The `if_then_else` function

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  if_then_elseᵉ_ : boolᵉ → Aᵉ → Aᵉ → Aᵉ
  ifᵉ trueᵉ thenᵉ xᵉ elseᵉ yᵉ = xᵉ
  ifᵉ falseᵉ thenᵉ xᵉ elseᵉ yᵉ = yᵉ
```

### Raising universe levels of the booleans

```agda
raise-boolᵉ : (lᵉ : Level) → UUᵉ lᵉ
raise-boolᵉ lᵉ = raiseᵉ lᵉ boolᵉ

raise-trueᵉ : (lᵉ : Level) → raise-boolᵉ lᵉ
raise-trueᵉ lᵉ = map-raiseᵉ trueᵉ

raise-falseᵉ : (lᵉ : Level) → raise-boolᵉ lᵉ
raise-falseᵉ lᵉ = map-raiseᵉ falseᵉ

compute-raise-boolᵉ : (lᵉ : Level) → boolᵉ ≃ᵉ raise-boolᵉ lᵉ
compute-raise-boolᵉ lᵉ = compute-raiseᵉ lᵉ boolᵉ
```

### The standard propositions associated to the constructors of bool

```agda
prop-boolᵉ : boolᵉ → Propᵉ lzero
prop-boolᵉ trueᵉ = unit-Propᵉ
prop-boolᵉ falseᵉ = empty-Propᵉ

type-prop-boolᵉ : boolᵉ → UUᵉ lzero
type-prop-boolᵉ = type-Propᵉ ∘ᵉ prop-boolᵉ
```

### Equality on the booleans

```agda
Eq-boolᵉ : boolᵉ → boolᵉ → UUᵉ lzero
Eq-boolᵉ trueᵉ trueᵉ = unitᵉ
Eq-boolᵉ trueᵉ falseᵉ = emptyᵉ
Eq-boolᵉ falseᵉ trueᵉ = emptyᵉ
Eq-boolᵉ falseᵉ falseᵉ = unitᵉ

refl-Eq-boolᵉ : (xᵉ : boolᵉ) → Eq-boolᵉ xᵉ xᵉ
refl-Eq-boolᵉ trueᵉ = starᵉ
refl-Eq-boolᵉ falseᵉ = starᵉ

Eq-eq-boolᵉ :
  {xᵉ yᵉ : boolᵉ} → xᵉ ＝ᵉ yᵉ → Eq-boolᵉ xᵉ yᵉ
Eq-eq-boolᵉ {xᵉ = xᵉ} reflᵉ = refl-Eq-boolᵉ xᵉ

eq-Eq-boolᵉ :
  {xᵉ yᵉ : boolᵉ} → Eq-boolᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-boolᵉ {trueᵉ} {trueᵉ} starᵉ = reflᵉ
eq-Eq-boolᵉ {falseᵉ} {falseᵉ} starᵉ = reflᵉ

neq-false-true-boolᵉ : falseᵉ ≠ᵉ trueᵉ
neq-false-true-boolᵉ ()

neq-true-false-boolᵉ : trueᵉ ≠ᵉ falseᵉ
neq-true-false-boolᵉ ()
```

## Structure

### The boolean operators

```agda
neg-boolᵉ : boolᵉ → boolᵉ
neg-boolᵉ trueᵉ = falseᵉ
neg-boolᵉ falseᵉ = trueᵉ

conjunction-boolᵉ : boolᵉ → boolᵉ → boolᵉ
conjunction-boolᵉ trueᵉ trueᵉ = trueᵉ
conjunction-boolᵉ trueᵉ falseᵉ = falseᵉ
conjunction-boolᵉ falseᵉ trueᵉ = falseᵉ
conjunction-boolᵉ falseᵉ falseᵉ = falseᵉ

disjunction-boolᵉ : boolᵉ → boolᵉ → boolᵉ
disjunction-boolᵉ trueᵉ trueᵉ = trueᵉ
disjunction-boolᵉ trueᵉ falseᵉ = trueᵉ
disjunction-boolᵉ falseᵉ trueᵉ = trueᵉ
disjunction-boolᵉ falseᵉ falseᵉ = falseᵉ

implication-boolᵉ : boolᵉ → boolᵉ → boolᵉ
implication-boolᵉ trueᵉ trueᵉ = trueᵉ
implication-boolᵉ trueᵉ falseᵉ = falseᵉ
implication-boolᵉ falseᵉ trueᵉ = trueᵉ
implication-boolᵉ falseᵉ falseᵉ = trueᵉ
```

## Properties

### The booleans are a set

```agda
abstract
  is-prop-Eq-boolᵉ : (xᵉ yᵉ : boolᵉ) → is-propᵉ (Eq-boolᵉ xᵉ yᵉ)
  is-prop-Eq-boolᵉ trueᵉ trueᵉ = is-prop-unitᵉ
  is-prop-Eq-boolᵉ trueᵉ falseᵉ = is-prop-emptyᵉ
  is-prop-Eq-boolᵉ falseᵉ trueᵉ = is-prop-emptyᵉ
  is-prop-Eq-boolᵉ falseᵉ falseᵉ = is-prop-unitᵉ

abstract
  is-set-boolᵉ : is-setᵉ boolᵉ
  is-set-boolᵉ =
    is-set-prop-in-idᵉ
      ( Eq-boolᵉ)
      ( is-prop-Eq-boolᵉ)
      ( refl-Eq-boolᵉ)
      ( λ xᵉ yᵉ → eq-Eq-boolᵉ)

bool-Setᵉ : Setᵉ lzero
pr1ᵉ bool-Setᵉ = boolᵉ
pr2ᵉ bool-Setᵉ = is-set-boolᵉ
```

### The type of booleans is equivalent to `Fin 2`

```agda
bool-Fin-two-ℕᵉ : Finᵉ 2 → boolᵉ
bool-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) = trueᵉ
bool-Fin-two-ℕᵉ (inrᵉ starᵉ) = falseᵉ

Fin-two-ℕ-boolᵉ : boolᵉ → Finᵉ 2
Fin-two-ℕ-boolᵉ trueᵉ = inlᵉ (inrᵉ starᵉ)
Fin-two-ℕ-boolᵉ falseᵉ = inrᵉ starᵉ

abstract
  is-retraction-Fin-two-ℕ-boolᵉ : Fin-two-ℕ-boolᵉ ∘ᵉ bool-Fin-two-ℕᵉ ~ᵉ idᵉ
  is-retraction-Fin-two-ℕ-boolᵉ (inlᵉ (inrᵉ starᵉ)) = reflᵉ
  is-retraction-Fin-two-ℕ-boolᵉ (inrᵉ starᵉ) = reflᵉ

abstract
  is-section-Fin-two-ℕ-boolᵉ : bool-Fin-two-ℕᵉ ∘ᵉ Fin-two-ℕ-boolᵉ ~ᵉ idᵉ
  is-section-Fin-two-ℕ-boolᵉ trueᵉ = reflᵉ
  is-section-Fin-two-ℕ-boolᵉ falseᵉ = reflᵉ

equiv-bool-Fin-two-ℕᵉ : Finᵉ 2 ≃ᵉ boolᵉ
pr1ᵉ equiv-bool-Fin-two-ℕᵉ = bool-Fin-two-ℕᵉ
pr2ᵉ equiv-bool-Fin-two-ℕᵉ =
  is-equiv-is-invertibleᵉ
    ( Fin-two-ℕ-boolᵉ)
    ( is-section-Fin-two-ℕ-boolᵉ)
    ( is-retraction-Fin-two-ℕ-boolᵉ)
```

### The type of booleans is finite

```agda
is-finite-boolᵉ : is-finiteᵉ boolᵉ
is-finite-boolᵉ = is-finite-equivᵉ equiv-bool-Fin-two-ℕᵉ (is-finite-Finᵉ 2ᵉ)

bool-𝔽ᵉ : 𝔽ᵉ lzero
pr1ᵉ bool-𝔽ᵉ = boolᵉ
pr2ᵉ bool-𝔽ᵉ = is-finite-boolᵉ
```

### Boolean negation has no fixed points

```agda
neq-neg-boolᵉ : (bᵉ : boolᵉ) → bᵉ ≠ᵉ neg-boolᵉ bᵉ
neq-neg-boolᵉ trueᵉ ()
neq-neg-boolᵉ falseᵉ ()
```

### Boolean negation is an involution

```agda
is-involution-neg-boolᵉ : is-involutionᵉ neg-boolᵉ
is-involution-neg-boolᵉ trueᵉ = reflᵉ
is-involution-neg-boolᵉ falseᵉ = reflᵉ
```

### Boolean negation is an equivalence

```agda
abstract
  is-equiv-neg-boolᵉ : is-equivᵉ neg-boolᵉ
  is-equiv-neg-boolᵉ = is-equiv-is-involutionᵉ is-involution-neg-boolᵉ

equiv-neg-boolᵉ : boolᵉ ≃ᵉ boolᵉ
pr1ᵉ equiv-neg-boolᵉ = neg-boolᵉ
pr2ᵉ equiv-neg-boolᵉ = is-equiv-neg-boolᵉ
```

### The constant function `const bool b` is not an equivalence

```agda
abstract
  no-section-const-boolᵉ : (bᵉ : boolᵉ) → ¬ᵉ (sectionᵉ (constᵉ boolᵉ bᵉ))
  no-section-const-boolᵉ trueᵉ (gᵉ ,ᵉ Gᵉ) = neq-true-false-boolᵉ (Gᵉ falseᵉ)
  no-section-const-boolᵉ falseᵉ (gᵉ ,ᵉ Gᵉ) = neq-false-true-boolᵉ (Gᵉ trueᵉ)

abstract
  is-not-equiv-const-boolᵉ :
    (bᵉ : boolᵉ) → ¬ᵉ (is-equivᵉ (constᵉ boolᵉ bᵉ))
  is-not-equiv-const-boolᵉ bᵉ eᵉ = no-section-const-boolᵉ bᵉ (section-is-equivᵉ eᵉ)
```