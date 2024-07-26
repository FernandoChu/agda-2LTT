# Least upper bounds in posets

```agda
module order-theory.least-upper-bounds-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.upper-bounds-posetsᵉ
```

</details>

## Idea

Aᵉ **leastᵉ upperᵉ bound**ᵉ ofᵉ `a`ᵉ andᵉ `b`ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ suchᵉ
thatᵉ theᵉ logicalᵉ equivalenceᵉ

```text
  ((aᵉ ≤ᵉ yᵉ) ∧ᵉ (bᵉ ≤ᵉ yᵉ)) ⇔ᵉ (xᵉ ≤ᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `y`ᵉ in `P`.ᵉ Similarly,ᵉ aᵉ **leastᵉ upperᵉ bound**ᵉ ofᵉ aᵉ
familyᵉ `aᵉ : Iᵉ → P`ᵉ ofᵉ elementsᵉ ofᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ theᵉ
logicalᵉ equivalenceᵉ

```text
  (∀ᵢᵉ (aᵢᵉ ≤ᵉ yᵉ)) ⇔ᵉ (xᵉ ≤ᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `y`ᵉ in `P`.ᵉ

## Definitions

### The predicate of being a least binary upper bound of two elements in a poset

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (aᵉ bᵉ : type-Posetᵉ Pᵉ)
  where

  is-least-binary-upper-bound-Poset-Propᵉ : type-Posetᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-least-binary-upper-bound-Poset-Propᵉ xᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ yᵉ →
        iff-Propᵉ
          ( is-binary-upper-bound-Poset-Propᵉ Pᵉ aᵉ bᵉ yᵉ)
          ( leq-Poset-Propᵉ Pᵉ xᵉ yᵉ))

  is-least-binary-upper-bound-Posetᵉ : type-Posetᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-least-binary-upper-bound-Posetᵉ xᵉ =
    type-Propᵉ (is-least-binary-upper-bound-Poset-Propᵉ xᵉ)

  is-prop-is-least-binary-upper-bound-Posetᵉ :
    (xᵉ : type-Posetᵉ Pᵉ) →
    is-propᵉ (is-least-binary-upper-bound-Posetᵉ xᵉ)
  is-prop-is-least-binary-upper-bound-Posetᵉ xᵉ =
    is-prop-type-Propᵉ (is-least-binary-upper-bound-Poset-Propᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ : type-Posetᵉ Pᵉ}
  where

  forward-implication-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ → leq-Posetᵉ Pᵉ xᵉ yᵉ
  forward-implication-is-least-binary-upper-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    forward-implicationᵉ (Hᵉ yᵉ)

  backward-implication-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ xᵉ yᵉ → is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ
  backward-implication-is-least-binary-upper-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    backward-implicationᵉ (Hᵉ yᵉ)

  prove-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    ( (yᵉ : type-Posetᵉ Pᵉ) →
      is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ → leq-Posetᵉ Pᵉ xᵉ yᵉ) →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ
  pr1ᵉ (prove-is-least-binary-upper-bound-Posetᵉ Hᵉ Kᵉ yᵉ) Lᵉ = Kᵉ yᵉ Lᵉ
  pr2ᵉ (prove-is-least-binary-upper-bound-Posetᵉ Hᵉ Kᵉ yᵉ) Lᵉ =
    is-binary-upper-bound-leq-Posetᵉ Pᵉ Hᵉ Lᵉ

  is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ
  is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ {xᵉ} Hᵉ =
    backward-implication-is-least-binary-upper-bound-Posetᵉ Hᵉ
      ( refl-leq-Posetᵉ Pᵉ xᵉ)

  leq-left-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ aᵉ xᵉ
  leq-left-is-least-binary-upper-bound-Posetᵉ Hᵉ =
    leq-left-is-binary-upper-bound-Posetᵉ Pᵉ
      ( is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ Hᵉ)

  leq-right-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ bᵉ xᵉ
  leq-right-is-least-binary-upper-bound-Posetᵉ Hᵉ =
    leq-right-is-binary-upper-bound-Posetᵉ Pᵉ
      ( is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ Hᵉ)
```

### The proposition that two elements have a least upper bound

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (aᵉ bᵉ : type-Posetᵉ Pᵉ)
  where

  has-least-binary-upper-bound-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-least-binary-upper-bound-Posetᵉ =
    Σᵉ (type-Posetᵉ Pᵉ) (is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ)

  all-elements-equal-has-least-binary-upper-bound-Posetᵉ :
    all-elements-equalᵉ has-least-binary-upper-bound-Posetᵉ
  all-elements-equal-has-least-binary-upper-bound-Posetᵉ
    (pairᵉ uᵉ Hᵉ) (pairᵉ vᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-least-binary-upper-bound-Poset-Propᵉ Pᵉ aᵉ bᵉ)
      ( antisymmetric-leq-Posetᵉ Pᵉ uᵉ vᵉ
        ( forward-implication-is-least-binary-upper-bound-Posetᵉ Pᵉ Hᵉ
          ( is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ Pᵉ Kᵉ))
        ( forward-implication-is-least-binary-upper-bound-Posetᵉ Pᵉ Kᵉ
          ( is-binary-upper-bound-is-least-binary-upper-bound-Posetᵉ Pᵉ Hᵉ)))

  is-prop-has-least-binary-upper-bound-Posetᵉ :
    is-propᵉ has-least-binary-upper-bound-Posetᵉ
  is-prop-has-least-binary-upper-bound-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-least-binary-upper-bound-Posetᵉ

  has-least-binary-upper-bound-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-least-binary-upper-bound-Poset-Propᵉ =
    has-least-binary-upper-bound-Posetᵉ
  pr2ᵉ has-least-binary-upper-bound-Poset-Propᵉ =
    is-prop-has-least-binary-upper-bound-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ : type-Posetᵉ Pᵉ}
  where

  eq-is-least-binary-upper-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ
  eq-is-least-binary-upper-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    apᵉ
      ( pr1ᵉ)
      ( all-elements-equal-has-least-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ
        ( xᵉ ,ᵉ Hᵉ)
        ( yᵉ ,ᵉ Kᵉ))
```

### Least upper bounds of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} (aᵉ : Iᵉ → type-Posetᵉ Pᵉ)
  where

  is-least-upper-bound-family-of-elements-Poset-Propᵉ :
    type-Posetᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-least-upper-bound-family-of-elements-Poset-Propᵉ xᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ yᵉ →
        iff-Propᵉ
          ( Π-Propᵉ Iᵉ (λ iᵉ → leq-Poset-Propᵉ Pᵉ (aᵉ iᵉ) yᵉ))
          ( leq-Poset-Propᵉ Pᵉ xᵉ yᵉ))

  is-least-upper-bound-family-of-elements-Posetᵉ :
    type-Posetᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-least-upper-bound-family-of-elements-Posetᵉ zᵉ =
    type-Propᵉ (is-least-upper-bound-family-of-elements-Poset-Propᵉ zᵉ)

  is-prop-is-least-upper-bound-family-of-elements-Posetᵉ :
    (zᵉ : type-Posetᵉ Pᵉ) →
    is-propᵉ (is-least-upper-bound-family-of-elements-Posetᵉ zᵉ)
  is-prop-is-least-upper-bound-family-of-elements-Posetᵉ zᵉ =
    is-prop-type-Propᵉ (is-least-upper-bound-family-of-elements-Poset-Propᵉ zᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  where

  forward-implication-is-least-upper-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    is-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ → leq-Posetᵉ Pᵉ xᵉ yᵉ
  forward-implication-is-least-upper-bound-family-of-elements-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    forward-implicationᵉ (Hᵉ yᵉ)

  backward-implication-is-least-upper-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    leq-Posetᵉ Pᵉ xᵉ yᵉ → is-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ
  backward-implication-is-least-upper-bound-family-of-elements-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    backward-implicationᵉ (Hᵉ yᵉ)

  is-upper-bound-is-least-upper-bound-family-of-elements-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    is-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ
  is-upper-bound-is-least-upper-bound-family-of-elements-Posetᵉ {xᵉ} Hᵉ =
    backward-implication-is-least-upper-bound-family-of-elements-Posetᵉ Hᵉ
      ( refl-leq-Posetᵉ Pᵉ xᵉ)
```

### The proposition that a family of elements has a least upper bound

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} (aᵉ : Iᵉ → type-Posetᵉ Pᵉ)
  where

  has-least-upper-bound-family-of-elements-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-least-upper-bound-family-of-elements-Posetᵉ =
    Σᵉ (type-Posetᵉ Pᵉ) (is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ)

  all-elements-equal-has-least-upper-bound-family-of-elements-Posetᵉ :
    all-elements-equalᵉ has-least-upper-bound-family-of-elements-Posetᵉ
  all-elements-equal-has-least-upper-bound-family-of-elements-Posetᵉ
    ( xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-least-upper-bound-family-of-elements-Poset-Propᵉ Pᵉ aᵉ)
      ( antisymmetric-leq-Posetᵉ Pᵉ xᵉ yᵉ
        ( forward-implication-is-least-upper-bound-family-of-elements-Posetᵉ
          ( Pᵉ)
          ( Hᵉ)
          ( is-upper-bound-is-least-upper-bound-family-of-elements-Posetᵉ
            ( Pᵉ)
            ( Kᵉ)))
        ( forward-implication-is-least-upper-bound-family-of-elements-Posetᵉ
          ( Pᵉ)
          ( Kᵉ)
          ( is-upper-bound-is-least-upper-bound-family-of-elements-Posetᵉ
            ( Pᵉ)
            ( Hᵉ))))

  is-prop-has-least-upper-bound-family-of-elements-Posetᵉ :
    is-propᵉ has-least-upper-bound-family-of-elements-Posetᵉ
  is-prop-has-least-upper-bound-family-of-elements-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-least-upper-bound-family-of-elements-Posetᵉ

  has-least-upper-bound-family-of-elements-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ has-least-upper-bound-family-of-elements-Poset-Propᵉ =
    has-least-upper-bound-family-of-elements-Posetᵉ
  pr2ᵉ has-least-upper-bound-family-of-elements-Poset-Propᵉ =
    is-prop-has-least-upper-bound-family-of-elements-Posetᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  where

  eq-is-least-upper-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ
  eq-is-least-upper-bound-family-of-elements-Posetᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    apᵉ
      ( pr1ᵉ)
      ( all-elements-equal-has-least-upper-bound-family-of-elements-Posetᵉ
        ( Pᵉ)
        ( aᵉ)
        ( xᵉ ,ᵉ Hᵉ)
        ( yᵉ ,ᵉ Kᵉ))
```