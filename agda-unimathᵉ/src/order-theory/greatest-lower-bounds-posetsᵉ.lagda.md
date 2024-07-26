# Greatest lower bounds in posets

```agda
module order-theory.greatest-lower-bounds-posetsᵉ where
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

open import order-theory.lower-bounds-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **greatestᵉ lowerᵉ bound**ᵉ ofᵉ `a`ᵉ andᵉ `b`ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ suchᵉ
thatᵉ theᵉ logicalᵉ equivalenceᵉ

```text
  ((yᵉ ≤ᵉ aᵉ) ∧ᵉ (yᵉ ≤ᵉ bᵉ)) ⇔ᵉ (yᵉ ≤ᵉ xᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `y`ᵉ in `P`.ᵉ Similarly,ᵉ aᵉ **greatestᵉ lowerᵉ bound**ᵉ ofᵉ aᵉ
familyᵉ `aᵉ : Iᵉ → P`ᵉ ofᵉ elementsᵉ ofᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ theᵉ
logicalᵉ equivalenceᵉ

```text
  (∀ᵢᵉ (yᵉ ≤ᵉ aᵢᵉ)) ⇔ᵉ (yᵉ ≤ᵉ xᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `y`ᵉ in `P`.ᵉ

## Definitions

### The predicate of being a greatest binary lower bound of two elements in a poset

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (aᵉ bᵉ : type-Posetᵉ Pᵉ)
  where

  is-greatest-binary-lower-bound-Poset-Propᵉ : type-Posetᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-greatest-binary-lower-bound-Poset-Propᵉ xᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ yᵉ →
        iff-Propᵉ
          ( is-binary-lower-bound-Poset-Propᵉ Pᵉ aᵉ bᵉ yᵉ)
          ( leq-Poset-Propᵉ Pᵉ yᵉ xᵉ))

  is-greatest-binary-lower-bound-Posetᵉ : type-Posetᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-greatest-binary-lower-bound-Posetᵉ xᵉ =
    type-Propᵉ (is-greatest-binary-lower-bound-Poset-Propᵉ xᵉ)

  is-prop-is-greatest-binary-lower-bound-Posetᵉ :
    (xᵉ : type-Posetᵉ Pᵉ) →
    is-propᵉ (is-greatest-binary-lower-bound-Posetᵉ xᵉ)
  is-prop-is-greatest-binary-lower-bound-Posetᵉ xᵉ =
    is-prop-type-Propᵉ (is-greatest-binary-lower-bound-Poset-Propᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ : type-Posetᵉ Pᵉ}
  where

  forward-implication-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ → leq-Posetᵉ Pᵉ yᵉ xᵉ
  forward-implication-is-greatest-binary-lower-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    forward-implicationᵉ (Hᵉ yᵉ)

  backward-implication-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ yᵉ xᵉ → is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ
  backward-implication-is-greatest-binary-lower-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ =
    backward-implicationᵉ (Hᵉ yᵉ)

  prove-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    ( (yᵉ : type-Posetᵉ Pᵉ) →
      is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ → leq-Posetᵉ Pᵉ yᵉ xᵉ) →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ
  pr1ᵉ (prove-is-greatest-binary-lower-bound-Posetᵉ Hᵉ Kᵉ yᵉ) Lᵉ = Kᵉ yᵉ Lᵉ
  pr2ᵉ (prove-is-greatest-binary-lower-bound-Posetᵉ Hᵉ Kᵉ yᵉ) Lᵉ =
    is-binary-lower-bound-leq-Posetᵉ Pᵉ Hᵉ Lᵉ

  is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ
  is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ {xᵉ} Hᵉ =
    backward-implication-is-greatest-binary-lower-bound-Posetᵉ Hᵉ
      ( refl-leq-Posetᵉ Pᵉ xᵉ)

  leq-left-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ xᵉ aᵉ
  leq-left-is-greatest-binary-lower-bound-Posetᵉ Hᵉ =
    leq-left-is-binary-lower-bound-Posetᵉ Pᵉ
      ( is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ Hᵉ)

  leq-right-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    leq-Posetᵉ Pᵉ xᵉ bᵉ
  leq-right-is-greatest-binary-lower-bound-Posetᵉ Hᵉ =
    leq-right-is-binary-lower-bound-Posetᵉ Pᵉ
      ( is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ Hᵉ)
```

### The proposition that two elements have a greatest lower bound

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (aᵉ bᵉ : type-Posetᵉ Pᵉ)
  where

  has-greatest-binary-lower-bound-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-greatest-binary-lower-bound-Posetᵉ =
    Σᵉ (type-Posetᵉ Pᵉ) (is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ)

  all-elements-equal-has-greatest-binary-lower-bound-Posetᵉ :
    all-elements-equalᵉ has-greatest-binary-lower-bound-Posetᵉ
  all-elements-equal-has-greatest-binary-lower-bound-Posetᵉ
    (pairᵉ uᵉ Hᵉ) (pairᵉ vᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-greatest-binary-lower-bound-Poset-Propᵉ Pᵉ aᵉ bᵉ)
      ( antisymmetric-leq-Posetᵉ Pᵉ uᵉ vᵉ
        ( forward-implication-is-greatest-binary-lower-bound-Posetᵉ Pᵉ Kᵉ
          ( is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ Pᵉ Hᵉ))
        ( forward-implication-is-greatest-binary-lower-bound-Posetᵉ Pᵉ Hᵉ
          ( is-binary-lower-bound-is-greatest-binary-lower-bound-Posetᵉ Pᵉ Kᵉ)))

  is-prop-has-greatest-binary-lower-bound-Posetᵉ :
    is-propᵉ has-greatest-binary-lower-bound-Posetᵉ
  is-prop-has-greatest-binary-lower-bound-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-greatest-binary-lower-bound-Posetᵉ

  has-greatest-binary-lower-bound-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-greatest-binary-lower-bound-Poset-Propᵉ =
    has-greatest-binary-lower-bound-Posetᵉ
  pr2ᵉ has-greatest-binary-lower-bound-Poset-Propᵉ =
    is-prop-has-greatest-binary-lower-bound-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ : type-Posetᵉ Pᵉ}
  where

  eq-is-greatest-binary-lower-bound-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ →
    is-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ
  eq-is-greatest-binary-lower-bound-Posetᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    apᵉ
      ( pr1ᵉ)
      ( all-elements-equal-has-greatest-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ
        ( xᵉ ,ᵉ Hᵉ)
        ( yᵉ ,ᵉ Kᵉ))
```

### Greatest lower bounds of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} (aᵉ : Iᵉ → type-Posetᵉ Pᵉ)
  where

  is-greatest-lower-bound-family-of-elements-Poset-Propᵉ :
    type-Posetᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-greatest-lower-bound-family-of-elements-Poset-Propᵉ xᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ yᵉ →
        iff-Propᵉ
          ( Π-Propᵉ Iᵉ (λ iᵉ → leq-Poset-Propᵉ Pᵉ yᵉ (aᵉ iᵉ)))
          ( leq-Poset-Propᵉ Pᵉ yᵉ xᵉ))

  is-greatest-lower-bound-family-of-elements-Posetᵉ :
    type-Posetᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-greatest-lower-bound-family-of-elements-Posetᵉ zᵉ =
    type-Propᵉ (is-greatest-lower-bound-family-of-elements-Poset-Propᵉ zᵉ)

  is-prop-is-greatest-lower-bound-family-of-elements-Posetᵉ :
    (zᵉ : type-Posetᵉ Pᵉ) →
    is-propᵉ (is-greatest-lower-bound-family-of-elements-Posetᵉ zᵉ)
  is-prop-is-greatest-lower-bound-family-of-elements-Posetᵉ zᵉ =
    is-prop-type-Propᵉ (is-greatest-lower-bound-family-of-elements-Poset-Propᵉ zᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  where

  forward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    ((iᵉ : Iᵉ) → leq-Posetᵉ Pᵉ yᵉ (aᵉ iᵉ)) → leq-Posetᵉ Pᵉ yᵉ xᵉ
  forward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ
    { xᵉ} {yᵉ} Hᵉ =
    forward-implicationᵉ (Hᵉ yᵉ)

  backward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    leq-Posetᵉ Pᵉ yᵉ xᵉ → (iᵉ : Iᵉ) → leq-Posetᵉ Pᵉ yᵉ (aᵉ iᵉ)
  backward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ
    {xᵉ} {yᵉ} Hᵉ =
    backward-implicationᵉ (Hᵉ yᵉ)

  is-lower-bound-is-greatest-lower-bound-family-of-elements-Posetᵉ :
    {xᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    is-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ
  is-lower-bound-is-greatest-lower-bound-family-of-elements-Posetᵉ {xᵉ} Hᵉ =
    backward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ Hᵉ
      ( refl-leq-Posetᵉ Pᵉ xᵉ)
```

### The proposition that a family of elements has a greatest lower bound

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} (aᵉ : Iᵉ → type-Posetᵉ Pᵉ)
  where

  has-greatest-lower-bound-family-of-elements-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-greatest-lower-bound-family-of-elements-Posetᵉ =
    Σᵉ (type-Posetᵉ Pᵉ) (is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ)

  all-elements-equal-has-greatest-lower-bound-family-of-elements-Posetᵉ :
    all-elements-equalᵉ has-greatest-lower-bound-family-of-elements-Posetᵉ
  all-elements-equal-has-greatest-lower-bound-family-of-elements-Posetᵉ
    ( xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-greatest-lower-bound-family-of-elements-Poset-Propᵉ Pᵉ aᵉ)
      ( antisymmetric-leq-Posetᵉ Pᵉ xᵉ yᵉ
        ( forward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ
          ( Pᵉ)
          ( Kᵉ)
          ( is-lower-bound-is-greatest-lower-bound-family-of-elements-Posetᵉ
            ( Pᵉ)
            ( Hᵉ)))
        ( forward-implication-is-greatest-lower-bound-family-of-elements-Posetᵉ
          ( Pᵉ)
          ( Hᵉ)
          ( is-lower-bound-is-greatest-lower-bound-family-of-elements-Posetᵉ
            ( Pᵉ)
            ( Kᵉ))))

  is-prop-has-greatest-lower-bound-family-of-elements-Posetᵉ :
    is-propᵉ has-greatest-lower-bound-family-of-elements-Posetᵉ
  is-prop-has-greatest-lower-bound-family-of-elements-Posetᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-has-greatest-lower-bound-family-of-elements-Posetᵉ

  has-greatest-lower-bound-family-of-elements-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ has-greatest-lower-bound-family-of-elements-Poset-Propᵉ =
    has-greatest-lower-bound-family-of-elements-Posetᵉ
  pr2ᵉ has-greatest-lower-bound-family-of-elements-Poset-Propᵉ =
    is-prop-has-greatest-lower-bound-family-of-elements-Posetᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  where

  eq-is-greatest-lower-bound-family-of-elements-Posetᵉ :
    {xᵉ yᵉ : type-Posetᵉ Pᵉ} →
    is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ →
    is-greatest-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ →
    xᵉ ＝ᵉ yᵉ
  eq-is-greatest-lower-bound-family-of-elements-Posetᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    apᵉ
      ( pr1ᵉ)
      ( all-elements-equal-has-greatest-lower-bound-family-of-elements-Posetᵉ
        ( Pᵉ)
        ( aᵉ)
        ( xᵉ ,ᵉ Hᵉ)
        ( yᵉ ,ᵉ Kᵉ))
```