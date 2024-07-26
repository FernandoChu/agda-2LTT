# Least upper bounds in large posets

```agda
module order-theory.least-upper-bounds-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
open import order-theory.upper-bounds-large-posetsᵉ
```

</details>

## Idea

Aᵉ **leastᵉ upperᵉ bound**ᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : Iᵉ → P`ᵉ in aᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ in `P`ᵉ suchᵉ
thatᵉ theᵉ [logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  is-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ aᵉ yᵉ ↔ᵉ (xᵉ ≤ᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ in `P`.ᵉ

## Definitions

### The predicate on large posets of being a least upper bound of a family of elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-least-upper-bound-family-of-elements-Large-Posetᵉ :
    type-Large-Posetᵉ Pᵉ l3ᵉ → UUωᵉ
  is-least-upper-bound-family-of-elements-Large-Posetᵉ yᵉ =
    {l4ᵉ : Level} (zᵉ : type-Large-Posetᵉ Pᵉ l4ᵉ) →
    is-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ zᵉ ↔ᵉ leq-Large-Posetᵉ Pᵉ yᵉ zᵉ

  leq-is-least-upper-bound-family-of-elements-Large-Posetᵉ :
    (yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ yᵉ →
    {l4ᵉ : Level} (zᵉ : type-Large-Posetᵉ Pᵉ l4ᵉ) →
    is-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ zᵉ →
    leq-Large-Posetᵉ Pᵉ yᵉ zᵉ
  leq-is-least-upper-bound-family-of-elements-Large-Posetᵉ yᵉ Hᵉ zᵉ Kᵉ =
    forward-implicationᵉ (Hᵉ zᵉ) Kᵉ
```

### The predicate on families of elements in large posets of having least upper bounds

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (γᵉ : Level)
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  record
    has-least-upper-bound-family-of-elements-Large-Posetᵉ : UUωᵉ
    where
    field
      sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ :
        type-Large-Posetᵉ Pᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
      is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ :
        is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ
          sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ

  open has-least-upper-bound-family-of-elements-Large-Posetᵉ public
```

## Properties

### Least upper bounds of families of elements are upper bounds

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ}
  where

  is-upper-bound-is-least-upper-bound-family-of-elements-Large-Posetᵉ :
    {l3ᵉ : Level} {yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ} →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    is-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ yᵉ
  is-upper-bound-is-least-upper-bound-family-of-elements-Large-Posetᵉ Hᵉ =
    backward-implicationᵉ (Hᵉ _) (refl-leq-Large-Posetᵉ Pᵉ _)
```

### Least upper bounds of families of elements are unique up to similairity of elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ}
  where

  sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ :
    {l3ᵉ l4ᵉ : Level} {yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ} {zᵉ : type-Large-Posetᵉ Pᵉ l4ᵉ} →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ zᵉ →
    sim-Large-Posetᵉ Pᵉ yᵉ zᵉ
  pr1ᵉ (sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ Hᵉ Kᵉ) =
    forward-implicationᵉ
      ( Hᵉ _)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ Kᵉ)
  pr2ᵉ (sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ Hᵉ Kᵉ) =
    forward-implicationᵉ
      ( Kᵉ _)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ Hᵉ)
```

### A family of least upper bounds of families of elements in a family of large poset is a least upper bound in their dependent product

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (aᵉ : Jᵉ → type-Π-Large-Posetᵉ Pᵉ l3ᵉ)
  {l4ᵉ : Level} (xᵉ : type-Π-Large-Posetᵉ Pᵉ l4ᵉ)
  where

  is-least-upper-bound-Π-Large-Posetᵉ :
    ( (iᵉ : Iᵉ) →
      is-least-upper-bound-family-of-elements-Large-Posetᵉ
        ( Pᵉ iᵉ)
        ( λ jᵉ → aᵉ jᵉ iᵉ)
        ( xᵉ iᵉ)) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) aᵉ xᵉ
  is-least-upper-bound-Π-Large-Posetᵉ Hᵉ yᵉ =
    logical-equivalence-reasoningᵉ
      is-upper-bound-family-of-elements-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) aᵉ yᵉ
      ↔ᵉ ( (iᵉ : Iᵉ) →
          is-upper-bound-family-of-elements-Large-Posetᵉ
            ( Pᵉ iᵉ)
            ( λ jᵉ → aᵉ jᵉ iᵉ)
            ( yᵉ iᵉ))
        byᵉ
        inv-iffᵉ
          ( logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Posetᵉ
            ( Pᵉ)
              ( aᵉ)
              ( yᵉ))
      ↔ᵉ leq-Π-Large-Posetᵉ Pᵉ xᵉ yᵉ
        byᵉ
        iff-Π-iff-familyᵉ (λ iᵉ → Hᵉ iᵉ (yᵉ iᵉ))
```

### Least upper bounds in small posets from least upper bounds in large posets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-least-upper-bound-family-of-elements-poset-Large-Posetᵉ :
    (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    is-least-upper-bound-family-of-elements-Posetᵉ
      ( poset-Large-Posetᵉ Pᵉ l2ᵉ) (xᵉ) (yᵉ)
  is-least-upper-bound-family-of-elements-poset-Large-Posetᵉ yᵉ is-lub-yᵉ zᵉ =
    is-lub-yᵉ zᵉ
```