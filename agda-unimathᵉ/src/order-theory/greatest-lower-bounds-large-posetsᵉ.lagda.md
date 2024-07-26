# Greatest lower bounds in large posets

```agda
module order-theory.greatest-lower-bounds-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
open import order-theory.lower-bounds-large-posetsᵉ
```

</details>

## Idea

Aᵉ **greatestᵉ binaryᵉ lowerᵉ bound**ᵉ ofᵉ twoᵉ elementsᵉ `a`ᵉ andᵉ `b`ᵉ in aᵉ largeᵉ posetᵉ
`P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ suchᵉ thatᵉ forᵉ everyᵉ elementᵉ `y`ᵉ in `P`ᵉ theᵉ logicalᵉ
equivalenceᵉ

```text
  is-binary-lower-bound-Large-Posetᵉ Pᵉ aᵉ bᵉ yᵉ ↔ᵉ yᵉ ≤ᵉ xᵉ
```

holds.ᵉ

## Definitions

### The predicate that an element of a large poset is the greatest lower bound of two elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} (aᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (bᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-greatest-binary-lower-bound-Large-Posetᵉ :
    {l3ᵉ : Level} → type-Large-Posetᵉ Pᵉ l3ᵉ → UUωᵉ
  is-greatest-binary-lower-bound-Large-Posetᵉ xᵉ =
    {l4ᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ l4ᵉ) →
    is-binary-lower-bound-Large-Posetᵉ Pᵉ aᵉ bᵉ yᵉ ↔ᵉ leq-Large-Posetᵉ Pᵉ yᵉ xᵉ
```

## Properties

### Any pointwise greatest lower bound of two elements in a dependent product of large posets is a greatest lower bound

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (xᵉ : type-Π-Large-Posetᵉ Pᵉ l1ᵉ)
  (yᵉ : type-Π-Large-Posetᵉ Pᵉ l2ᵉ)
  (zᵉ : type-Π-Large-Posetᵉ Pᵉ l3ᵉ)
  where

  is-greatest-binary-lower-bound-Π-Large-Posetᵉ :
    ( (iᵉ : Iᵉ) →
      is-greatest-binary-lower-bound-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (zᵉ iᵉ)) →
    is-greatest-binary-lower-bound-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) xᵉ yᵉ zᵉ
  is-greatest-binary-lower-bound-Π-Large-Posetᵉ Hᵉ uᵉ =
    logical-equivalence-reasoningᵉ
      is-binary-lower-bound-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) xᵉ yᵉ uᵉ
        ↔ᵉ ((iᵉ : Iᵉ) → is-binary-lower-bound-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (uᵉ iᵉ))
          byᵉ
          inv-iffᵉ
            ( logical-equivalence-is-binary-lower-bound-Π-Large-Posetᵉ Pᵉ xᵉ yᵉ uᵉ)
        ↔ᵉ leq-Π-Large-Posetᵉ Pᵉ uᵉ zᵉ
          byᵉ iff-Π-iff-familyᵉ (λ iᵉ → Hᵉ iᵉ (uᵉ iᵉ))
```