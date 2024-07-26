# Subsets of commutative monoids

```agda
module group-theory.subsets-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.subsets-monoidsᵉ
```

</details>

## Idea

Aᵉ subsetᵉ ofᵉ aᵉ commutativeᵉ monoidᵉ `M`ᵉ isᵉ aᵉ subsetᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `M`.ᵉ

## Definitions

### Subsets of commutative monoids

```agda
subset-Commutative-Monoidᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Mᵉ : Commutative-Monoidᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subset-Commutative-Monoidᵉ l2ᵉ Mᵉ =
  subset-Monoidᵉ l2ᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Pᵉ : subset-Commutative-Monoidᵉ l2ᵉ Mᵉ)
  where

  is-in-subset-Commutative-Monoidᵉ : type-Commutative-Monoidᵉ Mᵉ → UUᵉ l2ᵉ
  is-in-subset-Commutative-Monoidᵉ =
    is-in-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-prop-is-in-subset-Commutative-Monoidᵉ :
    (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    is-propᵉ (is-in-subset-Commutative-Monoidᵉ xᵉ)
  is-prop-is-in-subset-Commutative-Monoidᵉ =
    is-prop-is-in-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  type-subset-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Commutative-Monoidᵉ =
    type-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-set-type-subset-Commutative-Monoidᵉ : is-setᵉ type-subset-Commutative-Monoidᵉ
  is-set-type-subset-Commutative-Monoidᵉ =
    is-set-type-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  set-subset-Commutative-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-subset-Commutative-Monoidᵉ =
    set-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  inclusion-subset-Commutative-Monoidᵉ :
    type-subset-Commutative-Monoidᵉ → type-Commutative-Monoidᵉ Mᵉ
  inclusion-subset-Commutative-Monoidᵉ =
    inclusion-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  ap-inclusion-subset-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-subset-Commutative-Monoidᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-subset-Commutative-Monoidᵉ xᵉ ＝ᵉ
    inclusion-subset-Commutative-Monoidᵉ yᵉ
  ap-inclusion-subset-Commutative-Monoidᵉ =
    ap-inclusion-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  is-in-subset-inclusion-subset-Commutative-Monoidᵉ :
    (xᵉ : type-subset-Commutative-Monoidᵉ) →
    is-in-subset-Commutative-Monoidᵉ (inclusion-subset-Commutative-Monoidᵉ xᵉ)
  is-in-subset-inclusion-subset-Commutative-Monoidᵉ =
    is-in-subset-inclusion-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ
```

### The condition that a subset contains the unit

```agda
  contains-unit-prop-subset-Commutative-Monoidᵉ : Propᵉ l2ᵉ
  contains-unit-prop-subset-Commutative-Monoidᵉ =
    contains-unit-prop-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ

  contains-unit-subset-Commutative-Monoidᵉ : UUᵉ l2ᵉ
  contains-unit-subset-Commutative-Monoidᵉ =
    contains-unit-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-prop-subset-Commutative-Monoidᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-prop-subset-Commutative-Monoidᵉ =
    is-closed-under-multiplication-prop-subset-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( Pᵉ)

  is-closed-under-multiplication-subset-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Commutative-Monoidᵉ =
    is-closed-under-multiplication-subset-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ) Pᵉ
```