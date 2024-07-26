# Iterated deloopings of pointed types

```agda
module higher-group-theory.iterated-deloopings-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.iterated-loop-spacesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ {{#conceptᵉ "`n`-foldᵉ deloopings"ᵉ Disambiguation="pointedᵉ type"ᵉ}} ofᵉ
aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `X`ᵉ isᵉ theᵉ typeᵉ

```text
  Σᵉ (Yᵉ : Pointed-Type),ᵉ is-connectedᵉ (n-1ᵉ) Yᵉ ×ᵉ (Ωⁿᵉ Xᵉ ≃∗ᵉ Y).ᵉ
```

Here,ᵉ theᵉ pointedᵉ typeᵉ `Ωⁿᵉ X`ᵉ isᵉ theᵉ `n`-thᵉ
[iteratedᵉ loopᵉ space](synthetic-homotopy-theory.iterated-loop-spaces.mdᵉ) ofᵉ `X`.ᵉ

## Definitions

### The type of `n`-fold deloopings of a pointed type, with respect to a universe level

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (nᵉ : ℕᵉ) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  iterated-delooping-Levelᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  iterated-delooping-Levelᵉ =
    Σᵉ ( Pointed-Typeᵉ l2ᵉ)
      ( λ Yᵉ →
        ( is-connectedᵉ (truncation-level-minus-one-ℕᵉ nᵉ) (type-Pointed-Typeᵉ Yᵉ)) ×ᵉ
        ( iterated-loop-spaceᵉ nᵉ Xᵉ ≃∗ᵉ Yᵉ))
```

### The type of `n`-fold deloopings of a pointed type

```agda
module _
  {l1ᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  iterated-deloopingᵉ : UUᵉ (lsuc l1ᵉ)
  iterated-deloopingᵉ = iterated-delooping-Levelᵉ l1ᵉ nᵉ Xᵉ
```