# Rational commutative monoids

```agda
module group-theory.rational-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.powers-of-elements-commutative-monoidsᵉ
```

</details>

## Idea

Aᵉ **rationalᵉ commutativeᵉ monoid**ᵉ isᵉ aᵉ
[commutativeᵉ monoid](group-theory.commutative-monoids.mdᵉ) `(M,0,+)`ᵉ in whichᵉ theᵉ
mapᵉ `xᵉ ↦ᵉ nx`ᵉ isᵉ invertibleᵉ forᵉ everyᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `nᵉ >ᵉ 0`.ᵉ Thisᵉ
conditionᵉ impliesᵉ thatᵉ weᵉ canᵉ invertᵉ theᵉ naturalᵉ numbersᵉ in `M`,ᵉ whichᵉ areᵉ theᵉ
elementsᵉ ofᵉ theᵉ formᵉ `n1`ᵉ in `M`.ᵉ

Noteᵉ: Sinceᵉ weᵉ usuallyᵉ writeᵉ commutativeᵉ monoidsᵉ multiplicatively,ᵉ theᵉ conditionᵉ
thatᵉ aᵉ commutativeᵉ monoidᵉ isᵉ rationalᵉ isᵉ thatᵉ theᵉ mapᵉ `xᵉ ↦ᵉ xⁿ`ᵉ isᵉ invertibleᵉ forᵉ
everyᵉ naturalᵉ numberᵉ `nᵉ >ᵉ 0`.ᵉ However,ᵉ forᵉ rationalᵉ commutativeᵉ monoidsᵉ weᵉ willᵉ
writeᵉ theᵉ binaryᵉ operationᵉ additively.ᵉ

## Definition

### The predicate of being a rational commutative monoid

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  is-rational-prop-Commutative-Monoidᵉ : Propᵉ lᵉ
  is-rational-prop-Commutative-Monoidᵉ =
    Π-Propᵉ ℕᵉ
      ( λ nᵉ →
        is-equiv-Propᵉ (power-Commutative-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ)))

  is-rational-Commutative-Monoidᵉ : UUᵉ lᵉ
  is-rational-Commutative-Monoidᵉ =
    type-Propᵉ is-rational-prop-Commutative-Monoidᵉ

  is-prop-is-rational-Commutative-Monoidᵉ :
    is-propᵉ is-rational-Commutative-Monoidᵉ
  is-prop-is-rational-Commutative-Monoidᵉ =
    is-prop-type-Propᵉ is-rational-prop-Commutative-Monoidᵉ
```

### Rational commutative monoids

```agda
Rational-Commutative-Monoidᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Rational-Commutative-Monoidᵉ lᵉ =
  Σᵉ (Commutative-Monoidᵉ lᵉ) is-rational-Commutative-Monoidᵉ

module _
  {lᵉ : Level} (Mᵉ : Rational-Commutative-Monoidᵉ lᵉ)
  where

  commutative-monoid-Rational-Commutative-Monoidᵉ : Commutative-Monoidᵉ lᵉ
  commutative-monoid-Rational-Commutative-Monoidᵉ = pr1ᵉ Mᵉ

  monoid-Rational-Commutative-Monoidᵉ : Monoidᵉ lᵉ
  monoid-Rational-Commutative-Monoidᵉ =
    monoid-Commutative-Monoidᵉ commutative-monoid-Rational-Commutative-Monoidᵉ

  type-Rational-Commutative-Monoidᵉ : UUᵉ lᵉ
  type-Rational-Commutative-Monoidᵉ =
    type-Commutative-Monoidᵉ commutative-monoid-Rational-Commutative-Monoidᵉ

  add-Rational-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Rational-Commutative-Monoidᵉ) →
    type-Rational-Commutative-Monoidᵉ
  add-Rational-Commutative-Monoidᵉ =
    mul-Commutative-Monoidᵉ commutative-monoid-Rational-Commutative-Monoidᵉ

  zero-Rational-Commutative-Monoidᵉ : type-Rational-Commutative-Monoidᵉ
  zero-Rational-Commutative-Monoidᵉ =
    unit-Commutative-Monoidᵉ commutative-monoid-Rational-Commutative-Monoidᵉ

  associative-add-Rational-Commutative-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Rational-Commutative-Monoidᵉ) →
    add-Rational-Commutative-Monoidᵉ
      ( add-Rational-Commutative-Monoidᵉ xᵉ yᵉ)
      ( zᵉ) ＝ᵉ
    add-Rational-Commutative-Monoidᵉ
      ( xᵉ)
      ( add-Rational-Commutative-Monoidᵉ yᵉ zᵉ)
  associative-add-Rational-Commutative-Monoidᵉ =
    associative-mul-Commutative-Monoidᵉ
      commutative-monoid-Rational-Commutative-Monoidᵉ

  left-unit-law-add-Rational-Commutative-Monoidᵉ :
    (xᵉ : type-Rational-Commutative-Monoidᵉ) →
    add-Rational-Commutative-Monoidᵉ zero-Rational-Commutative-Monoidᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Rational-Commutative-Monoidᵉ =
    left-unit-law-mul-Commutative-Monoidᵉ
      commutative-monoid-Rational-Commutative-Monoidᵉ

  right-unit-law-add-Rational-Commutative-Monoidᵉ :
    (xᵉ : type-Rational-Commutative-Monoidᵉ) →
    add-Rational-Commutative-Monoidᵉ xᵉ zero-Rational-Commutative-Monoidᵉ ＝ᵉ xᵉ
  right-unit-law-add-Rational-Commutative-Monoidᵉ =
    right-unit-law-mul-Commutative-Monoidᵉ
      commutative-monoid-Rational-Commutative-Monoidᵉ

  multiple-Rational-Commutative-Monoidᵉ :
    ℕᵉ → type-Rational-Commutative-Monoidᵉ → type-Rational-Commutative-Monoidᵉ
  multiple-Rational-Commutative-Monoidᵉ =
    power-Commutative-Monoidᵉ commutative-monoid-Rational-Commutative-Monoidᵉ

  is-rational-Rational-Commutative-Monoidᵉ :
    is-rational-Commutative-Monoidᵉ
      commutative-monoid-Rational-Commutative-Monoidᵉ
  is-rational-Rational-Commutative-Monoidᵉ = pr2ᵉ Mᵉ
```