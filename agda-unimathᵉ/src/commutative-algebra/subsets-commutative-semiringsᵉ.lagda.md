# Subsets of commutative semirings

```agda
module commutative-algebra.subsets-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.subsets-semiringsᵉ
```

</details>

## Idea

Aᵉ **subset**ᵉ ofᵉ aᵉ commutativeᵉ semiringᵉ isᵉ aᵉ subtypeᵉ ofᵉ itsᵉ underlyingᵉ type.ᵉ

## Definition

### Subsets of commutative semirings

```agda
subset-Commutative-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Commutative-Semiringᵉ lᵉ Aᵉ =
  subset-Semiringᵉ lᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

is-set-subset-Commutative-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) →
  is-setᵉ (subset-Commutative-Semiringᵉ lᵉ Aᵉ)
is-set-subset-Commutative-Semiringᵉ lᵉ Aᵉ =
  is-set-subset-Semiringᵉ lᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ)
  where

  type-subset-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Commutative-Semiringᵉ =
    type-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ

  inclusion-subset-Commutative-Semiringᵉ :
    type-subset-Commutative-Semiringᵉ → type-Commutative-Semiringᵉ Aᵉ
  inclusion-subset-Commutative-Semiringᵉ =
    inclusion-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ

  ap-inclusion-subset-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-subset-Commutative-Semiringᵉ) →
    xᵉ ＝ᵉ yᵉ →
    ( inclusion-subset-Commutative-Semiringᵉ xᵉ ＝ᵉ
      inclusion-subset-Commutative-Semiringᵉ yᵉ)
  ap-inclusion-subset-Commutative-Semiringᵉ =
    ap-inclusion-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ

  is-in-subset-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-subset-Commutative-Semiringᵉ = is-in-subtypeᵉ Sᵉ

  is-prop-is-in-subset-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    is-propᵉ (is-in-subset-Commutative-Semiringᵉ xᵉ)
  is-prop-is-in-subset-Commutative-Semiringᵉ =
    is-prop-is-in-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Commutative-Semiringᵉ :
    {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} →
    is-in-subset-Commutative-Semiringᵉ xᵉ → xᵉ ＝ᵉ yᵉ →
    is-in-subset-Commutative-Semiringᵉ yᵉ
  is-closed-under-eq-subset-Commutative-Semiringᵉ =
    is-closed-under-eq-subtypeᵉ Sᵉ

  is-in-subset-inclusion-subset-Commutative-Semiringᵉ :
    (xᵉ : type-subset-Commutative-Semiringᵉ) →
    is-in-subset-Commutative-Semiringᵉ (inclusion-subset-Commutative-Semiringᵉ xᵉ)
  is-in-subset-inclusion-subset-Commutative-Semiringᵉ =
    is-in-subtype-inclusion-subtypeᵉ Sᵉ
```

### The condition that a subset contains zero

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ)
  where

  contains-zero-subset-Commutative-Semiringᵉ : UUᵉ l2ᵉ
  contains-zero-subset-Commutative-Semiringᵉ =
    contains-zero-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ
```

### The condition that a subset contains one

```agda
  contains-one-subset-Commutative-Semiringᵉ : UUᵉ l2ᵉ
  contains-one-subset-Commutative-Semiringᵉ =
    contains-one-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-addition-subset-Commutative-Semiringᵉ =
    is-closed-under-addition-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Commutative-Semiringᵉ =
    is-closed-under-multiplication-subset-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( Sᵉ)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-left-multiplication-subset-Commutative-Semiringᵉ =
    is-closed-under-left-multiplication-subset-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( Sᵉ)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Commutative-Semiringᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-right-multiplication-subset-Commutative-Semiringᵉ =
    is-closed-under-right-multiplication-subset-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( Sᵉ)
```