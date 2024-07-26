# Subsets of semirings

```agda
module ring-theory.subsets-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Aᵉ subsetᵉ ofᵉ aᵉ semiringᵉ isᵉ aᵉ subtypeᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ aᵉ semiringᵉ

## Definition

### Subsets of semirings

```agda
subset-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Semiringᵉ lᵉ Rᵉ = subtypeᵉ lᵉ (type-Semiringᵉ Rᵉ)

is-set-subset-Semiringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) → is-setᵉ (subset-Semiringᵉ lᵉ Rᵉ)
is-set-subset-Semiringᵉ lᵉ Rᵉ =
  is-set-function-typeᵉ is-set-type-Propᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : subset-Semiringᵉ l2ᵉ Rᵉ)
  where

  is-in-subset-Semiringᵉ : type-Semiringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-subset-Semiringᵉ = is-in-subtypeᵉ Sᵉ

  is-prop-is-in-subset-Semiringᵉ :
    (xᵉ : type-Semiringᵉ Rᵉ) → is-propᵉ (is-in-subset-Semiringᵉ xᵉ)
  is-prop-is-in-subset-Semiringᵉ = is-prop-is-in-subtypeᵉ Sᵉ

  type-subset-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Semiringᵉ = type-subtypeᵉ Sᵉ

  inclusion-subset-Semiringᵉ : type-subset-Semiringᵉ → type-Semiringᵉ Rᵉ
  inclusion-subset-Semiringᵉ = inclusion-subtypeᵉ Sᵉ

  ap-inclusion-subset-Semiringᵉ :
    (xᵉ yᵉ : type-subset-Semiringᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-subset-Semiringᵉ xᵉ ＝ᵉ inclusion-subset-Semiringᵉ yᵉ)
  ap-inclusion-subset-Semiringᵉ = ap-inclusion-subtypeᵉ Sᵉ

  is-in-subset-inclusion-subset-Semiringᵉ :
    (xᵉ : type-subset-Semiringᵉ) →
    is-in-subset-Semiringᵉ (inclusion-subset-Semiringᵉ xᵉ)
  is-in-subset-inclusion-subset-Semiringᵉ =
    is-in-subtype-inclusion-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Semiringᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    is-in-subset-Semiringᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Semiringᵉ yᵉ
  is-closed-under-eq-subset-Semiringᵉ =
    is-closed-under-eq-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Semiring'ᵉ :
    {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    is-in-subset-Semiringᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Semiringᵉ xᵉ
  is-closed-under-eq-subset-Semiring'ᵉ =
    is-closed-under-eq-subtype'ᵉ Sᵉ
```

### The condition that a subset contains zero

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Sᵉ : subset-Semiringᵉ l2ᵉ Rᵉ)
  where

  contains-zero-subset-Semiringᵉ : UUᵉ l2ᵉ
  contains-zero-subset-Semiringᵉ = is-in-subtypeᵉ Sᵉ (zero-Semiringᵉ Rᵉ)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Semiringᵉ : UUᵉ l2ᵉ
  contains-one-subset-Semiringᵉ = is-in-subtypeᵉ Sᵉ (one-Semiringᵉ Rᵉ)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-addition-subset-Semiringᵉ =
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    is-in-subtypeᵉ Sᵉ xᵉ → is-in-subtypeᵉ Sᵉ yᵉ →
    is-in-subtypeᵉ Sᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Semiringᵉ =
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → is-in-subtypeᵉ Sᵉ xᵉ → is-in-subtypeᵉ Sᵉ yᵉ →
    is-in-subtypeᵉ Sᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-left-multiplication-subset-Semiringᵉ =
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → is-in-subtypeᵉ Sᵉ yᵉ →
    is-in-subtypeᵉ Sᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-right-multiplication-subset-Semiringᵉ =
    (xᵉ yᵉ : type-Semiringᵉ Rᵉ) → is-in-subtypeᵉ Sᵉ xᵉ →
    is-in-subtypeᵉ Sᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ)
```