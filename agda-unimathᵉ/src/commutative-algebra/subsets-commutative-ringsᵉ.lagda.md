# Subsets of commutative rings

```agda
module commutative-algebra.subsets-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.identity-typesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.subgroups-abelian-groupsᵉ

open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Aᵉ **subset**ᵉ ofᵉ aᵉ commutativeᵉ ringᵉ isᵉ aᵉ subtypeᵉ ofᵉ itsᵉ underlyingᵉ type.ᵉ

## Definition

### Subsets of rings

```agda
subset-Commutative-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Commutative-Ringᵉ lᵉ Aᵉ = subtypeᵉ lᵉ (type-Commutative-Ringᵉ Aᵉ)

is-set-subset-Commutative-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) →
  is-setᵉ (subset-Commutative-Ringᵉ lᵉ Aᵉ)
is-set-subset-Commutative-Ringᵉ lᵉ Aᵉ =
  is-set-function-typeᵉ is-set-type-Propᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  is-in-subset-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-subset-Commutative-Ringᵉ = is-in-subtypeᵉ Sᵉ

  is-prop-is-in-subset-Commutative-Ringᵉ :
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) → is-propᵉ (is-in-subset-Commutative-Ringᵉ xᵉ)
  is-prop-is-in-subset-Commutative-Ringᵉ = is-prop-is-in-subtypeᵉ Sᵉ

  type-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Commutative-Ringᵉ = type-subtypeᵉ Sᵉ

  inclusion-subset-Commutative-Ringᵉ :
    type-subset-Commutative-Ringᵉ → type-Commutative-Ringᵉ Aᵉ
  inclusion-subset-Commutative-Ringᵉ = inclusion-subtypeᵉ Sᵉ

  ap-inclusion-subset-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-subset-Commutative-Ringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-subset-Commutative-Ringᵉ xᵉ ＝ᵉ inclusion-subset-Commutative-Ringᵉ yᵉ
  ap-inclusion-subset-Commutative-Ringᵉ = ap-inclusion-subtypeᵉ Sᵉ

  is-in-subset-inclusion-subset-Commutative-Ringᵉ :
    (xᵉ : type-subset-Commutative-Ringᵉ) →
    is-in-subset-Commutative-Ringᵉ (inclusion-subset-Commutative-Ringᵉ xᵉ)
  is-in-subset-inclusion-subset-Commutative-Ringᵉ =
    is-in-subtype-inclusion-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-in-subset-Commutative-Ringᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Commutative-Ringᵉ yᵉ
  is-closed-under-eq-subset-Commutative-Ringᵉ =
    is-closed-under-eq-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Commutative-Ring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    is-in-subset-Commutative-Ringᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Commutative-Ringᵉ xᵉ
  is-closed-under-eq-subset-Commutative-Ring'ᵉ =
    is-closed-under-eq-subtype'ᵉ Sᵉ
```

### The condition that a subset contains zero

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  contains-zero-subset-Commutative-Ringᵉ : UUᵉ l2ᵉ
  contains-zero-subset-Commutative-Ringᵉ =
    is-in-subset-Commutative-Ringᵉ Aᵉ Sᵉ (zero-Commutative-Ringᵉ Aᵉ)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Commutative-Ringᵉ : UUᵉ l2ᵉ
  contains-one-subset-Commutative-Ringᵉ =
    is-in-subset-Commutative-Ringᵉ Aᵉ Sᵉ (one-Commutative-Ringᵉ Aᵉ)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-addition-subset-Commutative-Ringᵉ =
    is-closed-under-addition-subset-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Sᵉ
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-negatives-subset-Commutative-Ringᵉ =
    is-closed-under-negatives-subset-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Sᵉ
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Commutative-Ringᵉ =
    is-closed-under-multiplication-subset-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Sᵉ
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-left-multiplication-subset-Commutative-Ringᵉ =
    is-closed-under-left-multiplication-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Sᵉ)
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-right-multiplication-subset-Commutative-Ringᵉ =
    is-closed-under-right-multiplication-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Sᵉ)
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-additive-subgroup-subset-Commutative-Ringᵉ :
    {l2ᵉ : Level} → subset-Commutative-Ringᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-additive-subgroup-subset-Commutative-Ringᵉ =
    is-subgroup-Abᵉ (ab-Commutative-Ringᵉ Aᵉ)
```