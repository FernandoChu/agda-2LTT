# Subsets of rings

```agda
module ring-theory.subsets-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.subgroups-abelian-groupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ subsetᵉ ofᵉ aᵉ ringᵉ isᵉ aᵉ subtypeᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ aᵉ ringᵉ

## Definition

### Subsets of rings

```agda
subset-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Ringᵉ lᵉ Rᵉ = subtypeᵉ lᵉ (type-Ringᵉ Rᵉ)

is-set-subset-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) → is-setᵉ (subset-Ringᵉ lᵉ Rᵉ)
is-set-subset-Ringᵉ lᵉ Rᵉ =
  is-set-function-typeᵉ is-set-type-Propᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : subset-Ringᵉ l2ᵉ Rᵉ)
  where

  is-in-subset-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-subset-Ringᵉ = is-in-subtypeᵉ Sᵉ

  is-prop-is-in-subset-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (is-in-subset-Ringᵉ xᵉ)
  is-prop-is-in-subset-Ringᵉ = is-prop-is-in-subtypeᵉ Sᵉ

  type-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Ringᵉ = type-subtypeᵉ Sᵉ

  inclusion-subset-Ringᵉ : type-subset-Ringᵉ → type-Ringᵉ Rᵉ
  inclusion-subset-Ringᵉ = inclusion-subtypeᵉ Sᵉ

  ap-inclusion-subset-Ringᵉ :
    (xᵉ yᵉ : type-subset-Ringᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-subset-Ringᵉ xᵉ ＝ᵉ inclusion-subset-Ringᵉ yᵉ)
  ap-inclusion-subset-Ringᵉ = ap-inclusion-subtypeᵉ Sᵉ

  is-in-subset-inclusion-subset-Ringᵉ :
    (xᵉ : type-subset-Ringᵉ) → is-in-subset-Ringᵉ (inclusion-subset-Ringᵉ xᵉ)
  is-in-subset-inclusion-subset-Ringᵉ =
    is-in-subtype-inclusion-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-subset-Ringᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Ringᵉ yᵉ
  is-closed-under-eq-subset-Ringᵉ =
    is-closed-under-eq-subtypeᵉ Sᵉ

  is-closed-under-eq-subset-Ring'ᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-subset-Ringᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Ringᵉ xᵉ
  is-closed-under-eq-subset-Ring'ᵉ =
    is-closed-under-eq-subtype'ᵉ Sᵉ
```

### The condition that a subset contains zero

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Sᵉ : subset-Ringᵉ l2ᵉ Rᵉ)
  where

  contains-zero-subset-Ringᵉ : UUᵉ l2ᵉ
  contains-zero-subset-Ringᵉ = is-in-subset-Ringᵉ Rᵉ Sᵉ (zero-Ringᵉ Rᵉ)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Ringᵉ : UUᵉ l2ᵉ
  contains-one-subset-Ringᵉ = is-in-subset-Ringᵉ Rᵉ Sᵉ (one-Ringᵉ Rᵉ)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-addition-subset-Ringᵉ =
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    is-in-subset-Ringᵉ Rᵉ Sᵉ xᵉ → is-in-subset-Ringᵉ Rᵉ Sᵉ yᵉ →
    is-in-subset-Ringᵉ Rᵉ Sᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ)
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-negatives-subset-Ringᵉ =
    {xᵉ : type-Ringᵉ Rᵉ} →
    is-in-subset-Ringᵉ Rᵉ Sᵉ xᵉ → is-in-subset-Ringᵉ Rᵉ Sᵉ (neg-Ringᵉ Rᵉ xᵉ)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-multiplication-subset-Ringᵉ =
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-in-subset-Ringᵉ Rᵉ Sᵉ xᵉ → is-in-subset-Ringᵉ Rᵉ Sᵉ yᵉ →
    is-in-subset-Ringᵉ Rᵉ Sᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-left-multiplication-subset-Ring-Propᵉ =
    Π-Propᵉ
      ( type-Ringᵉ Rᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Ringᵉ Rᵉ)
          ( λ yᵉ →
            function-Propᵉ
              ( is-in-subset-Ringᵉ Rᵉ Sᵉ yᵉ)
              ( Sᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ))))

  is-closed-under-left-multiplication-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-left-multiplication-subset-Ringᵉ =
    type-Propᵉ is-closed-under-left-multiplication-subset-Ring-Propᵉ

  is-prop-is-closed-under-left-multiplication-subset-Ringᵉ :
    is-propᵉ is-closed-under-left-multiplication-subset-Ringᵉ
  is-prop-is-closed-under-left-multiplication-subset-Ringᵉ =
    is-prop-type-Propᵉ is-closed-under-left-multiplication-subset-Ring-Propᵉ
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-right-multiplication-subset-Ring-Propᵉ =
    Π-Propᵉ
      ( type-Ringᵉ Rᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Ringᵉ Rᵉ)
          ( λ yᵉ →
            function-Propᵉ
              ( is-in-subset-Ringᵉ Rᵉ Sᵉ xᵉ)
              ( Sᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ))))

  is-closed-under-right-multiplication-subset-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-closed-under-right-multiplication-subset-Ringᵉ =
    type-Propᵉ is-closed-under-right-multiplication-subset-Ring-Propᵉ

  is-prop-is-closed-under-right-multiplication-subset-Ringᵉ :
    is-propᵉ is-closed-under-right-multiplication-subset-Ringᵉ
  is-prop-is-closed-under-right-multiplication-subset-Ringᵉ =
    is-prop-type-Propᵉ is-closed-under-right-multiplication-subset-Ring-Propᵉ
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-additive-subgroup-subset-Ringᵉ :
    {l2ᵉ : Level} → subset-Ringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-additive-subgroup-subset-Ringᵉ = is-subgroup-Abᵉ (ab-Ringᵉ Rᵉ)

  is-prop-is-additive-subgroup-subset-Ringᵉ :
    {l2ᵉ : Level} (Aᵉ : subset-Ringᵉ l2ᵉ Rᵉ) →
    is-propᵉ (is-additive-subgroup-subset-Ringᵉ Aᵉ)
  is-prop-is-additive-subgroup-subset-Ringᵉ =
    is-prop-is-subgroup-Abᵉ (ab-Ringᵉ Rᵉ)
```