# Algebras over rings

```agda
module ring-theory.algebras-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.modules-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Anᵉ **algebra**ᵉ overᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ consistsᵉ ofᵉ anᵉ
[`R`-module](ring-theory.modules-rings.mdᵉ) `M`ᵉ equippedᵉ with aᵉ binaryᵉ operationᵉ
`xᵉ yᵉ ↦ᵉ xyᵉ : Mᵉ → Mᵉ → M`ᵉ suchᵉ thatᵉ

```text
  (xy)zᵉ  = x(yzᵉ)
  r(xyᵉ)  = (rx)yᵉ
  r(xyᵉ)  = x(ryᵉ)
  (x+y)zᵉ = xz+yzᵉ
  x(y+zᵉ) = xy+xzᵉ
```

## Definitions

### Nonunital algebras over a ring

```agda
has-bilinear-mul-left-module-Ringᵉ :
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Mᵉ : left-module-Ringᵉ l2ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
has-bilinear-mul-left-module-Ringᵉ Rᵉ Mᵉ =
  Σᵉ ( (xᵉ yᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) → type-left-module-Ringᵉ Rᵉ Mᵉ)
    ( λ μᵉ →
      ( (xᵉ yᵉ zᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) → μᵉ (μᵉ xᵉ yᵉ) zᵉ ＝ᵉ μᵉ xᵉ (μᵉ yᵉ zᵉ)) ×ᵉ
      ( ( ( (rᵉ : type-Ringᵉ Rᵉ) (xᵉ yᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) →
            mul-left-module-Ringᵉ Rᵉ Mᵉ rᵉ (μᵉ xᵉ yᵉ) ＝ᵉ
            μᵉ (mul-left-module-Ringᵉ Rᵉ Mᵉ rᵉ xᵉ) yᵉ) ×ᵉ
          ( (rᵉ : type-Ringᵉ Rᵉ) (xᵉ yᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) →
            mul-left-module-Ringᵉ Rᵉ Mᵉ rᵉ (μᵉ xᵉ yᵉ) ＝ᵉ
            μᵉ xᵉ (mul-left-module-Ringᵉ Rᵉ Mᵉ rᵉ yᵉ))) ×ᵉ
        ( ( (xᵉ yᵉ zᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) →
            μᵉ (add-left-module-Ringᵉ Rᵉ Mᵉ xᵉ yᵉ) zᵉ ＝ᵉ
            add-left-module-Ringᵉ Rᵉ Mᵉ (μᵉ xᵉ zᵉ) (μᵉ yᵉ zᵉ)) ×ᵉ
          ( (xᵉ yᵉ zᵉ : type-left-module-Ringᵉ Rᵉ Mᵉ) →
            μᵉ xᵉ (add-left-module-Ringᵉ Rᵉ Mᵉ yᵉ zᵉ) ＝ᵉ
            add-left-module-Ringᵉ Rᵉ Mᵉ (μᵉ xᵉ yᵉ) (μᵉ xᵉ zᵉ)))))

Nonunital-Left-Algebra-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Nonunital-Left-Algebra-Ringᵉ l2ᵉ Rᵉ =
  Σᵉ ( left-module-Ringᵉ l2ᵉ Rᵉ) (has-bilinear-mul-left-module-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Aᵉ : Nonunital-Left-Algebra-Ringᵉ l2ᵉ Rᵉ)
  where

  left-module-Nonunital-Left-Algebra-Ringᵉ : left-module-Ringᵉ l2ᵉ Rᵉ
  left-module-Nonunital-Left-Algebra-Ringᵉ = pr1ᵉ Aᵉ

  bilinear-mul-Nonunital-Left-Algebra-Ringᵉ :
    has-bilinear-mul-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ
  bilinear-mul-Nonunital-Left-Algebra-Ringᵉ = pr2ᵉ Aᵉ

  type-Nonunital-Left-Algebra-Ringᵉ : UUᵉ l2ᵉ
  type-Nonunital-Left-Algebra-Ringᵉ =
    type-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  zero-Nonunital-Left-Algebra-Ringᵉ : type-Nonunital-Left-Algebra-Ringᵉ
  zero-Nonunital-Left-Algebra-Ringᵉ =
    zero-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ yᵉ : type-Nonunital-Left-Algebra-Ringᵉ) → type-Nonunital-Left-Algebra-Ringᵉ
  add-Nonunital-Left-Algebra-Ringᵉ =
    add-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  neg-Nonunital-Left-Algebra-Ringᵉ :
    type-Nonunital-Left-Algebra-Ringᵉ → type-Nonunital-Left-Algebra-Ringᵉ
  neg-Nonunital-Left-Algebra-Ringᵉ =
    neg-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  action-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) →
    type-Nonunital-Left-Algebra-Ringᵉ → type-Nonunital-Left-Algebra-Ringᵉ
  action-Nonunital-Left-Algebra-Ringᵉ =
    mul-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  mul-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ yᵉ : type-Nonunital-Left-Algebra-Ringᵉ) → type-Nonunital-Left-Algebra-Ringᵉ
  mul-Nonunital-Left-Algebra-Ringᵉ =
    pr1ᵉ bilinear-mul-Nonunital-Left-Algebra-Ringᵉ

  associative-add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    add-Nonunital-Left-Algebra-Ringᵉ (add-Nonunital-Left-Algebra-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Nonunital-Left-Algebra-Ringᵉ xᵉ (add-Nonunital-Left-Algebra-Ringᵉ yᵉ zᵉ)
  associative-add-Nonunital-Left-Algebra-Ringᵉ =
    associative-add-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  left-unit-law-add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    add-Nonunital-Left-Algebra-Ringᵉ zero-Nonunital-Left-Algebra-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Nonunital-Left-Algebra-Ringᵉ =
    left-unit-law-add-left-module-Ringᵉ Rᵉ left-module-Nonunital-Left-Algebra-Ringᵉ

  right-unit-law-add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    add-Nonunital-Left-Algebra-Ringᵉ xᵉ zero-Nonunital-Left-Algebra-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Nonunital-Left-Algebra-Ringᵉ =
    right-unit-law-add-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  left-inverse-law-add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    add-Nonunital-Left-Algebra-Ringᵉ (neg-Nonunital-Left-Algebra-Ringᵉ xᵉ) xᵉ ＝ᵉ
    zero-Nonunital-Left-Algebra-Ringᵉ
  left-inverse-law-add-Nonunital-Left-Algebra-Ringᵉ =
    left-inverse-law-add-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  right-inverse-law-add-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    add-Nonunital-Left-Algebra-Ringᵉ xᵉ (neg-Nonunital-Left-Algebra-Ringᵉ xᵉ) ＝ᵉ
    zero-Nonunital-Left-Algebra-Ringᵉ
  right-inverse-law-add-Nonunital-Left-Algebra-Ringᵉ =
    right-inverse-law-add-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  left-distributive-action-add-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ yᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ rᵉ
      ( add-Nonunital-Left-Algebra-Ringᵉ xᵉ yᵉ) ＝ᵉ
    add-Nonunital-Left-Algebra-Ringᵉ
      ( action-Nonunital-Left-Algebra-Ringᵉ rᵉ xᵉ)
      ( action-Nonunital-Left-Algebra-Ringᵉ rᵉ yᵉ)
  left-distributive-action-add-Nonunital-Left-Algebra-Ringᵉ =
    left-distributive-mul-add-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  right-distributive-action-add-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ (add-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ ＝ᵉ
    add-Nonunital-Left-Algebra-Ringᵉ
      ( action-Nonunital-Left-Algebra-Ringᵉ rᵉ xᵉ)
      ( action-Nonunital-Left-Algebra-Ringᵉ sᵉ xᵉ)
  right-distributive-action-add-Nonunital-Left-Algebra-Ringᵉ =
    right-distributive-mul-add-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  associative-action-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ sᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ (mul-Ringᵉ Rᵉ rᵉ sᵉ) xᵉ ＝ᵉ
    action-Nonunital-Left-Algebra-Ringᵉ rᵉ
      ( action-Nonunital-Left-Algebra-Ringᵉ sᵉ xᵉ)
  associative-action-Nonunital-Left-Algebra-Ringᵉ =
    associative-mul-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  left-zero-law-action-Nonunital-Left-Algebra-Ringᵉ :
    (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ (zero-Ringᵉ Rᵉ) xᵉ ＝ᵉ
    zero-Nonunital-Left-Algebra-Ringᵉ
  left-zero-law-action-Nonunital-Left-Algebra-Ringᵉ =
    left-zero-law-mul-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  right-zero-law-action-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ rᵉ zero-Nonunital-Left-Algebra-Ringᵉ ＝ᵉ
    zero-Nonunital-Left-Algebra-Ringᵉ
  right-zero-law-action-Nonunital-Left-Algebra-Ringᵉ =
    right-zero-law-mul-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  left-negative-law-action-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ (neg-Ringᵉ Rᵉ rᵉ) xᵉ ＝ᵉ
    neg-Nonunital-Left-Algebra-Ringᵉ (action-Nonunital-Left-Algebra-Ringᵉ rᵉ xᵉ)
  left-negative-law-action-Nonunital-Left-Algebra-Ringᵉ =
    left-negative-law-mul-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ

  right-negative-law-action-Nonunital-Left-Algebra-Ringᵉ :
    (rᵉ : type-Ringᵉ Rᵉ) (xᵉ : type-Nonunital-Left-Algebra-Ringᵉ) →
    action-Nonunital-Left-Algebra-Ringᵉ rᵉ (neg-Nonunital-Left-Algebra-Ringᵉ xᵉ) ＝ᵉ
    neg-Nonunital-Left-Algebra-Ringᵉ (action-Nonunital-Left-Algebra-Ringᵉ rᵉ xᵉ)
  right-negative-law-action-Nonunital-Left-Algebra-Ringᵉ =
    right-negative-law-mul-left-module-Ringᵉ Rᵉ
      left-module-Nonunital-Left-Algebra-Ringᵉ
```

### Unital algebras over a ring

Thisᵉ remainsᵉ to beᵉ defined.ᵉ
[#740](https://github.com/UniMath/agda-unimath/issues/740ᵉ)