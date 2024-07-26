# Accessible elements with respect to relations

```agda
module order-theory.accessible-elements-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.negationᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `X`ᵉ with aᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ)
`_<ᵉ_ : Xᵉ → Xᵉ → Type`ᵉ weᵉ sayᵉ thatᵉ `xᵉ : X`ᵉ isᵉ **accessible**ᵉ ifᵉ `y`ᵉ isᵉ accessibleᵉ
forᵉ allᵉ `yᵉ <ᵉ x`.ᵉ Noteᵉ thatᵉ theᵉ predicateᵉ ofᵉ beingᵉ anᵉ accessibleᵉ elementᵉ isᵉ aᵉ
recursiveᵉ condition.ᵉ Theᵉ accessibilityᵉ predicateᵉ isᵉ thereforeᵉ implementedᵉ asᵉ anᵉ
inductive typeᵉ with oneᵉ constructorᵉ:

```text
  accessᵉ : ((yᵉ : Xᵉ) → yᵉ <ᵉ xᵉ → is-accessibleᵉ yᵉ) → is-accessibleᵉ xᵉ
```

## Definitions

### The predicate of being an accessible element with respect to a relation

```agda
module _
  {l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  data is-accessible-element-Relationᵉ (xᵉ : Xᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    accessᵉ :
      ({yᵉ : Xᵉ} → yᵉ <ᵉ xᵉ → is-accessible-element-Relationᵉ yᵉ) →
      is-accessible-element-Relationᵉ xᵉ
```

### Accessible elements with respect to relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  accessible-element-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  accessible-element-Relationᵉ = Σᵉ Xᵉ (is-accessible-element-Relationᵉ _<ᵉ_)
```

## Properties

### Any element in relation to an accessible element is accessible

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  is-accessible-element-is-related-to-accessible-element-Relationᵉ :
    {xᵉ : Xᵉ} → is-accessible-element-Relationᵉ _<ᵉ_ xᵉ →
    {yᵉ : Xᵉ} → yᵉ <ᵉ xᵉ → is-accessible-element-Relationᵉ _<ᵉ_ yᵉ
  is-accessible-element-is-related-to-accessible-element-Relationᵉ (accessᵉ fᵉ) =
    fᵉ
```

### An induction principle for accessible elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  ind-accessible-element-Relationᵉ :
    ( {xᵉ : Xᵉ} → is-accessible-element-Relationᵉ _<ᵉ_ xᵉ →
      ({yᵉ : Xᵉ} → yᵉ <ᵉ xᵉ → Pᵉ yᵉ) → Pᵉ xᵉ) →
    {xᵉ : Xᵉ} → is-accessible-element-Relationᵉ _<ᵉ_ xᵉ → Pᵉ xᵉ
  ind-accessible-element-Relationᵉ IHᵉ (accessᵉ fᵉ) =
    IHᵉ (accessᵉ fᵉ) (λ Hᵉ → ind-accessible-element-Relationᵉ IHᵉ (fᵉ Hᵉ))
```

### Accessibility is a property

**Proof:**ᵉ Considerᵉ anᵉ elementᵉ `xᵉ : X`ᵉ ofᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ binaryᵉ
relationᵉ `_<_`.ᵉ Weᵉ proveᵉ byᵉ doubleᵉ inductionᵉ thatᵉ anyᵉ twoᵉ elementsᵉ ofᵉ
`is-accessible-element-Relationᵉ _<ᵉ_ x`ᵉ areᵉ equal.ᵉ Itᵉ thereforeᵉ sufficesᵉ to proveᵉ
thatᵉ `accessᵉ fᵉ ＝ᵉ accessᵉ f'`ᵉ forᵉ anyᵉ twoᵉ elementsᵉ

```text
  fᵉ f'ᵉ : {yᵉ : Xᵉ} → yᵉ <ᵉ xᵉ → is-accessible-element-Relationᵉ _<ᵉ_ yᵉ
```

Theᵉ inductionᵉ hypothesesᵉ assertsᵉ thatᵉ anyᵉ twoᵉ elementsᵉ ofᵉ typeᵉ
`is-accessible-element-Relationᵉ _<ᵉ_ y`ᵉ areᵉ equalᵉ forᵉ anyᵉ `yᵉ <ᵉ x`.ᵉ Theᵉ inductionᵉ
hypothesisᵉ thereforeᵉ impliesᵉ thatᵉ anyᵉ twoᵉ elementsᵉ in theᵉ typeᵉ

```text
  {yᵉ : Xᵉ} → yᵉ <ᵉ xᵉ → is-accessible-element-Relationᵉ _<ᵉ_ yᵉ
```

areᵉ equal.ᵉ Thereforeᵉ itᵉ followsᵉ thatᵉ `fᵉ ＝ᵉ f'`,ᵉ andᵉ weᵉ concludeᵉ thatᵉ
`accessᵉ fᵉ ＝ᵉ accessᵉ f'`.ᵉ

```agda
module _ {l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ) where

  all-elements-equal-is-accessible-element-Relationᵉ :
    (xᵉ : Xᵉ) → all-elements-equalᵉ (is-accessible-element-Relationᵉ _<ᵉ_ xᵉ)
  all-elements-equal-is-accessible-element-Relationᵉ xᵉ (accessᵉ fᵉ) (accessᵉ f'ᵉ) =
    apᵉ
      ( accessᵉ)
      ( eq-htpy-implicitᵉ
        ( λ yᵉ →
          eq-htpyᵉ
            ( λ Hᵉ →
              all-elements-equal-is-accessible-element-Relationᵉ yᵉ
                ( fᵉ Hᵉ)
                ( f'ᵉ Hᵉ))))

  is-prop-is-accessible-element-Relationᵉ :
    (xᵉ : Xᵉ) → is-propᵉ (is-accessible-element-Relationᵉ _<ᵉ_ xᵉ)
  is-prop-is-accessible-element-Relationᵉ xᵉ =
    is-prop-all-elements-equalᵉ
      ( all-elements-equal-is-accessible-element-Relationᵉ xᵉ)

  is-accessible-element-prop-Relationᵉ : (xᵉ : Xᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-accessible-element-prop-Relationᵉ xᵉ) =
    is-accessible-element-Relationᵉ _<ᵉ_ xᵉ
  pr2ᵉ (is-accessible-element-prop-Relationᵉ xᵉ) =
    is-prop-is-accessible-element-Relationᵉ xᵉ
```

### If `x` is an `<`-accessible element, then `<` is antisymmetric at `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  is-asymmetric-is-accessible-element-Relationᵉ :
    {xᵉ : Xᵉ} → is-accessible-element-Relationᵉ _<ᵉ_ xᵉ →
    {yᵉ : Xᵉ} → xᵉ <ᵉ yᵉ → ¬ᵉ (yᵉ <ᵉ xᵉ)
  is-asymmetric-is-accessible-element-Relationᵉ (accessᵉ fᵉ) Hᵉ Kᵉ =
    is-asymmetric-is-accessible-element-Relationᵉ (fᵉ Kᵉ) Kᵉ Hᵉ
```

### If `x` is an `<`-accessible element, then `<` is irreflexive at `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_<ᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  is-irreflexive-is-accessible-element-Relationᵉ :
    {xᵉ : Xᵉ} → is-accessible-element-Relationᵉ _<ᵉ_ xᵉ → ¬ᵉ (xᵉ <ᵉ xᵉ)
  is-irreflexive-is-accessible-element-Relationᵉ aᵉ Hᵉ =
    is-asymmetric-is-accessible-element-Relationᵉ _<ᵉ_ aᵉ Hᵉ Hᵉ
```