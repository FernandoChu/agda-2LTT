# Right ideals of rings

```agda
module ring-theory.right-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Aᵉ **rightᵉ ideal**ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ aᵉ rightᵉ submoduleᵉ ofᵉ
`R`.ᵉ

## Definitions

### Right ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-right-ideal-subset-Ringᵉ :
    {l2ᵉ : Level} → subset-Ringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-right-ideal-subset-Ringᵉ Pᵉ =
    is-additive-subgroup-subset-Ringᵉ Rᵉ Pᵉ ×ᵉ
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ Pᵉ

  is-prop-is-right-ideal-subset-Ringᵉ :
    {l2ᵉ : Level} (Sᵉ : subset-Ringᵉ l2ᵉ Rᵉ) → is-propᵉ (is-right-ideal-subset-Ringᵉ Sᵉ)
  is-prop-is-right-ideal-subset-Ringᵉ Sᵉ =
    is-prop-productᵉ
      ( is-prop-is-additive-subgroup-subset-Ringᵉ Rᵉ Sᵉ)
      ( is-prop-is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ Sᵉ)

right-ideal-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
right-ideal-Ringᵉ lᵉ Rᵉ = Σᵉ (subset-Ringᵉ lᵉ Rᵉ) (is-right-ideal-subset-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  subset-right-ideal-Ringᵉ : subset-Ringᵉ l2ᵉ Rᵉ
  subset-right-ideal-Ringᵉ = pr1ᵉ Iᵉ

  is-in-right-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-right-ideal-Ringᵉ xᵉ = type-Propᵉ (subset-right-ideal-Ringᵉ xᵉ)

  type-right-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-right-ideal-Ringᵉ = type-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ

  inclusion-right-ideal-Ringᵉ : type-right-ideal-Ringᵉ → type-Ringᵉ Rᵉ
  inclusion-right-ideal-Ringᵉ = inclusion-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ

  ap-inclusion-right-ideal-Ringᵉ :
    (xᵉ yᵉ : type-right-ideal-Ringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-right-ideal-Ringᵉ xᵉ ＝ᵉ inclusion-right-ideal-Ringᵉ yᵉ
  ap-inclusion-right-ideal-Ringᵉ =
    ap-inclusion-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ

  is-in-subset-inclusion-right-ideal-Ringᵉ :
    (xᵉ : type-right-ideal-Ringᵉ) →
    is-in-right-ideal-Ringᵉ (inclusion-right-ideal-Ringᵉ xᵉ)
  is-in-subset-inclusion-right-ideal-Ringᵉ =
    is-in-subset-inclusion-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ

  is-closed-under-eq-right-ideal-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-right-ideal-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-right-ideal-Ringᵉ yᵉ
  is-closed-under-eq-right-ideal-Ringᵉ =
    is-closed-under-eq-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ

  is-closed-under-eq-right-ideal-Ring'ᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-right-ideal-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-right-ideal-Ringᵉ xᵉ
  is-closed-under-eq-right-ideal-Ring'ᵉ =
    is-closed-under-eq-subset-Ring'ᵉ Rᵉ subset-right-ideal-Ringᵉ

  is-right-ideal-subset-right-ideal-Ringᵉ :
    is-right-ideal-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-right-ideal-subset-right-ideal-Ringᵉ = pr2ᵉ Iᵉ

  is-additive-subgroup-subset-right-ideal-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-additive-subgroup-subset-right-ideal-Ringᵉ =
    pr1ᵉ is-right-ideal-subset-right-ideal-Ringᵉ

  contains-zero-right-ideal-Ringᵉ : is-in-right-ideal-Ringᵉ (zero-Ringᵉ Rᵉ)
  contains-zero-right-ideal-Ringᵉ =
    pr1ᵉ is-additive-subgroup-subset-right-ideal-Ringᵉ

  is-closed-under-addition-right-ideal-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-closed-under-addition-right-ideal-Ringᵉ =
    pr1ᵉ (pr2ᵉ is-additive-subgroup-subset-right-ideal-Ringᵉ)

  is-closed-under-negatives-right-ideal-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-closed-under-negatives-right-ideal-Ringᵉ =
    pr2ᵉ (pr2ᵉ is-additive-subgroup-subset-right-ideal-Ringᵉ)

  is-closed-under-right-multiplication-right-ideal-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-closed-under-right-multiplication-right-ideal-Ringᵉ =
    pr2ᵉ is-right-ideal-subset-right-ideal-Ringᵉ

  is-right-ideal-right-ideal-Ringᵉ :
    is-right-ideal-subset-Ringᵉ Rᵉ subset-right-ideal-Ringᵉ
  is-right-ideal-right-ideal-Ringᵉ = pr2ᵉ Iᵉ
```

## Properties

### Characterizing equality of right ideals in rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  has-same-elements-right-ideal-Ringᵉ :
    (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-right-ideal-Ringᵉ Jᵉ =
    has-same-elements-subtypeᵉ
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Jᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  refl-has-same-elements-right-ideal-Ringᵉ :
    has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ Iᵉ
  refl-has-same-elements-right-ideal-Ringᵉ =
    refl-has-same-elements-subtypeᵉ (subset-right-ideal-Ringᵉ Rᵉ Iᵉ)

  is-torsorial-has-same-elements-right-ideal-Ringᵉ :
    is-torsorialᵉ (has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ)
  is-torsorial-has-same-elements-right-ideal-Ringᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-subtypeᵉ (subset-right-ideal-Ringᵉ Rᵉ Iᵉ))
      ( is-prop-is-right-ideal-subset-Ringᵉ Rᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( refl-has-same-elements-right-ideal-Ringᵉ)
      ( is-right-ideal-right-ideal-Ringᵉ Rᵉ Iᵉ)

  has-same-elements-eq-right-ideal-Ringᵉ :
    (Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) → has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  has-same-elements-eq-right-ideal-Ringᵉ .Iᵉ reflᵉ =
    refl-has-same-elements-right-ideal-Ringᵉ

  is-equiv-has-same-elements-eq-right-ideal-Ringᵉ :
    (Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    is-equivᵉ (has-same-elements-eq-right-ideal-Ringᵉ Jᵉ)
  is-equiv-has-same-elements-eq-right-ideal-Ringᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-has-same-elements-right-ideal-Ringᵉ
      has-same-elements-eq-right-ideal-Ringᵉ

  extensionality-right-ideal-Ringᵉ :
    (Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) ≃ᵉ has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  pr1ᵉ (extensionality-right-ideal-Ringᵉ Jᵉ) =
    has-same-elements-eq-right-ideal-Ringᵉ Jᵉ
  pr2ᵉ (extensionality-right-ideal-Ringᵉ Jᵉ) =
    is-equiv-has-same-elements-eq-right-ideal-Ringᵉ Jᵉ

  eq-has-same-elements-right-ideal-Ringᵉ :
    (Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-has-same-elements-right-ideal-Ringᵉ Jᵉ =
    map-inv-equivᵉ (extensionality-right-ideal-Ringᵉ Jᵉ)
```