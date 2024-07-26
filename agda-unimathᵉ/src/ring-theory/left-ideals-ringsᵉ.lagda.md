# Left ideals of rings

```agda
module ring-theory.left-ideals-ringsᵉ where
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

Aᵉ **leftᵉ ideal**ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ aᵉ leftᵉ submoduleᵉ ofᵉ
`R`.ᵉ

## Definitions

### Left ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-left-ideal-subset-Ringᵉ :
    {l2ᵉ : Level} → subset-Ringᵉ l2ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-left-ideal-subset-Ringᵉ Sᵉ =
    is-additive-subgroup-subset-Ringᵉ Rᵉ Sᵉ ×ᵉ
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ Sᵉ

  is-prop-is-left-ideal-subset-Ringᵉ :
    {l2ᵉ : Level} (Sᵉ : subset-Ringᵉ l2ᵉ Rᵉ) → is-propᵉ (is-left-ideal-subset-Ringᵉ Sᵉ)
  is-prop-is-left-ideal-subset-Ringᵉ Sᵉ =
    is-prop-productᵉ
      ( is-prop-is-additive-subgroup-subset-Ringᵉ Rᵉ Sᵉ)
      ( is-prop-is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ Sᵉ)

left-ideal-Ringᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
left-ideal-Ringᵉ lᵉ Rᵉ = Σᵉ (subset-Ringᵉ lᵉ Rᵉ) (is-left-ideal-subset-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  subset-left-ideal-Ringᵉ : subset-Ringᵉ l2ᵉ Rᵉ
  subset-left-ideal-Ringᵉ = pr1ᵉ Iᵉ

  is-in-left-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-left-ideal-Ringᵉ xᵉ = type-Propᵉ (subset-left-ideal-Ringᵉ xᵉ)

  type-left-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-left-ideal-Ringᵉ = type-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ

  inclusion-left-ideal-Ringᵉ : type-left-ideal-Ringᵉ → type-Ringᵉ Rᵉ
  inclusion-left-ideal-Ringᵉ = inclusion-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ

  ap-inclusion-left-ideal-Ringᵉ :
    (xᵉ yᵉ : type-left-ideal-Ringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-left-ideal-Ringᵉ xᵉ ＝ᵉ inclusion-left-ideal-Ringᵉ yᵉ
  ap-inclusion-left-ideal-Ringᵉ =
    ap-inclusion-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ

  is-in-subset-inclusion-left-ideal-Ringᵉ :
    (xᵉ : type-left-ideal-Ringᵉ) →
    is-in-left-ideal-Ringᵉ (inclusion-left-ideal-Ringᵉ xᵉ)
  is-in-subset-inclusion-left-ideal-Ringᵉ =
    is-in-subset-inclusion-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ

  is-closed-under-eq-left-ideal-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-left-ideal-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-left-ideal-Ringᵉ yᵉ
  is-closed-under-eq-left-ideal-Ringᵉ =
    is-closed-under-eq-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ

  is-closed-under-eq-left-ideal-Ring'ᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → is-in-left-ideal-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-left-ideal-Ringᵉ xᵉ
  is-closed-under-eq-left-ideal-Ring'ᵉ =
    is-closed-under-eq-subset-Ring'ᵉ Rᵉ subset-left-ideal-Ringᵉ

  is-left-ideal-subset-left-ideal-Ringᵉ :
    is-left-ideal-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-left-ideal-subset-left-ideal-Ringᵉ = pr2ᵉ Iᵉ

  is-additive-subgroup-subset-left-ideal-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-additive-subgroup-subset-left-ideal-Ringᵉ =
    pr1ᵉ is-left-ideal-subset-left-ideal-Ringᵉ

  contains-zero-left-ideal-Ringᵉ : is-in-left-ideal-Ringᵉ (zero-Ringᵉ Rᵉ)
  contains-zero-left-ideal-Ringᵉ =
    pr1ᵉ is-additive-subgroup-subset-left-ideal-Ringᵉ

  is-closed-under-addition-left-ideal-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-closed-under-addition-left-ideal-Ringᵉ =
    pr1ᵉ (pr2ᵉ is-additive-subgroup-subset-left-ideal-Ringᵉ)

  is-closed-under-negatives-left-ideal-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-closed-under-negatives-left-ideal-Ringᵉ =
    pr2ᵉ (pr2ᵉ is-additive-subgroup-subset-left-ideal-Ringᵉ)

  is-closed-under-left-multiplication-left-ideal-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-closed-under-left-multiplication-left-ideal-Ringᵉ =
    pr2ᵉ is-left-ideal-subset-left-ideal-Ringᵉ

  is-left-ideal-left-ideal-Ringᵉ :
    is-left-ideal-subset-Ringᵉ Rᵉ subset-left-ideal-Ringᵉ
  is-left-ideal-left-ideal-Ringᵉ = pr2ᵉ Iᵉ
```

## Properties

### Characterizing equality of left ideals in rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  has-same-elements-left-ideal-Ringᵉ :
    (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-left-ideal-Ringᵉ Jᵉ =
    has-same-elements-subtypeᵉ
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Jᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  refl-has-same-elements-left-ideal-Ringᵉ :
    has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ Iᵉ
  refl-has-same-elements-left-ideal-Ringᵉ =
    refl-has-same-elements-subtypeᵉ (subset-left-ideal-Ringᵉ Rᵉ Iᵉ)

  is-torsorial-has-same-elements-left-ideal-Ringᵉ :
    is-torsorialᵉ (has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ)
  is-torsorial-has-same-elements-left-ideal-Ringᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-has-same-elements-subtypeᵉ (subset-left-ideal-Ringᵉ Rᵉ Iᵉ))
      ( is-prop-is-left-ideal-subset-Ringᵉ Rᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( refl-has-same-elements-left-ideal-Ringᵉ)
      ( is-left-ideal-left-ideal-Ringᵉ Rᵉ Iᵉ)

  has-same-elements-eq-left-ideal-Ringᵉ :
    (Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) → has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  has-same-elements-eq-left-ideal-Ringᵉ .Iᵉ reflᵉ =
    refl-has-same-elements-left-ideal-Ringᵉ

  is-equiv-has-same-elements-eq-left-ideal-Ringᵉ :
    (Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) →
    is-equivᵉ (has-same-elements-eq-left-ideal-Ringᵉ Jᵉ)
  is-equiv-has-same-elements-eq-left-ideal-Ringᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-has-same-elements-left-ideal-Ringᵉ
      has-same-elements-eq-left-ideal-Ringᵉ

  extensionality-left-ideal-Ringᵉ :
    (Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) ≃ᵉ has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ
  pr1ᵉ (extensionality-left-ideal-Ringᵉ Jᵉ) =
    has-same-elements-eq-left-ideal-Ringᵉ Jᵉ
  pr2ᵉ (extensionality-left-ideal-Ringᵉ Jᵉ) =
    is-equiv-has-same-elements-eq-left-ideal-Ringᵉ Jᵉ

  eq-has-same-elements-left-ideal-Ringᵉ :
    (Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) →
    has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-has-same-elements-left-ideal-Ringᵉ Jᵉ =
    map-inv-equivᵉ (extensionality-left-ideal-Ringᵉ Jᵉ)
```