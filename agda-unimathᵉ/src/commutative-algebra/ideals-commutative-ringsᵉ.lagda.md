# Ideals of commutative rings

```agda
module commutative-algebra.ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Anᵉ **ideal**ᵉ in aᵉ commutativeᵉ ringᵉ isᵉ aᵉ two-sidedᵉ idealᵉ in theᵉ underlyingᵉ ring.ᵉ

## Definitions

### Ideals in commutative rings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  is-ideal-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-ideal-subset-Commutative-Ringᵉ =
    is-ideal-subset-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Sᵉ

  is-left-ideal-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-left-ideal-subset-Commutative-Ringᵉ =
    is-left-ideal-subset-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Sᵉ

  is-right-ideal-subset-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-right-ideal-subset-Commutative-Ringᵉ =
    is-right-ideal-subset-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Sᵉ

ideal-Commutative-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
ideal-Commutative-Ringᵉ l2ᵉ Rᵉ = ideal-Ringᵉ l2ᵉ (ring-Commutative-Ringᵉ Rᵉ)

left-ideal-Commutative-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
left-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ =
  left-ideal-Ringᵉ l2ᵉ (ring-Commutative-Ringᵉ Rᵉ)

right-ideal-Commutative-Ringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Ringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
right-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ =
  right-ideal-Ringᵉ l2ᵉ (ring-Commutative-Ringᵉ Rᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  subset-ideal-Commutative-Ringᵉ : subset-Commutative-Ringᵉ l2ᵉ Rᵉ
  subset-ideal-Commutative-Ringᵉ = pr1ᵉ Iᵉ

  is-in-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Rᵉ → UUᵉ l2ᵉ
  is-in-ideal-Commutative-Ringᵉ xᵉ = type-Propᵉ (subset-ideal-Commutative-Ringᵉ xᵉ)

  type-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-ideal-Commutative-Ringᵉ =
    type-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ

  inclusion-ideal-Commutative-Ringᵉ :
    type-ideal-Commutative-Ringᵉ → type-Commutative-Ringᵉ Rᵉ
  inclusion-ideal-Commutative-Ringᵉ =
    inclusion-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ

  ap-inclusion-ideal-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-ideal-Commutative-Ringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-ideal-Commutative-Ringᵉ xᵉ ＝ᵉ inclusion-ideal-Commutative-Ringᵉ yᵉ
  ap-inclusion-ideal-Commutative-Ringᵉ =
    ap-inclusion-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ

  is-in-subset-inclusion-ideal-Commutative-Ringᵉ :
    (xᵉ : type-ideal-Commutative-Ringᵉ) →
    is-in-ideal-Commutative-Ringᵉ (inclusion-ideal-Commutative-Ringᵉ xᵉ)
  is-in-subset-inclusion-ideal-Commutative-Ringᵉ =
    is-in-subset-inclusion-subset-Commutative-Ringᵉ Rᵉ
      subset-ideal-Commutative-Ringᵉ

  is-closed-under-eq-ideal-Commutative-Ringᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Rᵉ} → is-in-ideal-Commutative-Ringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Commutative-Ringᵉ yᵉ
  is-closed-under-eq-ideal-Commutative-Ringᵉ =
    is-closed-under-eq-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ

  is-closed-under-eq-ideal-Commutative-Ring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Ringᵉ Rᵉ} → is-in-ideal-Commutative-Ringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Commutative-Ringᵉ xᵉ
  is-closed-under-eq-ideal-Commutative-Ring'ᵉ =
    is-closed-under-eq-subset-Commutative-Ring'ᵉ Rᵉ subset-ideal-Commutative-Ringᵉ

  is-ideal-ideal-Commutative-Ringᵉ :
    is-ideal-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ
  is-ideal-ideal-Commutative-Ringᵉ =
    is-ideal-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  is-additive-subgroup-ideal-Commutative-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Rᵉ)
      ( subset-ideal-Commutative-Ringᵉ)
  is-additive-subgroup-ideal-Commutative-Ringᵉ =
    is-additive-subgroup-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  contains-zero-ideal-Commutative-Ringᵉ :
    contains-zero-subset-Commutative-Ringᵉ Rᵉ subset-ideal-Commutative-Ringᵉ
  contains-zero-ideal-Commutative-Ringᵉ =
    contains-zero-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  is-closed-under-addition-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Rᵉ
      subset-ideal-Commutative-Ringᵉ
  is-closed-under-addition-ideal-Commutative-Ringᵉ =
    is-closed-under-addition-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  is-closed-under-negatives-ideal-Commutative-Ringᵉ :
    {xᵉ : type-Commutative-Ringᵉ Rᵉ} →
    is-in-ideal-Commutative-Ringᵉ xᵉ →
    is-in-ideal-Commutative-Ringᵉ (neg-Commutative-Ringᵉ Rᵉ xᵉ)
  is-closed-under-negatives-ideal-Commutative-Ringᵉ =
    pr2ᵉ (pr2ᵉ is-additive-subgroup-ideal-Commutative-Ringᵉ)

  is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Rᵉ
      subset-ideal-Commutative-Ringᵉ
  is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ =
    is-closed-under-left-multiplication-ideal-Ringᵉ
      ( ring-Commutative-Ringᵉ Rᵉ)
      ( Iᵉ)

  is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Rᵉ
      subset-ideal-Commutative-Ringᵉ
  is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ =
    is-closed-under-right-multiplication-ideal-Ringᵉ
      ( ring-Commutative-Ringᵉ Rᵉ)
      ( Iᵉ)

  is-closed-under-powers-ideal-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Rᵉ) →
    is-in-ideal-Commutative-Ringᵉ xᵉ →
    is-in-ideal-Commutative-Ringᵉ (power-Commutative-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ)
  is-closed-under-powers-ideal-Commutative-Ringᵉ zero-ℕᵉ xᵉ Hᵉ = Hᵉ
  is-closed-under-powers-ideal-Commutative-Ringᵉ (succ-ℕᵉ nᵉ) xᵉ Hᵉ =
    is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ
      ( power-Commutative-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ)
      ( xᵉ)
      ( Hᵉ)

  left-ideal-ideal-Commutative-Ringᵉ : left-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ
  left-ideal-ideal-Commutative-Ringᵉ =
    left-ideal-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  right-ideal-ideal-Commutative-Ringᵉ : right-ideal-Commutative-Ringᵉ l2ᵉ Rᵉ
  right-ideal-ideal-Commutative-Ringᵉ =
    right-ideal-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

ideal-left-ideal-Commutative-Ringᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Rᵉ) →
  contains-zero-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-addition-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-negatives-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  ideal-Commutative-Ringᵉ l2ᵉ Rᵉ
pr1ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ) = Sᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) = zᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ)))) = aᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ)))) = nᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) = mᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) xᵉ yᵉ Hᵉ =
  is-closed-under-eq-subset-Commutative-Ringᵉ Rᵉ Sᵉ
    ( mᵉ yᵉ xᵉ Hᵉ)
    ( commutative-mul-Commutative-Ringᵉ Rᵉ yᵉ xᵉ)

ideal-right-ideal-Commutative-Ringᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Rᵉ) →
  contains-zero-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-addition-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-negatives-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Rᵉ Sᵉ →
  ideal-Commutative-Ringᵉ l2ᵉ Rᵉ
pr1ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ) = Sᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) = zᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ)))) = aᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ)))) = nᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) xᵉ yᵉ Hᵉ =
  is-closed-under-eq-subset-Commutative-Ringᵉ Rᵉ Sᵉ
    ( mᵉ yᵉ xᵉ Hᵉ)
    ( commutative-mul-Commutative-Ringᵉ Rᵉ yᵉ xᵉ)
pr2ᵉ (pr2ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Ringᵉ Rᵉ Sᵉ zᵉ aᵉ nᵉ mᵉ))) = mᵉ
```

## Properties

### Characterizing equality of ideals in commutative rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  has-same-elements-ideal-Commutative-Ringᵉ :
    (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Rᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  has-same-elements-ideal-Commutative-Ringᵉ =
    has-same-elements-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ)
  where

  refl-has-same-elements-ideal-Commutative-Ringᵉ :
    has-same-elements-ideal-Commutative-Ringᵉ Rᵉ Iᵉ Iᵉ
  refl-has-same-elements-ideal-Commutative-Ringᵉ =
    refl-has-same-elements-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  is-torsorial-has-same-elements-ideal-Commutative-Ringᵉ :
    is-torsorialᵉ (has-same-elements-ideal-Commutative-Ringᵉ Rᵉ Iᵉ)
  is-torsorial-has-same-elements-ideal-Commutative-Ringᵉ =
    is-torsorial-has-same-elements-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  has-same-elements-eq-ideal-Commutative-Ringᵉ :
    (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) → has-same-elements-ideal-Commutative-Ringᵉ Rᵉ Iᵉ Jᵉ
  has-same-elements-eq-ideal-Commutative-Ringᵉ =
    has-same-elements-eq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  is-equiv-has-same-elements-eq-ideal-Commutative-Ringᵉ :
    (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) →
    is-equivᵉ (has-same-elements-eq-ideal-Commutative-Ringᵉ Jᵉ)
  is-equiv-has-same-elements-eq-ideal-Commutative-Ringᵉ =
    is-equiv-has-same-elements-eq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  extensionality-ideal-Commutative-Ringᵉ :
    (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) →
    (Iᵉ ＝ᵉ Jᵉ) ≃ᵉ has-same-elements-ideal-Commutative-Ringᵉ Rᵉ Iᵉ Jᵉ
  extensionality-ideal-Commutative-Ringᵉ =
    extensionality-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ

  eq-has-same-elements-ideal-Commutative-Ringᵉ :
    (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) →
    has-same-elements-ideal-Commutative-Ringᵉ Rᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-has-same-elements-ideal-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ
```