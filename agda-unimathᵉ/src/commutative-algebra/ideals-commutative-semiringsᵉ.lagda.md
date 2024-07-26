# Ideals of commutative semirings

```agda
module commutative-algebra.ideals-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.subsets-commutative-semiringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ideals-semiringsᵉ
```

</details>

## Idea

Anᵉ **ideal**ᵉ in aᵉ commutativeᵉ semiringᵉ isᵉ aᵉ two-sidedᵉ idealᵉ in theᵉ underlyingᵉ
semiring.ᵉ

## Definitions

### Ideals in commutative semirings

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ)
  where

  is-ideal-subset-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-ideal-subset-Commutative-Semiringᵉ =
    is-ideal-subset-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Sᵉ

ideal-Commutative-Semiringᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Commutative-Semiringᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
ideal-Commutative-Semiringᵉ l2ᵉ Aᵉ =
  ideal-Semiringᵉ l2ᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Semiringᵉ l2ᵉ Aᵉ)
  where

  subset-ideal-Commutative-Semiringᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ
  subset-ideal-Commutative-Semiringᵉ =
    subset-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-in-ideal-Commutative-Semiringᵉ : type-Commutative-Semiringᵉ Aᵉ → UUᵉ l2ᵉ
  is-in-ideal-Commutative-Semiringᵉ =
    is-in-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-prop-is-in-ideal-Commutative-Semiringᵉ :
    (xᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    is-propᵉ (is-in-ideal-Commutative-Semiringᵉ xᵉ)
  is-prop-is-in-ideal-Commutative-Semiringᵉ =
    is-prop-is-in-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  type-ideal-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-ideal-Commutative-Semiringᵉ =
    type-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  inclusion-ideal-Commutative-Semiringᵉ :
    type-ideal-Commutative-Semiringᵉ → type-Commutative-Semiringᵉ Aᵉ
  inclusion-ideal-Commutative-Semiringᵉ =
    inclusion-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  ap-inclusion-ideal-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-ideal-Commutative-Semiringᵉ) → xᵉ ＝ᵉ yᵉ →
    inclusion-ideal-Commutative-Semiringᵉ xᵉ ＝ᵉ
    inclusion-ideal-Commutative-Semiringᵉ yᵉ
  ap-inclusion-ideal-Commutative-Semiringᵉ =
    ap-inclusion-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-in-subset-inclusion-ideal-Commutative-Semiringᵉ :
    (xᵉ : type-ideal-Commutative-Semiringᵉ) →
    is-in-ideal-Commutative-Semiringᵉ (inclusion-ideal-Commutative-Semiringᵉ xᵉ)
  is-in-subset-inclusion-ideal-Commutative-Semiringᵉ =
    is-in-subset-inclusion-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-closed-under-eq-ideal-Commutative-Semiringᵉ :
    {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} → is-in-ideal-Commutative-Semiringᵉ xᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Commutative-Semiringᵉ yᵉ
  is-closed-under-eq-ideal-Commutative-Semiringᵉ =
    is-closed-under-eq-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-closed-under-eq-ideal-Commutative-Semiring'ᵉ :
    {xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ} → is-in-ideal-Commutative-Semiringᵉ yᵉ →
    (xᵉ ＝ᵉ yᵉ) → is-in-ideal-Commutative-Semiringᵉ xᵉ
  is-closed-under-eq-ideal-Commutative-Semiring'ᵉ =
    is-closed-under-eq-ideal-Semiring'ᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-ideal-subset-ideal-Commutative-Semiringᵉ :
    is-ideal-subset-Commutative-Semiringᵉ Aᵉ subset-ideal-Commutative-Semiringᵉ
  is-ideal-subset-ideal-Commutative-Semiringᵉ =
    is-ideal-subset-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-additive-submonoid-ideal-Commutative-Semiringᵉ :
    is-additive-submonoid-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( subset-ideal-Commutative-Semiringᵉ)
  is-additive-submonoid-ideal-Commutative-Semiringᵉ =
    is-additive-submonoid-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  contains-zero-ideal-Commutative-Semiringᵉ :
    contains-zero-subset-Commutative-Semiringᵉ Aᵉ
      subset-ideal-Commutative-Semiringᵉ
  contains-zero-ideal-Commutative-Semiringᵉ =
    contains-zero-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-closed-under-addition-ideal-Commutative-Semiringᵉ :
    is-closed-under-addition-subset-Commutative-Semiringᵉ Aᵉ
      subset-ideal-Commutative-Semiringᵉ
  is-closed-under-addition-ideal-Commutative-Semiringᵉ =
    is-closed-under-addition-ideal-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ) Iᵉ

  is-closed-under-left-multiplication-ideal-Commutative-Semiringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Semiringᵉ Aᵉ
      subset-ideal-Commutative-Semiringᵉ
  is-closed-under-left-multiplication-ideal-Commutative-Semiringᵉ =
    is-closed-under-left-multiplication-ideal-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( Iᵉ)

  is-closed-under-right-multiplication-ideal-Commutative-Semiringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Semiringᵉ Aᵉ
      subset-ideal-Commutative-Semiringᵉ
  is-closed-under-right-multiplication-ideal-Commutative-Semiringᵉ =
    is-closed-under-right-multiplication-ideal-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( Iᵉ)

ideal-left-ideal-Commutative-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ) →
  contains-zero-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  is-closed-under-addition-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  is-closed-under-left-multiplication-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  ideal-Commutative-Semiringᵉ l2ᵉ Aᵉ
pr1ᵉ (ideal-left-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ) = Sᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = zᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = aᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = mᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (ideal-left-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) xᵉ yᵉ Hᵉ =
  is-closed-under-eq-subset-Commutative-Semiringᵉ Aᵉ Sᵉ
    ( mᵉ yᵉ xᵉ Hᵉ)
    ( commutative-mul-Commutative-Semiringᵉ Aᵉ yᵉ xᵉ)

ideal-right-ideal-Commutative-Semiringᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Semiringᵉ l2ᵉ Aᵉ) →
  contains-zero-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  is-closed-under-addition-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  is-closed-under-right-multiplication-subset-Commutative-Semiringᵉ Aᵉ Sᵉ →
  ideal-Commutative-Semiringᵉ l2ᵉ Aᵉ
pr1ᵉ (ideal-right-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ) = Sᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = zᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = aᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) xᵉ yᵉ Hᵉ =
  is-closed-under-eq-subset-Commutative-Semiringᵉ Aᵉ Sᵉ
    ( mᵉ yᵉ xᵉ Hᵉ)
    ( commutative-mul-Commutative-Semiringᵉ Aᵉ yᵉ xᵉ)
pr2ᵉ (pr2ᵉ (pr2ᵉ (ideal-right-ideal-Commutative-Semiringᵉ Aᵉ Sᵉ zᵉ aᵉ mᵉ))) = mᵉ
```