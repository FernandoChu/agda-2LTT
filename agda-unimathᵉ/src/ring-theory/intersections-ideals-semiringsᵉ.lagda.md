# Intersections of ideals of semirings

```agda
module ring-theory.intersections-ideals-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ideals-semiringsᵉ
open import ring-theory.semiringsᵉ
open import ring-theory.subsets-semiringsᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ [ideals](ring-theory.ideals-semirings.mdᵉ) ofᵉ aᵉ
[semiring](ring-theory.semirings.mdᵉ) consistsᵉ ofᵉ theᵉ elementsᵉ containedᵉ in bothᵉ
ofᵉ them.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ)
  (Aᵉ : ideal-Semiringᵉ l2ᵉ Rᵉ) (Bᵉ : ideal-Semiringᵉ l3ᵉ Rᵉ)
  where

  subset-intersection-ideal-Semiringᵉ : subset-Semiringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  subset-intersection-ideal-Semiringᵉ =
    intersection-subtypeᵉ
      ( subset-ideal-Semiringᵉ Rᵉ Aᵉ)
      ( subset-ideal-Semiringᵉ Rᵉ Bᵉ)

  contains-zero-intersection-ideal-Semiringᵉ :
    contains-zero-subset-Semiringᵉ Rᵉ subset-intersection-ideal-Semiringᵉ
  pr1ᵉ contains-zero-intersection-ideal-Semiringᵉ =
    contains-zero-ideal-Semiringᵉ Rᵉ Aᵉ
  pr2ᵉ contains-zero-intersection-ideal-Semiringᵉ =
    contains-zero-ideal-Semiringᵉ Rᵉ Bᵉ

  is-closed-under-addition-intersection-ideal-Semiringᵉ :
    is-closed-under-addition-subset-Semiringᵉ Rᵉ
      subset-intersection-ideal-Semiringᵉ
  pr1ᵉ (is-closed-under-addition-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ Kᵉ) =
    is-closed-under-addition-ideal-Semiringᵉ Rᵉ Aᵉ xᵉ yᵉ (pr1ᵉ Hᵉ) (pr1ᵉ Kᵉ)
  pr2ᵉ (is-closed-under-addition-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ Kᵉ) =
    is-closed-under-addition-ideal-Semiringᵉ Rᵉ Bᵉ xᵉ yᵉ (pr2ᵉ Hᵉ) (pr2ᵉ Kᵉ)

  is-closed-under-left-multiplication-intersection-ideal-Semiringᵉ :
    is-closed-under-left-multiplication-subset-Semiringᵉ Rᵉ
      subset-intersection-ideal-Semiringᵉ
  pr1ᵉ (is-closed-under-left-multiplication-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-left-multiplication-ideal-Semiringᵉ Rᵉ Aᵉ xᵉ yᵉ (pr1ᵉ Hᵉ)
  pr2ᵉ (is-closed-under-left-multiplication-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-left-multiplication-ideal-Semiringᵉ Rᵉ Bᵉ xᵉ yᵉ (pr2ᵉ Hᵉ)

  is-closed-under-right-multiplication-intersection-ideal-Semiringᵉ :
    is-closed-under-right-multiplication-subset-Semiringᵉ Rᵉ
      subset-intersection-ideal-Semiringᵉ
  pr1ᵉ (is-closed-under-right-multiplication-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-right-multiplication-ideal-Semiringᵉ Rᵉ Aᵉ xᵉ yᵉ (pr1ᵉ Hᵉ)
  pr2ᵉ (is-closed-under-right-multiplication-intersection-ideal-Semiringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-right-multiplication-ideal-Semiringᵉ Rᵉ Bᵉ xᵉ yᵉ (pr2ᵉ Hᵉ)
```