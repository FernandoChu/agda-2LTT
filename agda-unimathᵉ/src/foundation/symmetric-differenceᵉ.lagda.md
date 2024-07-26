# Symmetric difference of subtypes

```agda
module foundation.symmetric-differenceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.exclusive-sumᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.decidable-propositionsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ **symmetricᵉ difference**ᵉ ofᵉ twoᵉ [subtypes](foundation-core.subtypes.mdᵉ) `A`ᵉ
andᵉ `B`ᵉ isᵉ theᵉ subtypeᵉ thatᵉ containsᵉ theᵉ elementsᵉ thatᵉ areᵉ eitherᵉ in `A`ᵉ orᵉ in
`B`ᵉ butᵉ notᵉ in both.ᵉ

## Definition

```agda
module _
  {lᵉ l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  symmetric-difference-subtypeᵉ :
    subtypeᵉ l1ᵉ Xᵉ → subtypeᵉ l2ᵉ Xᵉ → subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  symmetric-difference-subtypeᵉ Pᵉ Qᵉ xᵉ =
    exclusive-sum-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ)

  symmetric-difference-decidable-subtypeᵉ :
    decidable-subtypeᵉ l1ᵉ Xᵉ → decidable-subtypeᵉ l2ᵉ Xᵉ →
    decidable-subtypeᵉ (l1ᵉ ⊔ l2ᵉ) Xᵉ
  symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ xᵉ =
    exclusive-sum-Decidable-Propᵉ (Pᵉ xᵉ) (Qᵉ xᵉ)
```

## Properties

### The coproduct of two decidable subtypes is equivalent to their symmetric difference plus two times their intersection

Thisᵉ isᵉ closelyᵉ relatedᵉ to theᵉ _inclusion-exclusionᵉ principle_.ᵉ

```agda
module _
  {lᵉ l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  left-cases-equiv-symmetric-differenceᵉ :
    (Pᵉ : decidable-subtypeᵉ l1ᵉ Xᵉ) (Qᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
    (xᵉ : Xᵉ) → type-Decidable-Propᵉ (Pᵉ xᵉ) →
    is-decidableᵉ (type-Decidable-Propᵉ (Qᵉ xᵉ)) →
    ( type-decidable-subtypeᵉ
      ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
    ( ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
      ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))
  left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ (inlᵉ qᵉ) =
    inrᵉ (inlᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))
  left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ (inrᵉ nqᵉ) =
    inlᵉ (pairᵉ xᵉ (inlᵉ (pairᵉ pᵉ nqᵉ)))

  right-cases-equiv-symmetric-differenceᵉ :
    ( Pᵉ : decidable-subtypeᵉ l1ᵉ Xᵉ) (Qᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
    (xᵉ : Xᵉ) → type-Decidable-Propᵉ (Qᵉ xᵉ) →
    is-decidableᵉ (type-Decidable-Propᵉ (Pᵉ xᵉ)) →
    ( type-decidable-subtypeᵉ
      ( symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
    ( ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
      ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))
  right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ (inlᵉ pᵉ) =
    inrᵉ (inrᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))
  right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ (inrᵉ npᵉ) =
    inlᵉ (pairᵉ xᵉ (inrᵉ (pairᵉ qᵉ npᵉ)))

  equiv-symmetric-differenceᵉ :
    (Pᵉ : decidable-subtypeᵉ l1ᵉ Xᵉ) (Qᵉ : decidable-subtypeᵉ l2ᵉ Xᵉ) →
    ( (type-decidable-subtypeᵉ Pᵉ +ᵉ type-decidable-subtypeᵉ Qᵉ) ≃ᵉ
      ( ( type-decidable-subtypeᵉ (symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
        ( ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
          ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))))
  pr1ᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ) (inlᵉ (pairᵉ xᵉ pᵉ)) =
    left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ
      ( is-decidable-Decidable-Propᵉ (Qᵉ xᵉ))
  pr1ᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ) (inrᵉ (pairᵉ xᵉ qᵉ)) =
    right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ
      ( is-decidable-Decidable-Propᵉ (Pᵉ xᵉ))
  pr2ᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ) =
    is-equiv-is-invertibleᵉ iᵉ rᵉ sᵉ
    where
    iᵉ :
      ( type-decidable-subtypeᵉ (symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
      ( ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
        ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ))) →
      type-decidable-subtypeᵉ Pᵉ +ᵉ type-decidable-subtypeᵉ Qᵉ
    iᵉ (inlᵉ (pairᵉ xᵉ (inlᵉ (pairᵉ pᵉ nqᵉ)))) = inlᵉ (pairᵉ xᵉ pᵉ)
    iᵉ (inlᵉ (pairᵉ xᵉ (inrᵉ (pairᵉ qᵉ npᵉ)))) = inrᵉ (pairᵉ xᵉ qᵉ)
    iᵉ (inrᵉ (inlᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))) = inlᵉ (pairᵉ xᵉ pᵉ)
    iᵉ (inrᵉ (inrᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))) = inrᵉ (pairᵉ xᵉ qᵉ)
    rᵉ :
      (Cᵉ :
        ( type-decidable-subtypeᵉ (symmetric-difference-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
        ( ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)) +ᵉ
          ( type-decidable-subtypeᵉ (intersection-decidable-subtypeᵉ Pᵉ Qᵉ)))) →
      ((pr1ᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ)) ∘ᵉ iᵉ) Cᵉ ＝ᵉ Cᵉ
    rᵉ (inlᵉ (pairᵉ xᵉ (inlᵉ (pairᵉ pᵉ nqᵉ)))) =
      trᵉ
        ( λ q'ᵉ →
          ( left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ q'ᵉ) ＝ᵉ
          ( inlᵉ (pairᵉ xᵉ (inlᵉ (pairᵉ pᵉ nqᵉ)))))
        ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-type-Decidable-Propᵉ (Qᵉ xᵉ))))
        ( reflᵉ)
    rᵉ (inlᵉ (pairᵉ xᵉ (inrᵉ (pairᵉ qᵉ npᵉ)))) =
      trᵉ
        ( λ p'ᵉ →
          ( right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ p'ᵉ) ＝ᵉ
          ( inlᵉ (pairᵉ xᵉ (inrᵉ (pairᵉ qᵉ npᵉ)))))
        ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-type-Decidable-Propᵉ (Pᵉ xᵉ))))
        ( reflᵉ)
    rᵉ (inrᵉ (inlᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))) =
      trᵉ
        ( λ q'ᵉ →
          (left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ q'ᵉ) ＝ᵉ
          (inrᵉ (inlᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))))
        ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-type-Decidable-Propᵉ (Qᵉ xᵉ))))
        ( reflᵉ)
    rᵉ (inrᵉ (inrᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))) =
      trᵉ
        ( λ p'ᵉ →
          (right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ p'ᵉ) ＝ᵉ
          (inrᵉ (inrᵉ (pairᵉ xᵉ (pairᵉ pᵉ qᵉ)))))
        ( eq-is-propᵉ (is-prop-is-decidableᵉ (is-prop-type-Decidable-Propᵉ (Pᵉ xᵉ))))
        ( reflᵉ)
    left-cases-sᵉ :
      (xᵉ : Xᵉ)
      (pᵉ : type-Decidable-Propᵉ (Pᵉ xᵉ))
      (qᵉ : is-decidableᵉ (type-Decidable-Propᵉ (Qᵉ xᵉ))) →
      iᵉ (left-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ pᵉ qᵉ) ＝ᵉ inlᵉ (pairᵉ xᵉ pᵉ)
    left-cases-sᵉ xᵉ pᵉ (inlᵉ qᵉ) = reflᵉ
    left-cases-sᵉ xᵉ pᵉ (inrᵉ nqᵉ) = reflᵉ
    right-cases-sᵉ :
      (xᵉ : Xᵉ)
      (qᵉ : type-Decidable-Propᵉ (Qᵉ xᵉ))
      (pᵉ : is-decidableᵉ (type-Decidable-Propᵉ (Pᵉ xᵉ))) →
      iᵉ (right-cases-equiv-symmetric-differenceᵉ Pᵉ Qᵉ xᵉ qᵉ pᵉ) ＝ᵉ inrᵉ (pairᵉ xᵉ qᵉ)
    right-cases-sᵉ xᵉ qᵉ (inlᵉ pᵉ) = reflᵉ
    right-cases-sᵉ xᵉ qᵉ (inrᵉ npᵉ) = reflᵉ
    sᵉ :
      (Cᵉ : type-decidable-subtypeᵉ Pᵉ +ᵉ type-decidable-subtypeᵉ Qᵉ) →
      (iᵉ ∘ᵉ pr1ᵉ (equiv-symmetric-differenceᵉ Pᵉ Qᵉ)) Cᵉ ＝ᵉ Cᵉ
    sᵉ (inlᵉ (pairᵉ xᵉ pᵉ)) =
      left-cases-sᵉ xᵉ pᵉ (is-decidable-Decidable-Propᵉ (Qᵉ xᵉ))
    sᵉ (inrᵉ (pairᵉ xᵉ qᵉ)) =
      right-cases-sᵉ xᵉ qᵉ (is-decidable-Decidable-Propᵉ (Pᵉ xᵉ))
```

## See also

-ᵉ [Complementsᵉ ofᵉ subtypes](foundation.complements-subtypes.mdᵉ)