# Bezout's lemma in the integers

```agda
module elementary-number-theory.bezouts-lemma-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.bezouts-lemma-natural-numbersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.distance-integersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.greatest-common-divisor-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
```

</details>

## Lemma

```agda
bezouts-lemma-eqn-to-intᵉ :
  (xᵉ yᵉ : ℤᵉ) → (Hᵉ : is-nonzero-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ))) →
  nat-gcd-ℤᵉ xᵉ yᵉ ＝ᵉ
  dist-ℕᵉ
    ( abs-ℤᵉ
      ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ) *ℤᵉ xᵉ))
    ( abs-ℤᵉ
      ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ) *ℤᵉ yᵉ))
bezouts-lemma-eqn-to-intᵉ xᵉ yᵉ Hᵉ =
  equational-reasoningᵉ
    nat-gcd-ℤᵉ xᵉ yᵉ
    ＝ᵉ dist-ℕᵉ
      ( (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ) *ℕᵉ (abs-ℤᵉ xᵉ))
      ( (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ) *ℕᵉ (abs-ℤᵉ yᵉ))
      byᵉ (invᵉ (bezouts-lemma-eqn-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
    ＝ᵉ dist-ℕᵉ
        ( mul-ℕᵉ
          ( abs-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
          ( abs-ℤᵉ xᵉ))
        ( mul-ℕᵉ
          ( minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)
          ( abs-ℤᵉ yᵉ))
      byᵉ
        ( apᵉ
          ( λ Kᵉ →
            dist-ℕᵉ
              ( Kᵉ *ℕᵉ (abs-ℤᵉ xᵉ))
              ( mul-ℕᵉ
                ( minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)
                ( abs-ℤᵉ yᵉ)))
          ( invᵉ
            ( abs-int-ℕᵉ
              ( minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))))
    ＝ᵉ dist-ℕᵉ
        ( mul-ℕᵉ
          ( abs-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
          ( abs-ℤᵉ xᵉ))
        ( mul-ℕᵉ
          ( abs-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
          ( abs-ℤᵉ yᵉ))
      byᵉ
        ( apᵉ
          ( λ Kᵉ →
            dist-ℕᵉ
              ( mul-ℕᵉ
                ( abs-ℤᵉ
                  ( int-ℕᵉ
                    ( minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
                ( abs-ℤᵉ xᵉ))
              ( Kᵉ *ℕᵉ (abs-ℤᵉ yᵉ)))
        (invᵉ
          ( abs-int-ℕᵉ
            ( minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))))
    ＝ᵉ dist-ℕᵉ
        ( abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
            ( xᵉ)))
        ( mul-ℕᵉ
          ( abs-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
          ( abs-ℤᵉ yᵉ))
      byᵉ
        ( apᵉ
          ( λ Kᵉ →
            dist-ℕᵉ
              ( Kᵉ)
              ( mul-ℕᵉ
                ( abs-ℤᵉ
                  ( int-ℕᵉ
                    ( minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ)))
                ( abs-ℤᵉ yᵉ)))
          ( invᵉ
            ( multiplicative-abs-ℤᵉ
              ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
              ( xᵉ))))
    ＝ᵉ dist-ℕᵉ
        ( abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
            ( xᵉ)))
        ( abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
            ( yᵉ)))
      byᵉ
        ( apᵉ
          ( dist-ℕᵉ
            ( abs-ℤᵉ
              ( mul-ℤᵉ
                ( int-ℕᵉ
                  ( minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
                ( xᵉ))))
          ( invᵉ
            ( multiplicative-abs-ℤᵉ
              ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Hᵉ))
              ( yᵉ))))

refactor-pos-condᵉ :
  (xᵉ yᵉ : ℤᵉ) → (Hᵉ : is-positive-ℤᵉ xᵉ) → (Kᵉ : is-positive-ℤᵉ yᵉ) →
  is-nonzero-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ))
refactor-pos-condᵉ xᵉ yᵉ Hᵉ _ =
  is-nonzero-abs-ℤᵉ xᵉ Hᵉ ∘ᵉ is-zero-left-is-zero-add-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ)

bezouts-lemma-refactor-hypothesesᵉ :
  (xᵉ yᵉ : ℤᵉ) (Hᵉ : is-positive-ℤᵉ xᵉ) (Kᵉ : is-positive-ℤᵉ yᵉ) →
  nat-gcd-ℤᵉ xᵉ yᵉ ＝ᵉ
  abs-ℤᵉ
    ( diff-ℤᵉ
      ( mul-ℤᵉ
        ( int-ℕᵉ
          ( minimal-positive-distance-x-coeffᵉ
            ( abs-ℤᵉ xᵉ)
            ( abs-ℤᵉ yᵉ)
            ( refactor-pos-condᵉ xᵉ yᵉ Hᵉ Kᵉ)))
        ( xᵉ))
      ( mul-ℤᵉ
        ( int-ℕᵉ
          ( minimal-positive-distance-y-coeffᵉ
            ( abs-ℤᵉ xᵉ)
            ( abs-ℤᵉ yᵉ)
            ( refactor-pos-condᵉ xᵉ yᵉ Hᵉ Kᵉ)))
        ( yᵉ)))
bezouts-lemma-refactor-hypothesesᵉ xᵉ yᵉ Hᵉ Kᵉ =
  equational-reasoningᵉ
    nat-gcd-ℤᵉ xᵉ yᵉ
    ＝ᵉ dist-ℕᵉ
        ( abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
            ( xᵉ)))
        ( abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
            ( yᵉ)))
      byᵉ bezouts-lemma-eqn-to-intᵉ xᵉ yᵉ Pᵉ
    ＝ᵉ dist-ℤᵉ
        ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ) *ℤᵉ xᵉ)
        ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ) *ℤᵉ yᵉ)
      byᵉ
        dist-abs-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
            ( xᵉ))
          ( mul-ℤᵉ
            ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
            ( yᵉ))
        x-product-nonnegᵉ y-product-nonnegᵉ
  where
  Pᵉ : is-nonzero-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ))
  Pᵉ = (refactor-pos-condᵉ xᵉ yᵉ Hᵉ Kᵉ)
  x-product-nonnegᵉ :
    is-nonnegative-ℤᵉ
      ( int-ℕᵉ (minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ) *ℤᵉ xᵉ)
  x-product-nonnegᵉ =
    is-nonnegative-mul-ℤᵉ
      ( is-nonnegative-int-ℕᵉ
        ( minimal-positive-distance-x-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
      ( is-nonnegative-is-positive-ℤᵉ Hᵉ)
  y-product-nonnegᵉ :
    is-nonnegative-ℤᵉ
      ( int-ℕᵉ (minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ) *ℤᵉ yᵉ)
  y-product-nonnegᵉ =
    is-nonnegative-mul-ℤᵉ
      ( is-nonnegative-int-ℕᵉ
        ( minimal-positive-distance-y-coeffᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) Pᵉ))
      ( is-nonnegative-is-positive-ℤᵉ Kᵉ)

bezouts-lemma-pos-intsᵉ :
  (xᵉ yᵉ : ℤᵉ) (Hᵉ : is-positive-ℤᵉ xᵉ) (Kᵉ : is-positive-ℤᵉ yᵉ) →
  Σᵉ ℤᵉ (λ sᵉ → Σᵉ ℤᵉ (λ tᵉ → (sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ))
bezouts-lemma-pos-intsᵉ xᵉ yᵉ Hᵉ Kᵉ =
  sx-ty-nonneg-case-splitᵉ
    ( decide-is-nonnegative-is-nonnegative-neg-ℤᵉ {(sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)})
  where
  sᵉ : ℤᵉ
  sᵉ = int-ℕᵉ (minimal-positive-distance-x-coeffᵉ
    (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) (refactor-pos-condᵉ xᵉ yᵉ Hᵉ Kᵉ))
  tᵉ : ℤᵉ
  tᵉ = int-ℕᵉ (minimal-positive-distance-y-coeffᵉ
    (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) (refactor-pos-condᵉ xᵉ yᵉ Hᵉ Kᵉ))

  sx-ty-nonneg-case-splitᵉ :
    ( is-nonnegative-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)) +ᵉ
      is-nonnegative-ℤᵉ (neg-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)))) →
    Σᵉ ℤᵉ (λ sᵉ → Σᵉ ℤᵉ (λ tᵉ → (sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ))
  pr1ᵉ (sx-ty-nonneg-case-splitᵉ (inlᵉ posᵉ)) = sᵉ
  pr1ᵉ (pr2ᵉ (sx-ty-nonneg-case-splitᵉ (inlᵉ posᵉ))) = neg-ℤᵉ tᵉ
  pr2ᵉ (pr2ᵉ (sx-ty-nonneg-case-splitᵉ (inlᵉ posᵉ))) =
    invᵉ
    ( equational-reasoningᵉ
        gcd-ℤᵉ xᵉ yᵉ
        ＝ᵉ int-ℕᵉ (abs-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)))
          byᵉ apᵉ int-ℕᵉ (bezouts-lemma-refactor-hypothesesᵉ xᵉ yᵉ Hᵉ Kᵉ)
        ＝ᵉ (sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)
          byᵉ int-abs-is-nonnegative-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)) posᵉ
        ＝ᵉ (sᵉ *ℤᵉ xᵉ) +ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ yᵉ)
          byᵉ apᵉ ((sᵉ *ℤᵉ xᵉ) +ℤᵉ_) (invᵉ (left-negative-law-mul-ℤᵉ tᵉ yᵉ)))

  pr1ᵉ (sx-ty-nonneg-case-splitᵉ (inrᵉ negᵉ)) = neg-ℤᵉ sᵉ
  pr1ᵉ (pr2ᵉ (sx-ty-nonneg-case-splitᵉ (inrᵉ negᵉ))) = tᵉ
  pr2ᵉ (pr2ᵉ (sx-ty-nonneg-case-splitᵉ (inrᵉ negᵉ))) =
    invᵉ
      ( equational-reasoningᵉ
          gcd-ℤᵉ xᵉ yᵉ
          ＝ᵉ int-ℕᵉ (abs-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)))
            byᵉ apᵉ int-ℕᵉ (bezouts-lemma-refactor-hypothesesᵉ xᵉ yᵉ Hᵉ Kᵉ)
          ＝ᵉ int-ℕᵉ (abs-ℤᵉ (neg-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ))))
            byᵉ apᵉ (int-ℕᵉ) (invᵉ (abs-neg-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ))))
          ＝ᵉ neg-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ))
            byᵉ
              int-abs-is-nonnegative-ℤᵉ
                ( neg-ℤᵉ ((sᵉ *ℤᵉ xᵉ) -ℤᵉ (tᵉ *ℤᵉ yᵉ)))
                ( negᵉ)
          ＝ᵉ (neg-ℤᵉ (sᵉ *ℤᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (tᵉ *ℤᵉ yᵉ)))
            byᵉ distributive-neg-add-ℤᵉ (sᵉ *ℤᵉ xᵉ) (neg-ℤᵉ (tᵉ *ℤᵉ yᵉ))
          ＝ᵉ ((neg-ℤᵉ sᵉ) *ℤᵉ xᵉ) +ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (tᵉ *ℤᵉ yᵉ)))
            byᵉ apᵉ (_+ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (tᵉ *ℤᵉ yᵉ))))
              (invᵉ (left-negative-law-mul-ℤᵉ sᵉ xᵉ))
          ＝ᵉ ((neg-ℤᵉ sᵉ) *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ)
            byᵉ apᵉ (((neg-ℤᵉ sᵉ) *ℤᵉ xᵉ) +ℤᵉ_) (neg-neg-ℤᵉ (tᵉ *ℤᵉ yᵉ)))

bezouts-lemma-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → Σᵉ ℤᵉ (λ sᵉ → Σᵉ ℤᵉ (λ tᵉ → (sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ))
bezouts-lemma-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = pairᵉ (neg-ℤᵉ sᵉ) (pairᵉ (neg-ℤᵉ tᵉ) eqnᵉ)
  where
  pos-bezoutᵉ :
    Σᵉ ( ℤᵉ)
      ( λ sᵉ →
        Σᵉ ( ℤᵉ)
          ( λ tᵉ →
            ( (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))) ＝ᵉ
            ( gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)))))
  pos-bezoutᵉ = bezouts-lemma-pos-intsᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) starᵉ starᵉ
  sᵉ : ℤᵉ
  sᵉ = pr1ᵉ (pos-bezoutᵉ)
  tᵉ : ℤᵉ
  tᵉ = pr1ᵉ (pr2ᵉ (pos-bezoutᵉ))
  eqnᵉ :
    ((neg-ℤᵉ sᵉ) *ℤᵉ (inlᵉ xᵉ)) +ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ (inlᵉ yᵉ)) ＝ᵉ
    gcd-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ)
  eqnᵉ =
    equational-reasoningᵉ
      ( (neg-ℤᵉ sᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)))) +ℤᵉ
      ( (neg-ℤᵉ tᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ yᵉ))))
      ＝ᵉ (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ yᵉ))))
        byᵉ
          ( apᵉ
            ( _+ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ yᵉ)))))
            ( double-negative-law-mul-ℤᵉ sᵉ (inrᵉ (inrᵉ xᵉ))))
      ＝ᵉ (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))
        byᵉ
          ( apᵉ
            ( (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ_)
            ( double-negative-law-mul-ℤᵉ tᵉ (inrᵉ (inrᵉ yᵉ))))
      ＝ᵉ gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))
        byᵉ pr2ᵉ (pr2ᵉ (pos-bezoutᵉ))
      ＝ᵉ gcd-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))
        byᵉ apᵉ (λ Mᵉ → (int-ℕᵉ (gcd-ℕᵉ Mᵉ (succ-ℕᵉ yᵉ)))) (abs-neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
      ＝ᵉ gcd-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ)
        byᵉ apᵉ (λ Mᵉ → (int-ℕᵉ (gcd-ℕᵉ (succ-ℕᵉ xᵉ) Mᵉ))) (abs-neg-ℤᵉ (inrᵉ (inrᵉ yᵉ)))
bezouts-lemma-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inlᵉ starᵉ)) = pairᵉ neg-one-ℤᵉ (pairᵉ one-ℤᵉ eqnᵉ)
  where
  eqnᵉ :
    (neg-one-ℤᵉ *ℤᵉ (inlᵉ xᵉ)) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) ＝ᵉ
    gcd-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inlᵉ starᵉ))
  eqnᵉ =
    equational-reasoningᵉ
      (neg-one-ℤᵉ *ℤᵉ (inlᵉ xᵉ)) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
      ＝ᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
        byᵉ
          apᵉ
            ( _+ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))))
            ( left-neg-unit-law-mul-ℤᵉ (inlᵉ xᵉ))
      ＝ᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ zero-ℤᵉ
        byᵉ apᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ_) (right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ int-ℕᵉ (abs-ℤᵉ (inlᵉ xᵉ))
        byᵉ right-unit-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ))
      ＝ᵉ gcd-ℤᵉ (inlᵉ xᵉ) zero-ℤᵉ
        byᵉ invᵉ (is-id-is-gcd-zero-ℤ'ᵉ {inlᵉ xᵉ} {gcd-ℤᵉ (inlᵉ xᵉ) zero-ℤᵉ} reflᵉ)
bezouts-lemma-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ)) = pairᵉ (neg-ℤᵉ sᵉ) (pairᵉ tᵉ eqnᵉ)
  where
  pos-bezoutᵉ :
    Σᵉ ( ℤᵉ)
      ( λ sᵉ →
        Σᵉ ( ℤᵉ)
          ( λ tᵉ →
            (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ))) ＝ᵉ
            gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))))
  pos-bezoutᵉ = bezouts-lemma-pos-intsᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) starᵉ starᵉ
  sᵉ : ℤᵉ
  sᵉ = pr1ᵉ (pos-bezoutᵉ)
  tᵉ : ℤᵉ
  tᵉ = pr1ᵉ (pr2ᵉ (pos-bezoutᵉ))
  eqnᵉ :
    ((neg-ℤᵉ sᵉ) *ℤᵉ (inlᵉ xᵉ)) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ))) ＝ᵉ
    gcd-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))
  eqnᵉ =
    equational-reasoningᵉ
      ((neg-ℤᵉ sᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))
      ＝ᵉ (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))
        byᵉ apᵉ (_+ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ))))
          (double-negative-law-mul-ℤᵉ sᵉ (inrᵉ (inrᵉ xᵉ)))
      ＝ᵉ gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))
        byᵉ pr2ᵉ (pr2ᵉ (pos-bezoutᵉ))
      ＝ᵉ gcd-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))
        byᵉ apᵉ (λ Mᵉ → (int-ℕᵉ (gcd-ℕᵉ Mᵉ (succ-ℕᵉ yᵉ)))) (abs-neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
bezouts-lemma-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inlᵉ yᵉ) = pairᵉ one-ℤᵉ (pairᵉ neg-one-ℤᵉ eqnᵉ)
  where
  eqnᵉ :
    (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (neg-one-ℤᵉ *ℤᵉ (inlᵉ yᵉ)) ＝ᵉ
    gcd-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inlᵉ yᵉ)
  eqnᵉ =
    equational-reasoningᵉ
      (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (neg-one-ℤᵉ *ℤᵉ (inlᵉ yᵉ))
      ＝ᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (inrᵉ (inrᵉ yᵉ))
        byᵉ
          apᵉ
            ( (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ_)
            ( left-neg-unit-law-mul-ℤᵉ (inlᵉ yᵉ))
      ＝ᵉ zero-ℤᵉ +ℤᵉ (inrᵉ (inrᵉ yᵉ))
        byᵉ apᵉ (_+ℤᵉ (inrᵉ (inrᵉ yᵉ))) (right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ int-ℕᵉ (abs-ℤᵉ (inlᵉ yᵉ))
        byᵉ left-unit-law-add-ℤᵉ (inrᵉ (inrᵉ yᵉ))
      ＝ᵉ gcd-ℤᵉ zero-ℤᵉ (inlᵉ yᵉ)
        byᵉ invᵉ (is-id-is-gcd-zero-ℤᵉ {inlᵉ yᵉ} {gcd-ℤᵉ zero-ℤᵉ (inlᵉ yᵉ)} reflᵉ)
bezouts-lemma-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inlᵉ starᵉ)) = pairᵉ one-ℤᵉ (pairᵉ one-ℤᵉ eqnᵉ)
  where
  eqnᵉ :
    (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) ＝ᵉ
    gcd-ℤᵉ zero-ℤᵉ zero-ℤᵉ
  eqnᵉ =
    equational-reasoningᵉ
      (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
      ＝ᵉ zero-ℤᵉ +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
        byᵉ
          apᵉ
            ( _+ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))))
            ( right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ zero-ℤᵉ +ℤᵉ zero-ℤᵉ
        byᵉ apᵉ (zero-ℤᵉ +ℤᵉ_) (right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ gcd-ℤᵉ zero-ℤᵉ zero-ℤᵉ
        byᵉ invᵉ (is-zero-gcd-ℤᵉ zero-ℤᵉ zero-ℤᵉ reflᵉ reflᵉ)
bezouts-lemma-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inrᵉ yᵉ)) = pairᵉ one-ℤᵉ (pairᵉ one-ℤᵉ eqnᵉ)
  where
  eqnᵉ :
    (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ))) ＝ᵉ
    gcd-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inrᵉ yᵉ))
  eqnᵉ =
    equational-reasoningᵉ
      (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))
      ＝ᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ (inrᵉ (inrᵉ yᵉ))
        byᵉ apᵉ
          ( (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) +ℤᵉ_)
          ( invᵉ (left-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ yᵉ))))
      ＝ᵉ zero-ℤᵉ +ℤᵉ (inrᵉ (inrᵉ yᵉ))
        byᵉ apᵉ (_+ℤᵉ (inrᵉ (inrᵉ yᵉ))) (right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ int-ℕᵉ (abs-ℤᵉ (inrᵉ (inrᵉ yᵉ)))
        byᵉ left-unit-law-add-ℤᵉ (inrᵉ (inrᵉ yᵉ))
      ＝ᵉ gcd-ℤᵉ zero-ℤᵉ (inrᵉ (inrᵉ yᵉ))
        byᵉ
          invᵉ
            ( is-id-is-gcd-zero-ℤᵉ
              { inrᵉ (inrᵉ yᵉ)}
              { gcd-ℤᵉ zero-ℤᵉ (inrᵉ (inrᵉ yᵉ))}
              ( reflᵉ))
bezouts-lemma-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ) = pairᵉ sᵉ (pairᵉ (neg-ℤᵉ tᵉ) eqnᵉ)
  where
  pos-bezoutᵉ :
    Σᵉ ( ℤᵉ)
      ( λ sᵉ →
        Σᵉ ( ℤᵉ)
          ( λ tᵉ →
            (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ))) ＝ᵉ
            gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))))
  pos-bezoutᵉ = bezouts-lemma-pos-intsᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) starᵉ starᵉ
  sᵉ : ℤᵉ
  sᵉ = pr1ᵉ (pos-bezoutᵉ)
  tᵉ : ℤᵉ
  tᵉ = pr1ᵉ (pr2ᵉ (pos-bezoutᵉ))
  eqnᵉ :
    (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ (inlᵉ yᵉ)) ＝ᵉ
    gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ)
  eqnᵉ =
    equational-reasoningᵉ
      (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ ((neg-ℤᵉ tᵉ) *ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ yᵉ))))
      ＝ᵉ (sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (tᵉ *ℤᵉ (inrᵉ (inrᵉ yᵉ)))
        byᵉ apᵉ ((sᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ_)
          (double-negative-law-mul-ℤᵉ tᵉ (inrᵉ (inrᵉ yᵉ)))
      ＝ᵉ gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))
        byᵉ pr2ᵉ (pr2ᵉ (pos-bezoutᵉ))
      ＝ᵉ gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ)
        byᵉ apᵉ (λ Mᵉ → (int-ℕᵉ (gcd-ℕᵉ (succ-ℕᵉ xᵉ) Mᵉ))) (abs-neg-ℤᵉ (inrᵉ (inrᵉ yᵉ)))
bezouts-lemma-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ)) = pairᵉ one-ℤᵉ (pairᵉ one-ℤᵉ eqnᵉ)
  where
  eqnᵉ :
    (one-ℤᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))) ＝ᵉ
    gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ))
  eqnᵉ =
    equational-reasoningᵉ
      (one-ℤᵉ *ℤᵉ (inrᵉ (inrᵉ xᵉ))) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
      ＝ᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ)))
        byᵉ
          apᵉ
            ( _+ℤᵉ (one-ℤᵉ *ℤᵉ (inrᵉ (inlᵉ starᵉ))))
            ( left-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
      ＝ᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ zero-ℤᵉ
        byᵉ apᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ_) (right-zero-law-mul-ℤᵉ one-ℤᵉ)
      ＝ᵉ int-ℕᵉ (abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
        byᵉ right-unit-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ))
      ＝ᵉ gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) zero-ℤᵉ
        byᵉ
          invᵉ
            ( is-id-is-gcd-zero-ℤ'ᵉ
              { inrᵉ (inrᵉ xᵉ)}
              { gcd-ℤᵉ (inrᵉ (inrᵉ xᵉ)) zero-ℤᵉ}
              ( reflᵉ))
bezouts-lemma-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) =
  bezouts-lemma-pos-intsᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) starᵉ starᵉ
```

Nowᵉ thatᵉ Bezout'sᵉ Lemmaᵉ hasᵉ beenᵉ established,ᵉ weᵉ establishᵉ aᵉ fewᵉ corollariesᵉ ofᵉ
Bezout.ᵉ

### If `x | y z` and `gcd-Z x y ＝ 1`, then `x | z`

```agda
div-right-factor-coprime-ℤᵉ :
  (xᵉ yᵉ zᵉ : ℤᵉ) → (div-ℤᵉ xᵉ (yᵉ *ℤᵉ zᵉ)) → (gcd-ℤᵉ xᵉ yᵉ ＝ᵉ one-ℤᵉ) → div-ℤᵉ xᵉ zᵉ
div-right-factor-coprime-ℤᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ = pairᵉ ((sᵉ *ℤᵉ zᵉ) +ℤᵉ (tᵉ *ℤᵉ kᵉ)) eqnᵉ
  where
  bezout-tripleᵉ :
    Σᵉ ℤᵉ (λ sᵉ → Σᵉ ℤᵉ (λ tᵉ → (sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ))
  bezout-tripleᵉ = bezouts-lemma-ℤᵉ xᵉ yᵉ
  sᵉ : ℤᵉ
  sᵉ = pr1ᵉ bezout-tripleᵉ
  tᵉ : ℤᵉ
  tᵉ = pr1ᵉ (pr2ᵉ bezout-tripleᵉ)
  bezout-eqnᵉ : (sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ
  bezout-eqnᵉ = pr2ᵉ (pr2ᵉ bezout-tripleᵉ)
  kᵉ : ℤᵉ
  kᵉ = pr1ᵉ Hᵉ
  div-yzᵉ : kᵉ *ℤᵉ xᵉ ＝ᵉ yᵉ *ℤᵉ zᵉ
  div-yzᵉ = pr2ᵉ Hᵉ
  eqnᵉ : ((sᵉ *ℤᵉ zᵉ) +ℤᵉ (tᵉ *ℤᵉ kᵉ)) *ℤᵉ xᵉ ＝ᵉ zᵉ
  eqnᵉ =
    equational-reasoningᵉ
      ((sᵉ *ℤᵉ zᵉ) +ℤᵉ (tᵉ *ℤᵉ kᵉ)) *ℤᵉ xᵉ
      ＝ᵉ ((sᵉ *ℤᵉ zᵉ) *ℤᵉ xᵉ) +ℤᵉ ((tᵉ *ℤᵉ kᵉ) *ℤᵉ xᵉ)
        byᵉ right-distributive-mul-add-ℤᵉ (sᵉ *ℤᵉ zᵉ) (tᵉ *ℤᵉ kᵉ) xᵉ
      ＝ᵉ ((sᵉ *ℤᵉ xᵉ) *ℤᵉ zᵉ) +ℤᵉ ((tᵉ *ℤᵉ kᵉ) *ℤᵉ xᵉ)
        byᵉ apᵉ (_+ℤᵉ ((tᵉ *ℤᵉ kᵉ) *ℤᵉ xᵉ))
        ( equational-reasoningᵉ
            (sᵉ *ℤᵉ zᵉ) *ℤᵉ xᵉ
            ＝ᵉ sᵉ *ℤᵉ (zᵉ *ℤᵉ xᵉ)
              byᵉ associative-mul-ℤᵉ sᵉ zᵉ xᵉ
            ＝ᵉ sᵉ *ℤᵉ (xᵉ *ℤᵉ zᵉ)
              byᵉ apᵉ (sᵉ *ℤᵉ_) (commutative-mul-ℤᵉ zᵉ xᵉ)
            ＝ᵉ (sᵉ *ℤᵉ xᵉ) *ℤᵉ zᵉ
              byᵉ invᵉ (associative-mul-ℤᵉ sᵉ xᵉ zᵉ))
      ＝ᵉ ((sᵉ *ℤᵉ xᵉ) *ℤᵉ zᵉ) +ℤᵉ ((tᵉ *ℤᵉ yᵉ) *ℤᵉ zᵉ)
        byᵉ apᵉ (((sᵉ *ℤᵉ xᵉ) *ℤᵉ zᵉ) +ℤᵉ_)
    ( equational-reasoningᵉ
        (tᵉ *ℤᵉ kᵉ) *ℤᵉ xᵉ
        ＝ᵉ tᵉ *ℤᵉ (kᵉ *ℤᵉ xᵉ)
          byᵉ associative-mul-ℤᵉ tᵉ kᵉ xᵉ
        ＝ᵉ tᵉ *ℤᵉ (yᵉ *ℤᵉ zᵉ)
          byᵉ apᵉ (tᵉ *ℤᵉ_) div-yzᵉ
        ＝ᵉ (tᵉ *ℤᵉ yᵉ) *ℤᵉ zᵉ
          byᵉ invᵉ (associative-mul-ℤᵉ tᵉ yᵉ zᵉ))
    ＝ᵉ ((sᵉ *ℤᵉ xᵉ) +ℤᵉ (tᵉ *ℤᵉ yᵉ)) *ℤᵉ zᵉ
      byᵉ invᵉ (right-distributive-mul-add-ℤᵉ (sᵉ *ℤᵉ xᵉ) (tᵉ *ℤᵉ yᵉ) zᵉ)
    ＝ᵉ one-ℤᵉ *ℤᵉ zᵉ
      byᵉ apᵉ (_*ℤᵉ zᵉ) (bezout-eqnᵉ ∙ᵉ Kᵉ)
    ＝ᵉ zᵉ
      byᵉ left-unit-law-mul-ℤᵉ zᵉ

div-right-factor-coprime-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → (div-ℕᵉ xᵉ (yᵉ *ℕᵉ zᵉ)) → (gcd-ℕᵉ xᵉ yᵉ ＝ᵉ 1ᵉ) → div-ℕᵉ xᵉ zᵉ
div-right-factor-coprime-ℕᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ =
  div-div-int-ℕᵉ
    ( div-right-factor-coprime-ℤᵉ
      ( int-ℕᵉ xᵉ)
      ( int-ℕᵉ yᵉ)
      ( int-ℕᵉ zᵉ)
        ( trᵉ (div-ℤᵉ (int-ℕᵉ xᵉ)) (invᵉ (mul-int-ℕᵉ yᵉ zᵉ)) (div-int-div-ℕᵉ Hᵉ))
      ( eq-gcd-gcd-int-ℕᵉ xᵉ yᵉ ∙ᵉ apᵉ int-ℕᵉ Kᵉ))
```