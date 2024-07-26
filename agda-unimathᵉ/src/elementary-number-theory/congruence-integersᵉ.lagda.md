# The congruence relations on the integers

```agda
module elementary-number-theory.congruence-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.distance-integersᵉ
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definitions

```agda
cong-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ → UUᵉ lzero
cong-ℤᵉ kᵉ xᵉ yᵉ = div-ℤᵉ kᵉ (xᵉ -ℤᵉ yᵉ)

is-cong-zero-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
is-cong-zero-ℤᵉ kᵉ xᵉ = cong-ℤᵉ kᵉ xᵉ zero-ℤᵉ
```

## Properties

```agda
is-cong-zero-div-ℤᵉ : (kᵉ xᵉ : ℤᵉ) → div-ℤᵉ kᵉ xᵉ → is-cong-zero-ℤᵉ kᵉ xᵉ
pr1ᵉ (is-cong-zero-div-ℤᵉ kᵉ xᵉ (pairᵉ dᵉ pᵉ)) = dᵉ
pr2ᵉ (is-cong-zero-div-ℤᵉ kᵉ xᵉ (pairᵉ dᵉ pᵉ)) = pᵉ ∙ᵉ invᵉ (right-unit-law-add-ℤᵉ xᵉ)

div-is-cong-zero-ℤᵉ : (kᵉ xᵉ : ℤᵉ) → is-cong-zero-ℤᵉ kᵉ xᵉ → div-ℤᵉ kᵉ xᵉ
pr1ᵉ (div-is-cong-zero-ℤᵉ kᵉ xᵉ (pairᵉ dᵉ pᵉ)) = dᵉ
pr2ᵉ (div-is-cong-zero-ℤᵉ kᵉ xᵉ (pairᵉ dᵉ pᵉ)) = pᵉ ∙ᵉ right-unit-law-add-ℤᵉ xᵉ

is-indiscrete-cong-ℤᵉ : (kᵉ : ℤᵉ) → is-unit-ℤᵉ kᵉ → (xᵉ yᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ
is-indiscrete-cong-ℤᵉ kᵉ Hᵉ xᵉ yᵉ = div-is-unit-ℤᵉ kᵉ (xᵉ -ℤᵉ yᵉ) Hᵉ

is-discrete-cong-ℤᵉ : (kᵉ : ℤᵉ) → is-zero-ℤᵉ kᵉ → (xᵉ yᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
is-discrete-cong-ℤᵉ .zero-ℤᵉ reflᵉ xᵉ yᵉ Kᵉ =
  eq-diff-ℤᵉ (is-zero-div-zero-ℤᵉ (xᵉ -ℤᵉ yᵉ) Kᵉ)

is-unit-cong-succ-ℤᵉ : (kᵉ xᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ (succ-ℤᵉ xᵉ) → is-unit-ℤᵉ kᵉ
pr1ᵉ (is-unit-cong-succ-ℤᵉ kᵉ xᵉ (pairᵉ yᵉ pᵉ)) = neg-ℤᵉ yᵉ
pr2ᵉ (is-unit-cong-succ-ℤᵉ kᵉ xᵉ (pairᵉ yᵉ pᵉ)) =
  ( left-negative-law-mul-ℤᵉ yᵉ kᵉ) ∙ᵉ
  ( is-injective-neg-ℤᵉ
    ( ( neg-neg-ℤᵉ (yᵉ *ℤᵉ kᵉ)) ∙ᵉ
      ( ( pᵉ) ∙ᵉ
        ( ( apᵉ (xᵉ +ℤᵉ_) (neg-succ-ℤᵉ xᵉ)) ∙ᵉ
          ( ( right-predecessor-law-add-ℤᵉ xᵉ (neg-ℤᵉ xᵉ)) ∙ᵉ
            ( apᵉ pred-ℤᵉ (right-inverse-law-add-ℤᵉ xᵉ)))))))

is-unit-cong-pred-ℤᵉ : (kᵉ xᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ (pred-ℤᵉ xᵉ) → is-unit-ℤᵉ kᵉ
pr1ᵉ (is-unit-cong-pred-ℤᵉ kᵉ xᵉ (pairᵉ yᵉ pᵉ)) = yᵉ
pr2ᵉ (is-unit-cong-pred-ℤᵉ kᵉ xᵉ (pairᵉ yᵉ pᵉ)) =
  ( pᵉ) ∙ᵉ
  ( ( apᵉ (xᵉ +ℤᵉ_) (neg-pred-ℤᵉ xᵉ)) ∙ᵉ
    ( ( right-successor-law-add-ℤᵉ xᵉ (neg-ℤᵉ xᵉ)) ∙ᵉ
      ( apᵉ succ-ℤᵉ (right-inverse-law-add-ℤᵉ xᵉ))))

refl-cong-ℤᵉ : (kᵉ : ℤᵉ) → is-reflexiveᵉ (cong-ℤᵉ kᵉ)
pr1ᵉ (refl-cong-ℤᵉ kᵉ xᵉ) = zero-ℤᵉ
pr2ᵉ (refl-cong-ℤᵉ kᵉ xᵉ) = left-zero-law-mul-ℤᵉ kᵉ ∙ᵉ invᵉ (is-zero-diff-ℤ'ᵉ xᵉ)

symmetric-cong-ℤᵉ : (kᵉ : ℤᵉ) → is-symmetricᵉ (cong-ℤᵉ kᵉ)
pr1ᵉ (symmetric-cong-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = neg-ℤᵉ dᵉ
pr2ᵉ (symmetric-cong-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  ( left-negative-law-mul-ℤᵉ dᵉ kᵉ) ∙ᵉ
  ( ( apᵉ neg-ℤᵉ pᵉ) ∙ᵉ
    ( distributive-neg-diff-ℤᵉ xᵉ yᵉ))

transitive-cong-ℤᵉ : (kᵉ : ℤᵉ) → is-transitiveᵉ (cong-ℤᵉ kᵉ)
pr1ᵉ (transitive-cong-ℤᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ eᵉ qᵉ) (pairᵉ dᵉ pᵉ)) = dᵉ +ℤᵉ eᵉ
pr2ᵉ (transitive-cong-ℤᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ eᵉ qᵉ) (pairᵉ dᵉ pᵉ)) =
  ( right-distributive-mul-add-ℤᵉ dᵉ eᵉ kᵉ) ∙ᵉ
  ( ( ap-add-ℤᵉ pᵉ qᵉ) ∙ᵉ
    ( triangle-diff-ℤᵉ xᵉ yᵉ zᵉ))

concatenate-eq-cong-ℤᵉ :
  (kᵉ xᵉ x'ᵉ yᵉ : ℤᵉ) → xᵉ ＝ᵉ x'ᵉ → cong-ℤᵉ kᵉ x'ᵉ yᵉ → cong-ℤᵉ kᵉ xᵉ yᵉ
concatenate-eq-cong-ℤᵉ kᵉ xᵉ .xᵉ yᵉ reflᵉ = idᵉ

concatenate-cong-eq-ℤᵉ :
  (kᵉ xᵉ yᵉ y'ᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ → yᵉ ＝ᵉ y'ᵉ → cong-ℤᵉ kᵉ xᵉ y'ᵉ
concatenate-cong-eq-ℤᵉ kᵉ xᵉ yᵉ .yᵉ Hᵉ reflᵉ = Hᵉ

concatenate-eq-cong-eq-ℤᵉ :
  (kᵉ xᵉ x'ᵉ y'ᵉ yᵉ : ℤᵉ) → xᵉ ＝ᵉ x'ᵉ → cong-ℤᵉ kᵉ x'ᵉ y'ᵉ → y'ᵉ ＝ᵉ yᵉ → cong-ℤᵉ kᵉ xᵉ yᵉ
concatenate-eq-cong-eq-ℤᵉ kᵉ xᵉ .xᵉ yᵉ .yᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

concatenate-cong-eq-cong-ℤᵉ :
  (kᵉ xᵉ yᵉ y'ᵉ zᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ → yᵉ ＝ᵉ y'ᵉ → cong-ℤᵉ kᵉ y'ᵉ zᵉ → cong-ℤᵉ kᵉ xᵉ zᵉ
concatenate-cong-eq-cong-ℤᵉ kᵉ xᵉ yᵉ .yᵉ zᵉ Hᵉ reflᵉ Kᵉ =
  transitive-cong-ℤᵉ kᵉ xᵉ yᵉ zᵉ Kᵉ Hᵉ

concatenate-cong-cong-cong-ℤᵉ :
  (kᵉ xᵉ yᵉ zᵉ wᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ → cong-ℤᵉ kᵉ yᵉ zᵉ → cong-ℤᵉ kᵉ zᵉ wᵉ → cong-ℤᵉ kᵉ xᵉ wᵉ
concatenate-cong-cong-cong-ℤᵉ kᵉ xᵉ yᵉ zᵉ wᵉ Hᵉ Kᵉ Lᵉ =
  transitive-cong-ℤᵉ kᵉ xᵉ yᵉ wᵉ (transitive-cong-ℤᵉ kᵉ yᵉ zᵉ wᵉ Lᵉ Kᵉ) Hᵉ

cong-cong-neg-ℤᵉ : (kᵉ xᵉ yᵉ : ℤᵉ) → cong-ℤᵉ kᵉ (neg-ℤᵉ xᵉ) (neg-ℤᵉ yᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ
pr1ᵉ (cong-cong-neg-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = neg-ℤᵉ dᵉ
pr2ᵉ (cong-cong-neg-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  ( left-negative-law-mul-ℤᵉ dᵉ kᵉ) ∙ᵉ
  ( ( apᵉ neg-ℤᵉ pᵉ) ∙ᵉ
    ( ( distributive-neg-add-ℤᵉ (neg-ℤᵉ xᵉ) (neg-ℤᵉ (neg-ℤᵉ yᵉ))) ∙ᵉ
      ( ap-add-ℤᵉ (neg-neg-ℤᵉ xᵉ) (neg-neg-ℤᵉ (neg-ℤᵉ yᵉ)))))

cong-neg-cong-ℤᵉ : (kᵉ xᵉ yᵉ : ℤᵉ) → cong-ℤᵉ kᵉ xᵉ yᵉ → cong-ℤᵉ kᵉ (neg-ℤᵉ xᵉ) (neg-ℤᵉ yᵉ)
pr1ᵉ (cong-neg-cong-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) = neg-ℤᵉ dᵉ
pr2ᵉ (cong-neg-cong-ℤᵉ kᵉ xᵉ yᵉ (pairᵉ dᵉ pᵉ)) =
  ( left-negative-law-mul-ℤᵉ dᵉ kᵉ) ∙ᵉ
  ( ( apᵉ neg-ℤᵉ pᵉ) ∙ᵉ
    ( distributive-neg-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)))
```

```agda
cong-int-cong-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ → cong-ℤᵉ (int-ℕᵉ kᵉ) (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)
cong-int-cong-ℕᵉ kᵉ xᵉ yᵉ Hᵉ =
  div-sim-unit-ℤᵉ
    ( refl-sim-unit-ℤᵉ (int-ℕᵉ kᵉ))
    ( sim-unit-abs-ℤᵉ ((int-ℕᵉ xᵉ) -ℤᵉ (int-ℕᵉ yᵉ)))
    ( trᵉ
      ( div-ℤᵉ (int-ℕᵉ kᵉ))
      ( invᵉ (apᵉ int-ℕᵉ (dist-int-ℕᵉ xᵉ yᵉ)))
      ( div-int-div-ℕᵉ Hᵉ))

cong-cong-int-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → cong-ℤᵉ (int-ℕᵉ kᵉ) (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) → cong-ℕᵉ kᵉ xᵉ yᵉ
cong-cong-int-ℕᵉ kᵉ xᵉ yᵉ Hᵉ =
  div-div-int-ℕᵉ
    ( trᵉ
      ( div-ℤᵉ (int-ℕᵉ kᵉ))
      ( apᵉ int-ℕᵉ (dist-int-ℕᵉ xᵉ yᵉ))
      ( div-sim-unit-ℤᵉ
        ( refl-sim-unit-ℤᵉ (int-ℕᵉ kᵉ))
        ( symmetric-sim-unit-ℤᵉ
          ( int-abs-ℤᵉ (int-ℕᵉ xᵉ -ℤᵉ int-ℕᵉ yᵉ))
          ( int-ℕᵉ xᵉ -ℤᵉ int-ℕᵉ yᵉ)
          ( sim-unit-abs-ℤᵉ ((int-ℕᵉ xᵉ) -ℤᵉ (int-ℕᵉ yᵉ))))
        ( Hᵉ)))
```