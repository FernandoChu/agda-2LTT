# Bezout's lemma on the natural numbers

```agda
module elementary-number-theory.bezouts-lemma-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-integersᵉ
open import elementary-number-theory.distance-integersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-modular-arithmeticᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.euclidean-division-natural-numbersᵉ
open import elementary-number-theory.greatest-common-divisor-natural-numbersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Bezout'sᵉ lemmaᵉ showsᵉ thatᵉ forᵉ anyᵉ twoᵉ naturalᵉ numbersᵉ `x`ᵉ andᵉ `y`ᵉ thereᵉ existᵉ
`k`ᵉ andᵉ `l`ᵉ suchᵉ thatᵉ `dist-ℕᵉ (kx,lyᵉ) = gcd(x,y)`.ᵉ Toᵉ proveᵉ this,ᵉ noteᵉ thatᵉ theᵉ
predicateᵉ `Pᵉ : ℕᵉ → UUᵉ lzero`ᵉ givenᵉ byᵉ

```text
  Pᵉ zᵉ :=ᵉ Σᵉ (kᵉ : ℕ),ᵉ Σᵉ (lᵉ : ℕ),ᵉ dist-ℕᵉ (kx,ᵉ lyᵉ) = zᵉ
```

isᵉ decidable,ᵉ becauseᵉ `Pᵉ zᵉ ⇔ᵉ [y]_xᵉ | [z]_x`ᵉ in `ℤ/x`.ᵉ Theᵉ leastᵉ positiveᵉ `z`ᵉ
suchᵉ thatᵉ `Pᵉ z`ᵉ holdsᵉ isᵉ `gcdᵉ xᵉ y`.ᵉ

## Definitions

```agda
is-distance-between-multiples-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ =
  Σᵉ ℕᵉ (λ kᵉ → Σᵉ ℕᵉ (λ lᵉ → dist-ℕᵉ (kᵉ *ℕᵉ xᵉ) (lᵉ *ℕᵉ yᵉ) ＝ᵉ zᵉ))

is-distance-between-multiples-fst-coeff-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ → ℕᵉ
is-distance-between-multiples-fst-coeff-ℕᵉ distᵉ = pr1ᵉ distᵉ

is-distance-between-multiples-snd-coeff-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ → ℕᵉ
is-distance-between-multiples-snd-coeff-ℕᵉ distᵉ = pr1ᵉ (pr2ᵉ distᵉ)

is-distance-between-multiples-eqn-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} (dᵉ : is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ) →
  dist-ℕᵉ
    ( (is-distance-between-multiples-fst-coeff-ℕᵉ dᵉ) *ℕᵉ xᵉ)
    ( (is-distance-between-multiples-snd-coeff-ℕᵉ dᵉ) *ℕᵉ yᵉ) ＝ᵉ zᵉ
is-distance-between-multiples-eqn-ℕᵉ distᵉ = pr2ᵉ (pr2ᵉ distᵉ)

is-distance-between-multiples-sym-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ →
  is-distance-between-multiples-ℕᵉ yᵉ xᵉ zᵉ
is-distance-between-multiples-sym-ℕᵉ xᵉ yᵉ zᵉ (pairᵉ kᵉ (pairᵉ lᵉ eqnᵉ)) =
  pairᵉ lᵉ (pairᵉ kᵉ (symmetric-dist-ℕᵉ (lᵉ *ℕᵉ yᵉ) (kᵉ *ℕᵉ xᵉ) ∙ᵉ eqnᵉ))
```

## Lemmas

### If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then `[y] | [z]` in `ℤ-Mod x`

Ifᵉ `zᵉ = dist-ℕᵉ (kx,ᵉ ly)`ᵉ forᵉ someᵉ `k`ᵉ andᵉ `l`,ᵉ thenᵉ itᵉ followsᵉ thatᵉ
`lyᵉ ≡ᵉ ±zᵉ modᵉ x`.ᵉ Itᵉ followsᵉ thatᵉ `±lyᵉ ≡ᵉ zᵉ modᵉ x`,ᵉ andᵉ thereforeᵉ thatᵉ `[yᵉ] | [z]`ᵉ
in `ℤ-Modᵉ x`ᵉ

```agda
int-is-distance-between-multiples-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) (dᵉ : is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ) →
  ( Hᵉ :
    leq-ℕᵉ
      ( (is-distance-between-multiples-fst-coeff-ℕᵉ dᵉ) *ℕᵉ xᵉ)
      ( (is-distance-between-multiples-snd-coeff-ℕᵉ dᵉ) *ℕᵉ yᵉ)) →
  ( int-ℕᵉ zᵉ) +ℤᵉ
  ( (int-ℕᵉ (is-distance-between-multiples-fst-coeff-ℕᵉ dᵉ)) *ℤᵉ (int-ℕᵉ xᵉ)) ＝ᵉ
  ( int-ℕᵉ (is-distance-between-multiples-snd-coeff-ℕᵉ dᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)
int-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ (kᵉ ,ᵉ lᵉ ,ᵉ pᵉ) Hᵉ =
  equational-reasoningᵉ
    (int-ℕᵉ zᵉ) +ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ))
    ＝ᵉ (int-ℕᵉ zᵉ) +ℤᵉ (int-ℕᵉ (kᵉ *ℕᵉ xᵉ))
      byᵉ apᵉ ((int-ℕᵉ zᵉ) +ℤᵉ_) (mul-int-ℕᵉ kᵉ xᵉ)
    ＝ᵉ int-ℕᵉ (zᵉ +ℕᵉ (kᵉ *ℕᵉ xᵉ))
      byᵉ add-int-ℕᵉ zᵉ (kᵉ *ℕᵉ xᵉ)
    ＝ᵉ int-ℕᵉ (lᵉ *ℕᵉ yᵉ)
      byᵉ apᵉ (int-ℕᵉ) (rewrite-left-dist-add-ℕᵉ zᵉ (kᵉ *ℕᵉ xᵉ) (lᵉ *ℕᵉ yᵉ) Hᵉ (invᵉ pᵉ))
    ＝ᵉ (int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ)
      byᵉ invᵉ (mul-int-ℕᵉ lᵉ yᵉ)

div-mod-is-distance-between-multiples-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) →
  is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ → div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ)
div-mod-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ (kᵉ ,ᵉ lᵉ ,ᵉ pᵉ) =
  kxly-case-splitᵉ (linear-leq-ℕᵉ (kᵉ *ℕᵉ xᵉ) (lᵉ *ℕᵉ yᵉ))
  where
  kxly-case-splitᵉ :
    leq-ℕᵉ (kᵉ *ℕᵉ xᵉ) (lᵉ *ℕᵉ yᵉ) +ᵉ leq-ℕᵉ (lᵉ *ℕᵉ yᵉ) (kᵉ *ℕᵉ xᵉ) →
    div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ)
  kxly-case-splitᵉ (inlᵉ kxlyᵉ) =
    ( mod-ℕᵉ xᵉ lᵉ ,ᵉ
      ( equational-reasoningᵉ
        mul-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ lᵉ) (mod-ℕᵉ xᵉ yᵉ)
        ＝ᵉ mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ lᵉ)) (mod-ℕᵉ xᵉ yᵉ)
          byᵉ invᵉ (apᵉ (λ pᵉ → mul-ℤ-Modᵉ xᵉ pᵉ (mod-ℕᵉ xᵉ yᵉ)) (mod-int-ℕᵉ xᵉ lᵉ))
        ＝ᵉ mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ lᵉ)) (mod-ℤᵉ xᵉ (int-ℕᵉ yᵉ))
          byᵉ invᵉ (apᵉ (λ pᵉ → mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ lᵉ)) pᵉ) (mod-int-ℕᵉ xᵉ yᵉ))
        ＝ᵉ mod-ℤᵉ xᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ invᵉ (preserves-mul-mod-ℤᵉ xᵉ (int-ℕᵉ lᵉ) (int-ℕᵉ yᵉ))
        ＝ᵉ mod-ℤᵉ xᵉ ((int-ℕᵉ zᵉ) +ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
          byᵉ
          invᵉ
            ( apᵉ
              ( mod-ℤᵉ xᵉ)
              ( int-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ (kᵉ ,ᵉ lᵉ ,ᵉ pᵉ) kxlyᵉ))
        ＝ᵉ add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)) (mod-ℤᵉ xᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
          byᵉ preserves-add-mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ) ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ))
            ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) (mod-ℤᵉ xᵉ (int-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)))
            ( preserves-mul-mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ) (int-ℕᵉ xᵉ))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ))
            ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) (mod-ℤᵉ xᵉ zero-ℤᵉ))
          byᵉ
          apᵉ
            ( λ pᵉ →
              add-ℤ-Modᵉ xᵉ
                ( mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ))
                ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) pᵉ))
            ( mod-int-ℕᵉ xᵉ xᵉ ∙ᵉ (mod-refl-ℕᵉ xᵉ ∙ᵉ invᵉ (mod-zero-ℤᵉ xᵉ)))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ))
            ( mod-ℤᵉ xᵉ ((int-ℕᵉ kᵉ) *ℤᵉ zero-ℤᵉ))
          byᵉ
          apᵉ
            ( add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)))
            ( invᵉ (preserves-mul-mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ) zero-ℤᵉ))
        ＝ᵉ add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)) (mod-ℤᵉ xᵉ zero-ℤᵉ)
          byᵉ
          apᵉ
            ( λ pᵉ → add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)) (mod-ℤᵉ xᵉ pᵉ))
            ( right-zero-law-mul-ℤᵉ (int-ℕᵉ kᵉ))
        ＝ᵉ mod-ℤᵉ xᵉ ((int-ℕᵉ zᵉ) +ℤᵉ zero-ℤᵉ)
          byᵉ invᵉ (preserves-add-mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ) zero-ℤᵉ)
        ＝ᵉ mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)
          byᵉ apᵉ (mod-ℤᵉ xᵉ) (right-unit-law-add-ℤᵉ (int-ℕᵉ zᵉ))
        ＝ᵉ mod-ℕᵉ xᵉ zᵉ byᵉ mod-int-ℕᵉ xᵉ zᵉ))
  kxly-case-splitᵉ (inrᵉ lykxᵉ) =
    ( mod-ℤᵉ xᵉ (neg-ℤᵉ (int-ℕᵉ lᵉ)) ,ᵉ
      ( equational-reasoningᵉ
        mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (neg-ℤᵉ (int-ℕᵉ lᵉ))) (mod-ℕᵉ xᵉ yᵉ)
        ＝ᵉ mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (neg-ℤᵉ (int-ℕᵉ lᵉ))) (mod-ℤᵉ xᵉ (int-ℕᵉ yᵉ))
          byᵉ
          invᵉ
            ( apᵉ
              ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (neg-ℤᵉ (int-ℕᵉ lᵉ))))
              ( mod-int-ℕᵉ xᵉ yᵉ))
        ＝ᵉ mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ invᵉ (preserves-mul-mod-ℤᵉ xᵉ (neg-ℤᵉ (int-ℕᵉ lᵉ)) (int-ℕᵉ yᵉ))
        ＝ᵉ mod-ℤᵉ xᵉ (((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ zero-ℤᵉ)
          byᵉ
          apᵉ
            ( mod-ℤᵉ xᵉ)
            ( invᵉ (right-unit-law-add-ℤᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ( mod-ℤᵉ xᵉ zero-ℤᵉ)
          byᵉ preserves-add-mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) (zero-ℤᵉ)
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ( mod-ℤᵉ xᵉ ((int-ℕᵉ kᵉ) *ℤᵉ zero-ℤᵉ))
          byᵉ
          apᵉ
            ( λ pᵉ →
              add-ℤ-Modᵉ xᵉ
                ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
                ( mod-ℤᵉ xᵉ pᵉ))
            ( invᵉ (right-zero-law-mul-ℤᵉ (int-ℕᵉ kᵉ)))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) (mod-ℤᵉ xᵉ zero-ℤᵉ))
          byᵉ
          apᵉ
            ( add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
            ( preserves-mul-mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ) zero-ℤᵉ)
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) (mod-ℤᵉ xᵉ (int-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( λ pᵉ →
              add-ℤ-Modᵉ xᵉ
                ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
                ( mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ)) pᵉ))
            ( mod-zero-ℤᵉ xᵉ ∙ᵉ (invᵉ (mod-refl-ℕᵉ xᵉ) ∙ᵉ invᵉ (mod-int-ℕᵉ xᵉ xᵉ)))
        ＝ᵉ add-ℤ-Modᵉ xᵉ
            ( mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ( mod-ℤᵉ xᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( add-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
            ( invᵉ (preserves-mul-mod-ℤᵉ xᵉ (int-ℕᵉ kᵉ) (int-ℕᵉ xᵉ)))
        ＝ᵉ mod-ℤᵉ xᵉ
            ( ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
          byᵉ
          invᵉ
            ( preserves-add-mod-ℤᵉ xᵉ
              ( (neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
              ( (int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
        ＝ᵉ mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ)
          byᵉ
          apᵉ
            ( mod-ℤᵉ xᵉ)
            ( equational-reasoningᵉ
              ((neg-ℤᵉ (int-ℕᵉ lᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ))
              ＝ᵉ (neg-ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ))
                byᵉ
                apᵉ
                  ( _+ℤᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)))
                  ( left-negative-law-mul-ℤᵉ (int-ℕᵉ lᵉ) (int-ℕᵉ yᵉ))
              ＝ᵉ ((int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
                byᵉ
                commutative-add-ℤᵉ
                  ( neg-ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
                  ( (int-ℕᵉ kᵉ) *ℤᵉ (int-ℕᵉ xᵉ))
              ＝ᵉ add-ℤᵉ
                  ( (int-ℕᵉ zᵉ) +ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
                  ( neg-ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
                byᵉ
                apᵉ
                  ( _+ℤᵉ (neg-ℤᵉ ((int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ))))
                  ( invᵉ
                    ( int-is-distance-between-multiples-ℕᵉ yᵉ xᵉ zᵉ
                      ( is-distance-between-multiples-sym-ℕᵉ xᵉ yᵉ zᵉ (kᵉ ,ᵉ lᵉ ,ᵉ pᵉ))
                    ( lykxᵉ)))
              ＝ᵉ int-ℕᵉ zᵉ
                byᵉ
                is-retraction-right-add-neg-ℤᵉ
                  ( (int-ℕᵉ lᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( int-ℕᵉ zᵉ))
              ＝ᵉ mod-ℕᵉ xᵉ zᵉ byᵉ mod-int-ℕᵉ xᵉ zᵉ))
```

### If `[y] | [z]` in `ℤ-Mod x`, then `z = dist-ℕ (kx, ly)` for some `k` and `l`

Ifᵉ `xᵉ = 0`,ᵉ thenᵉ weᵉ canᵉ simplyᵉ argueᵉ in `ℤ`.ᵉ Otherwise,ᵉ ifᵉ `[yᵉ] | [z]`ᵉ in
`ℤ-Modᵉ x`,ᵉ thereᵉ existsᵉ someᵉ equivalenceᵉ classᵉ `u`ᵉ in `ℤ-Modᵉ x`ᵉ suchᵉ thatᵉ
`[uᵉ] [yᵉ] ≡ᵉ [z]`ᵉ asᵉ aᵉ congruenceᵉ modᵉ `x`.ᵉ Thisᵉ `u`ᵉ canᵉ alwaysᵉ beᵉ chosenᵉ suchᵉ thatᵉ
`xᵉ >ᵉ uᵉ ≥ᵉ 0`.ᵉ Therefore,ᵉ thereᵉ existsᵉ someᵉ integerᵉ `aᵉ ≥ᵉ 0`ᵉ suchᵉ thatᵉ
`axᵉ = uyᵉ -ᵉ z`,ᵉ orᵉ `axᵉ = zᵉ -ᵉ uy`.ᵉ Inᵉ theᵉ firstᵉ case,ᵉ weᵉ canᵉ extractᵉ theᵉ distanceᵉ
conditionᵉ weᵉ desire.ᵉ Inᵉ theᵉ otherᵉ case,ᵉ weᵉ haveᵉ thatᵉ `axᵉ +ᵉ uyᵉ = z`.ᵉ Thisᵉ canᵉ beᵉ
writtenᵉ asᵉ `(aᵉ +ᵉ y)xᵉ +ᵉ (uᵉ -ᵉ x)yᵉ = z`,ᵉ soᵉ thatᵉ theᵉ secondᵉ termᵉ isᵉ nonpositive.ᵉ
Then,ᵉ in thisᵉ case,ᵉ weᵉ againᵉ canᵉ extractᵉ theᵉ distanceᵉ conditionᵉ weᵉ desire.ᵉ

```agda
cong-div-mod-ℤᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) (qᵉ : div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ)) →
  cong-ℤᵉ (int-ℕᵉ xᵉ) ((int-ℤ-Modᵉ xᵉ (pr1ᵉ qᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) (int-ℕᵉ zᵉ)
cong-div-mod-ℤᵉ xᵉ yᵉ zᵉ (uᵉ ,ᵉ pᵉ) =
  cong-eq-mod-ℤᵉ xᵉ
    ( (int-ℤ-Modᵉ xᵉ uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
    ( int-ℕᵉ zᵉ)
    ( equational-reasoningᵉ
      mod-ℤᵉ xᵉ ((int-ℤ-Modᵉ xᵉ uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      ＝ᵉ mul-ℤ-Modᵉ xᵉ (mod-ℤᵉ xᵉ (int-ℤ-Modᵉ xᵉ uᵉ)) (mod-ℤᵉ xᵉ (int-ℕᵉ yᵉ))
        byᵉ preserves-mul-mod-ℤᵉ xᵉ (int-ℤ-Modᵉ xᵉ uᵉ) (int-ℕᵉ yᵉ)
      ＝ᵉ mul-ℤ-Modᵉ xᵉ uᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ yᵉ))
        byᵉ
        apᵉ
          ( λ pᵉ → mul-ℤ-Modᵉ xᵉ pᵉ (mod-ℤᵉ xᵉ (int-ℕᵉ yᵉ)))
          ( is-section-int-ℤ-Modᵉ xᵉ uᵉ)
      ＝ᵉ mul-ℤ-Modᵉ xᵉ uᵉ (mod-ℕᵉ xᵉ yᵉ)
        byᵉ apᵉ (mul-ℤ-Modᵉ xᵉ uᵉ) (mod-int-ℕᵉ xᵉ yᵉ)
      ＝ᵉ mod-ℕᵉ xᵉ zᵉ byᵉ pᵉ
      ＝ᵉ mod-ℤᵉ xᵉ (int-ℕᵉ zᵉ) byᵉ invᵉ (mod-int-ℕᵉ xᵉ zᵉ))

is-distance-between-multiples-div-mod-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) →
  div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ) → is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ
is-distance-between-multiples-div-mod-ℕᵉ zero-ℕᵉ yᵉ zᵉ (uᵉ ,ᵉ pᵉ) =
  u-nonneg-case-splitᵉ (decide-is-nonnegative-is-nonnegative-neg-ℤᵉ {uᵉ})
  where
  u-nonneg-case-splitᵉ :
    (is-nonnegative-ℤᵉ uᵉ +ᵉ is-nonnegative-ℤᵉ (neg-ℤᵉ uᵉ)) →
    is-distance-between-multiples-ℕᵉ zero-ℕᵉ yᵉ zᵉ
  u-nonneg-case-splitᵉ (inlᵉ nonnegᵉ) =
    ( zero-ℕᵉ ,ᵉ
      abs-ℤᵉ uᵉ ,ᵉ
      is-injective-int-ℕᵉ
        ( invᵉ (mul-int-ℕᵉ (abs-ℤᵉ uᵉ) yᵉ) ∙ᵉ
          ( ( apᵉ
              ( _*ℤᵉ (int-ℕᵉ yᵉ))
              ( int-abs-is-nonnegative-ℤᵉ uᵉ nonnegᵉ)) ∙ᵉ
            ( pᵉ))))
  u-nonneg-case-splitᵉ (inrᵉ negᵉ) =
    ( zero-ℕᵉ ,ᵉ
      zero-ℕᵉ ,ᵉ
      is-injective-int-ℕᵉ
        ( invᵉ
          ( is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ
            ( is-nonnegative-int-ℕᵉ zᵉ)
            ( trᵉ
              ( is-nonnegative-ℤᵉ)
              ( left-negative-law-mul-ℤᵉ uᵉ (int-ℕᵉ yᵉ) ∙ᵉ apᵉ (neg-ℤᵉ) pᵉ)
              ( is-nonnegative-mul-ℤᵉ negᵉ (is-nonnegative-int-ℕᵉ yᵉ))))))

is-distance-between-multiples-div-mod-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ (uᵉ ,ᵉ pᵉ) =
  uy-z-case-splitᵉ (decide-is-nonnegative-is-nonnegative-neg-ℤᵉ
    { ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ))})
  where
  aᵉ : ℤᵉ
  aᵉ = pr1ᵉ (cong-div-mod-ℤᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ (uᵉ ,ᵉ pᵉ))

  a-eqn-posᵉ :
    add-ℤᵉ
      ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))) ＝ᵉ
    int-ℕᵉ zᵉ
  a-eqn-posᵉ =
    equational-reasoningᵉ
    add-ℤᵉ
      ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
    ＝ᵉ add-ℤᵉ
        ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      byᵉ
      commutative-add-ℤᵉ
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
        ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
    ＝ᵉ add-ℤᵉ
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      byᵉ
      apᵉ
        ( _+ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
        ( invᵉ (left-negative-law-mul-ℤᵉ aᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
    ＝ᵉ add-ℤᵉ
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( add-ℤᵉ
          ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ)))
          ( int-ℕᵉ zᵉ))
      byᵉ
      apᵉ
        ( ((neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ_)
        ( invᵉ
          ( is-section-right-add-neg-ℤᵉ
            ( int-ℕᵉ zᵉ)
            ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ))))
        ( int-ℕᵉ zᵉ)
      byᵉ
      invᵉ
        ( associative-add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ)))
          ( int-ℕᵉ zᵉ))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ( int-ℕᵉ zᵉ)
      byᵉ
      apᵉ
        ( λ pᵉ → (((neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ pᵉ) +ℤᵉ (int-ℕᵉ zᵉ))
        ( invᵉ (pr2ᵉ (cong-div-mod-ℤᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ (uᵉ ,ᵉ pᵉ))))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
          ( aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ( int-ℕᵉ zᵉ)
      byᵉ
      apᵉ
        ( λ pᵉ → (pᵉ +ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))) +ℤᵉ (int-ℕᵉ zᵉ))
        ( left-negative-law-mul-ℤᵉ aᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
    ＝ᵉ zero-ℤᵉ +ℤᵉ (int-ℕᵉ zᵉ)
      byᵉ
      apᵉ
        ( _+ℤᵉ (int-ℕᵉ zᵉ))
        ( left-inverse-law-add-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
    ＝ᵉ int-ℕᵉ zᵉ byᵉ left-unit-law-add-ℤᵉ (int-ℕᵉ zᵉ)

  a-extra-eqn-negᵉ :
    add-ℤᵉ
      ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
      ( neg-ℤᵉ
        ( mul-ℤᵉ
          ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
          ( int-ℕᵉ yᵉ))) ＝ᵉ
    ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ int-ℕᵉ yᵉ) +ℤᵉ (neg-ℤᵉ (aᵉ *ℤᵉ int-ℕᵉ (succ-ℕᵉ xᵉ)))
  a-extra-eqn-negᵉ =
    equational-reasoningᵉ
    add-ℤᵉ
      ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
      ( neg-ℤᵉ
        ( mul-ℤᵉ
          ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
          ( int-ℕᵉ yᵉ)))
    ＝ᵉ add-ℤᵉ
        ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( mul-ℤᵉ
          ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))))
          ( int-ℕᵉ yᵉ))
      byᵉ
      apᵉ
        ( (((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ_)
        ( invᵉ
          ( left-negative-law-mul-ℤᵉ
            ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
            ( int-ℕᵉ yᵉ)))
    ＝ᵉ add-ℤᵉ
        ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))) *ℤᵉ (int-ℕᵉ yᵉ))
      byᵉ
      apᵉ
        ( λ pᵉ →
          add-ℤᵉ
            ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( pᵉ *ℤᵉ (int-ℕᵉ yᵉ)))
        ( equational-reasoningᵉ
          neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
          ＝ᵉ neg-ℤᵉ ((neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)) +ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            byᵉ
            apᵉ
              ( neg-ℤᵉ)
              ( commutative-add-ℤᵉ
                ( int-ℕᵉ (succ-ℕᵉ xᵉ))
                ( neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
          ＝ᵉ add-ℤᵉ
              ( neg-ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
              ( neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            byᵉ
            distributive-neg-add-ℤᵉ
              ( neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))
              ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          ＝ᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            byᵉ
            apᵉ
              ( _+ℤᵉ (neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
              ( neg-neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
    ＝ᵉ add-ℤᵉ
        ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( add-ℤᵉ
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
          ( (neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) *ℤᵉ (int-ℕᵉ yᵉ)))
      byᵉ
      apᵉ
        ( (((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ_)
        ( right-distributive-mul-add-ℤᵉ
          ( int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)
          ( neg-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( int-ℕᵉ yᵉ))
    ＝ᵉ add-ℤᵉ
        ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( add-ℤᵉ
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
          ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
      byᵉ
      apᵉ
        ( λ pᵉ →
          add-ℤᵉ
            ( ((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ pᵉ))
        ( left-negative-law-mul-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)) (int-ℕᵉ yᵉ))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( (int-ℕᵉ yᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ( add-ℤᵉ
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
          ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
      byᵉ
      apᵉ
        ( _+ℤᵉ
          ( add-ℤᵉ
            ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
            ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))))
        ( right-distributive-mul-add-ℤᵉ (neg-ℤᵉ aᵉ) (int-ℕᵉ yᵉ) (int-ℕᵉ (succ-ℕᵉ xᵉ)))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
        ( add-ℤᵉ
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
          ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
      byᵉ
      apᵉ
        ( λ pᵉ →
          add-ℤᵉ
            ( ((neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ pᵉ)
            ( add-ℤᵉ
              ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
              ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))))
        ( commutative-mul-ℤᵉ (int-ℕᵉ yᵉ) (int-ℕᵉ (succ-ℕᵉ xᵉ)))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
        ( add-ℤᵉ
          ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
      byᵉ
      interchange-law-add-add-ℤᵉ
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
        ( neg-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
    ＝ᵉ add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
        ( zero-ℤᵉ)
      byᵉ
      apᵉ
        ( add-ℤᵉ
          ( add-ℤᵉ
            ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))))
          ( right-inverse-law-add-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
    ＝ᵉ add-ℤᵉ
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
      byᵉ
      right-unit-law-add-ℤᵉ
        ( add-ℤᵉ
          ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
    ＝ᵉ add-ℤᵉ
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
      byᵉ
      commutative-add-ℤᵉ
        ( (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
    ＝ᵉ add-ℤᵉ
        ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
        ( neg-ℤᵉ (aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
      byᵉ
      apᵉ
        ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ_)
        ( left-negative-law-mul-ℤᵉ aᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))

  uy-z-case-splitᵉ :
    ( ( is-nonnegative-ℤᵉ
        ( ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ)))) +ᵉ
      ( is-nonnegative-ℤᵉ
        ( neg-ℤᵉ
          ( add-ℤᵉ
            ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
            ( neg-ℤᵉ (int-ℕᵉ zᵉ)))))) →
    is-distance-between-multiples-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ
  uy-z-case-splitᵉ (inlᵉ uy-zᵉ) =
    ( abs-ℤᵉ aᵉ ,ᵉ
      nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ ,ᵉ
      ( equational-reasoningᵉ
        dist-ℕᵉ ((abs-ℤᵉ aᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)) ((nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ)
        ＝ᵉ dist-ℕᵉ ((nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ) ((abs-ℤᵉ aᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
          symmetric-dist-ℕᵉ
            ( (abs-ℤᵉ aᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
            ( (nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ)
        ＝ᵉ dist-ℤᵉ
            ( int-ℕᵉ ((nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ))
            ( int-ℕᵉ ((abs-ℤᵉ aᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
          invᵉ
            ( dist-int-ℕᵉ
              ( (nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ)
              ( (abs-ℤᵉ aᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
        ＝ᵉ dist-ℤᵉ
            ( int-ℕᵉ ((nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ))
            ( (int-ℕᵉ (abs-ℤᵉ aᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( dist-ℤᵉ (int-ℕᵉ ((nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℕᵉ yᵉ)))
            ( invᵉ (mul-int-ℕᵉ (abs-ℤᵉ aᵉ) (succ-ℕᵉ xᵉ)))
        ＝ᵉ dist-ℤᵉ
            ( (int-ℕᵉ (nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
            ( (int-ℕᵉ (abs-ℤᵉ aᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( λ pᵉ → dist-ℤᵉ pᵉ ((int-ℕᵉ (abs-ℤᵉ aᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
            ( invᵉ (mul-int-ℕᵉ (nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ) yᵉ))
        ＝ᵉ dist-ℤᵉ
            ( (int-ℕᵉ (nat-Finᵉ (succ-ℕᵉ xᵉ) uᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
            ( aᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( λ pᵉ →
              dist-ℤᵉ
                ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                ( pᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
            ( int-abs-is-nonnegative-ℤᵉ aᵉ a-is-nonnegative-ℤᵉ)
        ＝ᵉ abs-ℤᵉ (int-ℕᵉ zᵉ)
          byᵉ apᵉ (abs-ℤᵉ) a-eqn-posᵉ
        ＝ᵉ zᵉ
          byᵉ abs-int-ℕᵉ zᵉ))
    where
    a-is-nonnegative-ℤᵉ : is-nonnegative-ℤᵉ aᵉ
    a-is-nonnegative-ℤᵉ =
      is-nonnegative-left-factor-mul-ℤᵉ
        ( trᵉ
          ( is-nonnegative-ℤᵉ)
          ( invᵉ
            ( pr2ᵉ (cong-div-mod-ℤᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ (uᵉ ,ᵉ pᵉ))))
          ( uy-zᵉ))
        ( is-nonnegative-int-ℕᵉ (succ-ℕᵉ xᵉ))

  uy-z-case-splitᵉ (inrᵉ z-uyᵉ) =
    ( (abs-ℤᵉ aᵉ) +ℕᵉ yᵉ ,ᵉ
      abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))) ,ᵉ
      ( equational-reasoningᵉ
        dist-ℕᵉ (((abs-ℤᵉ aᵉ) +ℕᵉ yᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
          (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ)
        ＝ᵉ dist-ℤᵉ (int-ℕᵉ (((abs-ℤᵉ aᵉ) +ℕᵉ yᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
          (int-ℕᵉ (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ))
        byᵉ invᵉ (dist-int-ℕᵉ (((abs-ℤᵉ aᵉ) +ℕᵉ yᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
          (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ))
        ＝ᵉ dist-ℤᵉ ((int-ℕᵉ ((abs-ℤᵉ aᵉ) +ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (int-ℕᵉ (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ))
        byᵉ apᵉ (λ pᵉ → dist-ℤᵉ pᵉ (int-ℕᵉ (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ)))
          (invᵉ (mul-int-ℕᵉ ((abs-ℤᵉ aᵉ) +ℕᵉ yᵉ) (succ-ℕᵉ xᵉ)))
        ＝ᵉ dist-ℤᵉ (((int-ℕᵉ (abs-ℤᵉ aᵉ)) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (int-ℕᵉ (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ))
        byᵉ
          apᵉ
            ( λ pᵉ →
              dist-ℤᵉ
                ( pᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
                ( int-ℕᵉ (mul-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
                  (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ)))
          (invᵉ (add-int-ℕᵉ (abs-ℤᵉ aᵉ) yᵉ))
        ＝ᵉ dist-ℤᵉ (((int-ℕᵉ (abs-ℤᵉ aᵉ)) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (mul-ℤᵉ (int-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))))) (int-ℕᵉ yᵉ))
        byᵉ
          apᵉ
            ( dist-ℤᵉ (((int-ℕᵉ (abs-ℤᵉ aᵉ)) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
            ( invᵉ (mul-int-ℕᵉ (abs-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
              (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))) yᵉ))
        ＝ᵉ dist-ℤᵉ (((int-ℕᵉ (abs-ℤᵉ aᵉ)) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (mul-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
            (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))) (int-ℕᵉ yᵉ))
          byᵉ apᵉ (λ pᵉ → dist-ℤᵉ (((int-ℕᵉ (abs-ℤᵉ aᵉ)) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ
              (int-ℕᵉ (succ-ℕᵉ xᵉ))) (pᵉ *ℤᵉ (int-ℕᵉ yᵉ)))
          (int-abs-is-nonnegative-ℤᵉ ((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ
            (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))) (int-ℤ-Mod-boundedᵉ xᵉ uᵉ))
        ＝ᵉ dist-ℤᵉ
            ( ((int-ℕᵉ (abs-ℤᵉ (neg-ℤᵉ aᵉ))) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( mul-ℤᵉ
              ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
              ( int-ℕᵉ yᵉ))
        byᵉ
          apᵉ
            ( λ pᵉ →
              dist-ℤᵉ
                ( ((int-ℕᵉ pᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
                ( mul-ℤᵉ
                  ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ)))
                  ( int-ℕᵉ yᵉ)))
          (invᵉ (abs-neg-ℤᵉ aᵉ))
        ＝ᵉ dist-ℤᵉ (((neg-ℤᵉ aᵉ) +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (mul-ℤᵉ
            ( (int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))) (int-ℕᵉ yᵉ))
        byᵉ apᵉ (λ pᵉ → dist-ℤᵉ ((pᵉ +ℤᵉ (int-ℕᵉ yᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (((int-ℕᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ))) *ℤᵉ
            (int-ℕᵉ yᵉ)))
          (int-abs-is-nonnegative-ℤᵉ (neg-ℤᵉ aᵉ) neg-a-is-nonnegative-ℤᵉ)
        ＝ᵉ abs-ℤᵉ (int-ℕᵉ zᵉ)
        byᵉ apᵉ abs-ℤᵉ (a-extra-eqn-negᵉ ∙ᵉ a-eqn-posᵉ)
        ＝ᵉ zᵉ byᵉ abs-int-ℕᵉ zᵉ))
    where
    neg-a-is-nonnegative-ℤᵉ : is-nonnegative-ℤᵉ (neg-ℤᵉ aᵉ)
    neg-a-is-nonnegative-ℤᵉ =
      is-nonnegative-left-factor-mul-ℤᵉ
        ( trᵉ is-nonnegative-ℤᵉ
          ( equational-reasoningᵉ
            ( neg-ℤᵉ (((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
              ( neg-ℤᵉ (int-ℕᵉ zᵉ))))
            ＝ᵉ ( neg-ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ
                ( neg-ℤᵉ (neg-ℤᵉ (int-ℕᵉ zᵉ)))
              byᵉ
                ( distributive-neg-add-ℤᵉ
                  ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( neg-ℤᵉ (int-ℕᵉ zᵉ)))
            ＝ᵉ ( neg-ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ
                ( int-ℕᵉ zᵉ)
              byᵉ
                apᵉ
                  ( (neg-ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ_)
                  ( neg-neg-ℤᵉ (int-ℕᵉ zᵉ))
            ＝ᵉ add-ℤᵉ
              ( int-ℕᵉ zᵉ)
              ( neg-ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
              byᵉ
                commutative-add-ℤᵉ
                  ( neg-ℤᵉ ((int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)))
                  ( int-ℕᵉ zᵉ)
            ＝ᵉ (neg-ℤᵉ aᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))
              byᵉ invᵉ (pr2ᵉ
                ( symmetric-cong-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))
                ( (int-ℤ-Modᵉ (succ-ℕᵉ xᵉ) uᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) (int-ℕᵉ zᵉ)
                ( cong-div-mod-ℤᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ (uᵉ ,ᵉ pᵉ)))))
          ( z-uyᵉ))
          ( is-nonnegative-int-ℕᵉ (succ-ℕᵉ xᵉ))
```

### The type `is-distance-between-multiples-ℕ x y z` is decidable

```agda
is-decidable-is-distance-between-multiples-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → is-decidableᵉ (is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ)
is-decidable-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ =
  decidable-div-ℤ-case-splitᵉ
    (is-decidable-div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ))
  where
  decidable-div-ℤ-case-splitᵉ :
    ( div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ) +ᵉ
      ¬ᵉ ( div-ℤ-Modᵉ xᵉ (mod-ℕᵉ xᵉ yᵉ) (mod-ℕᵉ xᵉ zᵉ))) →
    is-decidableᵉ (is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ)
  decidable-div-ℤ-case-splitᵉ (inlᵉ div-Modᵉ) =
    inlᵉ (is-distance-between-multiples-div-mod-ℕᵉ xᵉ yᵉ zᵉ div-Modᵉ)
  decidable-div-ℤ-case-splitᵉ (inrᵉ neg-div-Modᵉ) =
    inrᵉ (λ distᵉ → neg-div-Modᵉ
      (div-mod-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ distᵉ))
```

## Theorem

Sinceᵉ `is-distance-between-multiples-ℕᵉ xᵉ yᵉ z`ᵉ isᵉ decidable,ᵉ weᵉ canᵉ proveᵉ
Bezout'sᵉ lemmaᵉ byᵉ theᵉ well-orderingᵉ principle.ᵉ First,ᵉ takeᵉ theᵉ leastᵉ positiveᵉ
distanceᵉ `d`ᵉ betweenᵉ multiplesᵉ ofᵉ `x`ᵉ andᵉ `y`.ᵉ

```agda
pos-distance-between-multiplesᵉ : (xᵉ yᵉ zᵉ : ℕᵉ) → UUᵉ lzero
pos-distance-between-multiplesᵉ xᵉ yᵉ zᵉ = is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ) →
  (is-nonzero-ℕᵉ zᵉ) ×ᵉ (is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ)

is-inhabited-pos-distance-between-multiplesᵉ :
  (xᵉ yᵉ : ℕᵉ) → Σᵉ ℕᵉ (pos-distance-between-multiplesᵉ xᵉ yᵉ)
is-inhabited-pos-distance-between-multiplesᵉ zero-ℕᵉ zero-ℕᵉ =
  pairᵉ zero-ℕᵉ (λ Hᵉ → ex-falsoᵉ (Hᵉ reflᵉ))
is-inhabited-pos-distance-between-multiplesᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) =
  pairᵉ (succ-ℕᵉ yᵉ) (λ Hᵉ → pair'ᵉ (is-nonzero-succ-ℕᵉ yᵉ)
    (pairᵉ zero-ℕᵉ (pairᵉ 1 (apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ yᵉ)))))
is-inhabited-pos-distance-between-multiplesᵉ (succ-ℕᵉ xᵉ) yᵉ = pairᵉ (succ-ℕᵉ xᵉ)
  (λ Hᵉ → pair'ᵉ (is-nonzero-succ-ℕᵉ xᵉ)
    (pairᵉ 1 (pairᵉ zero-ℕᵉ (apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ xᵉ)))))

minimal-pos-distance-between-multiplesᵉ :
  (xᵉ yᵉ : ℕᵉ) → minimal-element-ℕᵉ (pos-distance-between-multiplesᵉ xᵉ yᵉ)
minimal-pos-distance-between-multiplesᵉ xᵉ yᵉ = well-ordering-principle-ℕᵉ
  (pos-distance-between-multiplesᵉ xᵉ yᵉ)
  (λ zᵉ → is-decidable-function-typeᵉ
    (is-decidable-negᵉ (is-decidable-is-zero-ℕᵉ (xᵉ +ℕᵉ yᵉ)))
    (is-decidable-productᵉ (is-decidable-negᵉ (is-decidable-is-zero-ℕᵉ zᵉ))
      (is-decidable-is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ)))
  (is-inhabited-pos-distance-between-multiplesᵉ xᵉ yᵉ)

minimal-positive-distanceᵉ : (xᵉ yᵉ : ℕᵉ) → ℕᵉ
minimal-positive-distanceᵉ xᵉ yᵉ = pr1ᵉ (minimal-pos-distance-between-multiplesᵉ xᵉ yᵉ)
```

Thenᵉ `d`ᵉ dividesᵉ bothᵉ `x`ᵉ andᵉ `y`.ᵉ Sinceᵉ `gcdᵉ xᵉ y`ᵉ dividesᵉ anyᵉ numberᵉ ofᵉ theᵉ
formᵉ `dist-ℕᵉ (kx,ly)`,ᵉ itᵉ followsᵉ thatᵉ `gcdᵉ xᵉ yᵉ | d`,ᵉ andᵉ henceᵉ thatᵉ
`gcdᵉ xᵉ yᵉ ＝ᵉ d`.ᵉ

```agda
minimal-positive-distance-is-distanceᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ) →
  (is-distance-between-multiples-ℕᵉ xᵉ yᵉ (minimal-positive-distanceᵉ xᵉ yᵉ))
minimal-positive-distance-is-distanceᵉ xᵉ yᵉ nonzeroᵉ =
  pr2ᵉ ((pr1ᵉ (pr2ᵉ (minimal-pos-distance-between-multiplesᵉ xᵉ yᵉ))) nonzeroᵉ)

minimal-positive-distance-is-minimalᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  is-lower-bound-ℕᵉ
    ( pos-distance-between-multiplesᵉ xᵉ yᵉ)
    ( minimal-positive-distanceᵉ xᵉ yᵉ)
minimal-positive-distance-is-minimalᵉ xᵉ yᵉ =
  pr2ᵉ (pr2ᵉ (minimal-pos-distance-between-multiplesᵉ xᵉ yᵉ))

minimal-positive-distance-nonzeroᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  (is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ)) →
  (is-nonzero-ℕᵉ (minimal-positive-distanceᵉ xᵉ yᵉ))
minimal-positive-distance-nonzeroᵉ xᵉ yᵉ nonzeroᵉ =
  pr1ᵉ ((pr1ᵉ (pr2ᵉ (minimal-pos-distance-between-multiplesᵉ xᵉ yᵉ))) nonzeroᵉ)

minimal-positive-distance-leq-symᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  leq-ℕᵉ (minimal-positive-distanceᵉ xᵉ yᵉ) (minimal-positive-distanceᵉ yᵉ xᵉ)
minimal-positive-distance-leq-symᵉ xᵉ yᵉ =
  minimal-positive-distance-is-minimalᵉ xᵉ yᵉ (minimal-positive-distanceᵉ yᵉ xᵉ)
  (λ Hᵉ →
    pair'ᵉ
      ( minimal-positive-distance-nonzeroᵉ
        ( yᵉ)
        ( xᵉ)
        ( λ Kᵉ → Hᵉ (commutative-add-ℕᵉ xᵉ yᵉ ∙ᵉ Kᵉ)))
      ( is-distance-between-multiples-sym-ℕᵉ
        ( yᵉ)
        ( xᵉ)
        ( minimal-positive-distanceᵉ yᵉ xᵉ)
        ( minimal-positive-distance-is-distanceᵉ
          ( yᵉ)
          ( xᵉ)
          ( λ Kᵉ → Hᵉ (commutative-add-ℕᵉ xᵉ yᵉ ∙ᵉ Kᵉ)))))

minimal-positive-distance-symᵉ :
  (xᵉ yᵉ : ℕᵉ) → minimal-positive-distanceᵉ xᵉ yᵉ ＝ᵉ minimal-positive-distanceᵉ yᵉ xᵉ
minimal-positive-distance-symᵉ xᵉ yᵉ = antisymmetric-leq-ℕᵉ
  (minimal-positive-distanceᵉ xᵉ yᵉ)
  (minimal-positive-distanceᵉ yᵉ xᵉ)
  (minimal-positive-distance-leq-symᵉ xᵉ yᵉ)
  (minimal-positive-distance-leq-symᵉ yᵉ xᵉ)

minimal-positive-distance-x-coeffᵉ : (xᵉ yᵉ : ℕᵉ) → (is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ)) → ℕᵉ
minimal-positive-distance-x-coeffᵉ xᵉ yᵉ Hᵉ =
  pr1ᵉ (minimal-positive-distance-is-distanceᵉ xᵉ yᵉ Hᵉ)

minimal-positive-distance-succ-x-coeffᵉ : (xᵉ yᵉ : ℕᵉ) → ℕᵉ
minimal-positive-distance-succ-x-coeffᵉ xᵉ yᵉ =
  minimal-positive-distance-x-coeffᵉ
    ( succ-ℕᵉ xᵉ)
    ( yᵉ)
    ( trᵉ
      ( is-nonzero-ℕᵉ)
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
      ( is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)))

minimal-positive-distance-y-coeffᵉ : (xᵉ yᵉ : ℕᵉ) → (is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ)) → ℕᵉ
minimal-positive-distance-y-coeffᵉ xᵉ yᵉ Hᵉ =
  pr1ᵉ (pr2ᵉ (minimal-positive-distance-is-distanceᵉ xᵉ yᵉ Hᵉ))

minimal-positive-distance-succ-y-coeffᵉ : (xᵉ yᵉ : ℕᵉ) → ℕᵉ
minimal-positive-distance-succ-y-coeffᵉ xᵉ yᵉ =
  minimal-positive-distance-y-coeffᵉ
    ( succ-ℕᵉ xᵉ)
    ( yᵉ)
    ( trᵉ
      ( is-nonzero-ℕᵉ)
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
      ( is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)))

minimal-positive-distance-eqnᵉ :
  (xᵉ yᵉ : ℕᵉ) (Hᵉ : is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ)) →
  dist-ℕᵉ
    ( (minimal-positive-distance-x-coeffᵉ xᵉ yᵉ Hᵉ) *ℕᵉ xᵉ)
    ( (minimal-positive-distance-y-coeffᵉ xᵉ yᵉ Hᵉ) *ℕᵉ yᵉ) ＝ᵉ
  minimal-positive-distanceᵉ xᵉ yᵉ
minimal-positive-distance-eqnᵉ xᵉ yᵉ Hᵉ =
  pr2ᵉ (pr2ᵉ (minimal-positive-distance-is-distanceᵉ xᵉ yᵉ Hᵉ))

minimal-positive-distance-succ-eqnᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  dist-ℕᵉ
    ( (minimal-positive-distance-succ-x-coeffᵉ xᵉ yᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
    ( (minimal-positive-distance-succ-y-coeffᵉ xᵉ yᵉ) *ℕᵉ yᵉ) ＝ᵉ
  minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ
minimal-positive-distance-succ-eqnᵉ xᵉ yᵉ =
  minimal-positive-distance-eqnᵉ
    ( succ-ℕᵉ xᵉ)
    ( yᵉ)
    ( trᵉ
      ( is-nonzero-ℕᵉ)
      ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
      ( is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)))

minimal-positive-distance-div-succ-x-eqnᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  add-ℤᵉ
    ( mul-ℤᵉ
      ( int-ℕᵉ
        ( quotient-euclidean-division-ℕᵉ
          ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
          ( succ-ℕᵉ xᵉ)))
      ( int-ℕᵉ (minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)))
    ( int-ℕᵉ
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ))) ＝ᵉ
      int-ℕᵉ (succ-ℕᵉ xᵉ)
minimal-positive-distance-div-succ-x-eqnᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      add-ℤᵉ
        ( mul-ℤᵉ
          ( int-ℕᵉ
            ( quotient-euclidean-division-ℕᵉ
              ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
              ( succ-ℕᵉ xᵉ)))
          ( int-ℕᵉ (minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)))
        ( int-ℕᵉ
          ( remainder-euclidean-division-ℕᵉ
            ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
            ( succ-ℕᵉ xᵉ)))
      ＝ᵉ add-ℤᵉ
          ( int-ℕᵉ
            ( mul-ℕᵉ
              ( quotient-euclidean-division-ℕᵉ
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                ( succ-ℕᵉ xᵉ))
              ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)))
          ( int-ℕᵉ
            ( remainder-euclidean-division-ℕᵉ
              ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
              ( succ-ℕᵉ xᵉ)))
          byᵉ
            ( apᵉ
              ( _+ℤᵉ
                ( int-ℕᵉ
                  ( remainder-euclidean-division-ℕᵉ
                    ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                    ( succ-ℕᵉ xᵉ))))
              ( mul-int-ℕᵉ
                ( quotient-euclidean-division-ℕᵉ
                  ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                  ( succ-ℕᵉ xᵉ))
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)))
      ＝ᵉ int-ℕᵉ
            ( add-ℕᵉ
              ( mul-ℕᵉ
                ( quotient-euclidean-division-ℕᵉ
                  ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                  ( succ-ℕᵉ xᵉ))
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ))
              ( remainder-euclidean-division-ℕᵉ
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                ( succ-ℕᵉ xᵉ)))
          byᵉ
            ( add-int-ℕᵉ
              ( mul-ℕᵉ
                ( quotient-euclidean-division-ℕᵉ
                  ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                  ( succ-ℕᵉ xᵉ))
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ))
              ( remainder-euclidean-division-ℕᵉ
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                ( succ-ℕᵉ xᵉ)))
      ＝ᵉ int-ℕᵉ (succ-ℕᵉ xᵉ)
          byᵉ
            apᵉ
              ( int-ℕᵉ)
              ( eq-euclidean-division-ℕᵉ
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                ( succ-ℕᵉ xᵉ))

remainder-min-dist-succ-x-le-min-distᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  le-ℕᵉ
    ( remainder-euclidean-division-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( succ-ℕᵉ xᵉ))
    ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
remainder-min-dist-succ-x-le-min-distᵉ xᵉ yᵉ =
  strict-upper-bound-remainder-euclidean-division-ℕᵉ
    ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
    ( succ-ℕᵉ xᵉ)
    ( minimal-positive-distance-nonzeroᵉ
      ( succ-ℕᵉ xᵉ)
      ( yᵉ)
      ( trᵉ
        ( is-nonzero-ℕᵉ)
        ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
        ( is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ))))

remainder-min-dist-succ-x-is-distanceᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  (is-distance-between-multiples-ℕᵉ
    ( succ-ℕᵉ xᵉ)
    ( yᵉ)
    ( remainder-euclidean-division-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( succ-ℕᵉ xᵉ)))
remainder-min-dist-succ-x-is-distanceᵉ xᵉ yᵉ =
  sx-ty-case-splitᵉ (linear-leq-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)) (tᵉ *ℕᵉ yᵉ))
  where
  dᵉ : ℕᵉ
  dᵉ = minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ

  sᵉ : ℕᵉ
  sᵉ = minimal-positive-distance-succ-x-coeffᵉ xᵉ yᵉ

  tᵉ : ℕᵉ
  tᵉ = minimal-positive-distance-succ-y-coeffᵉ xᵉ yᵉ

  qᵉ : ℕᵉ
  qᵉ = quotient-euclidean-division-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)

  rᵉ : ℕᵉ
  rᵉ = remainder-euclidean-division-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)

  dist-sx-ty-eq-dᵉ : dist-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)) (tᵉ *ℕᵉ yᵉ) ＝ᵉ dᵉ
  dist-sx-ty-eq-dᵉ = minimal-positive-distance-succ-eqnᵉ xᵉ yᵉ

  sx-ty-case-splitᵉ :
    ( leq-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)) (tᵉ *ℕᵉ yᵉ) +ᵉ
      leq-ℕᵉ (tᵉ *ℕᵉ yᵉ) (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))) →
    is-distance-between-multiples-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ rᵉ
  sx-ty-case-splitᵉ (inlᵉ sxtyᵉ) =
    ((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1 ,ᵉ qᵉ *ℕᵉ tᵉ ,ᵉ invᵉ (dist-eqnᵉ))
    where
    add-dist-eqnᵉ :
      int-ℕᵉ dᵉ ＝ᵉ
      ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
    add-dist-eqnᵉ =
      equational-reasoningᵉ
        int-ℕᵉ dᵉ
        ＝ᵉ ((int-ℕᵉ dᵉ) +ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))) +ℤᵉ
          (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ
          invᵉ
            ( is-retraction-right-add-neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))) (int-ℕᵉ dᵉ))
        ＝ᵉ (int-ℕᵉ (dᵉ +ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))) +ℤᵉ
          (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ
          apᵉ
            ( _+ℤᵉ (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( add-int-ℕᵉ dᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))
        ＝ᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ apᵉ (λ Hᵉ → (int-ℕᵉ Hᵉ) +ℤᵉ (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))))
            (rewrite-left-dist-add-ℕᵉ dᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
              (tᵉ *ℕᵉ yᵉ) sxtyᵉ (invᵉ (dist-sx-ty-eq-dᵉ)))
        ＝ᵉ ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ
          apᵉ
            ( _+ℤᵉ (neg-ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( invᵉ (mul-int-ℕᵉ tᵉ yᵉ))
        ＝ᵉ ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (neg-ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ
          apᵉ
            ( λ Hᵉ → ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (neg-ℤᵉ Hᵉ))
            ( invᵉ (mul-int-ℕᵉ sᵉ (succ-ℕᵉ xᵉ)))
        ＝ᵉ ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
          apᵉ
            ( ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ_)
            ( invᵉ (left-negative-law-mul-ℤᵉ (int-ℕᵉ sᵉ) (int-ℕᵉ (succ-ℕᵉ xᵉ))))

    isolate-rem-eqnᵉ :
      int-ℕᵉ rᵉ ＝ᵉ
      add-ℤᵉ
        ( neg-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ qᵉ)
            ( add-ℤᵉ
              ( (int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
              ( (neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
        ( int-ℕᵉ (succ-ℕᵉ xᵉ))
    isolate-rem-eqnᵉ =
      equational-reasoningᵉ
        int-ℕᵉ rᵉ
        ＝ᵉ add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
          (add-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
              ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
          (int-ℕᵉ rᵉ))
          byᵉ invᵉ (is-retraction-left-add-neg-ℤᵉ
            ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            (int-ℕᵉ rᵉ))
        ＝ᵉ add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
          (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ dᵉ)) +ℤᵉ (int-ℕᵉ rᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( mul-ℤᵉ
                      ( int-ℕᵉ qᵉ)
                      ( add-ℤᵉ
                        ( (int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                        ( (neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
                  ( ((int-ℕᵉ qᵉ) *ℤᵉ Hᵉ) +ℤᵉ (int-ℕᵉ rᵉ)))
              ( invᵉ add-dist-eqnᵉ)
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( mul-ℤᵉ
                ( int-ℕᵉ qᵉ)
                ( add-ℤᵉ
                  ( (int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( (neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( add-ℤᵉ
                ( neg-ℤᵉ
                  ( mul-ℤᵉ
                    ( int-ℕᵉ qᵉ)
                    ( add-ℤᵉ
                      ( (int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
                      ( (neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))))
              ( minimal-positive-distance-div-succ-x-eqnᵉ xᵉ yᵉ)

    rearrange-arith-eqnᵉ :
      add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
        ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))) (int-ℕᵉ (succ-ℕᵉ xᵉ))
      ＝ᵉ add-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ one-ℤᵉ) *ℤᵉ
          (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
    rearrange-arith-eqnᵉ =
      equational-reasoningᵉ
        add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))) (int-ℕᵉ (succ-ℕᵉ xᵉ))
        ＝ᵉ add-ℤᵉ (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ
          ((int-ℕᵉ qᵉ) *ℤᵉ ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ (apᵉ (λ Hᵉ → (neg-ℤᵉ Hᵉ) +ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (left-distributive-mul-add-ℤᵉ (int-ℕᵉ qᵉ) ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))
              ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
        ＝ᵉ add-ℤᵉ (neg-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          ((int-ℕᵉ qᵉ) *ℤᵉ ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ (apᵉ (λ Hᵉ → add-ℤᵉ (neg-ℤᵉ (Hᵉ +ℤᵉ (mul-ℤᵉ (int-ℕᵉ qᵉ)
            ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))) (int-ℕᵉ (succ-ℕᵉ xᵉ)))
              (invᵉ (associative-mul-ℤᵉ (int-ℕᵉ qᵉ) (int-ℕᵉ tᵉ) (int-ℕᵉ yᵉ))))
        ＝ᵉ add-ℤᵉ (neg-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ Hᵉ))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( equational-reasoningᵉ
                ((int-ℕᵉ qᵉ) *ℤᵉ ((neg-ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
                ＝ᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (neg-ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))
                  byᵉ
                    invᵉ
                      ( associative-mul-ℤᵉ
                        ( int-ℕᵉ qᵉ)
                        ( neg-ℤᵉ (int-ℕᵉ sᵉ))
                        ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
                ＝ᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))
                  byᵉ apᵉ (_*ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
                  (right-negative-law-mul-ℤᵉ (int-ℕᵉ qᵉ) (int-ℕᵉ sᵉ))
                ＝ᵉ neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
                  byᵉ
                    left-negative-law-mul-ℤᵉ
                      ( (int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))
                      ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ＝ᵉ add-ℤᵉ
            ( add-ℤᵉ
              ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
              ( neg-ℤᵉ
                ( neg-ℤᵉ
                  ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( _+ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( distributive-neg-add-ℤᵉ
                ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
        ＝ᵉ add-ℤᵉ
            ( add-ℤᵉ
              ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
              ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
              add-ℤᵉ
                ( (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ Hᵉ)
                ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( neg-neg-ℤᵉ
                ( ((int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ
          ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ associative-add-ℤᵉ
            (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
        ＝ᵉ add-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ
          (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
          byᵉ commutative-add-ℤᵉ
            (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))
        ＝ᵉ add-ℤᵉ
            ( mul-ℤᵉ
              ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ one-ℤᵉ)
              ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
          byᵉ
            apᵉ
              ( _+ℤᵉ (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))))
              ( apᵉ
                ( (((int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ_)
                ( left-unit-law-mul-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) ∙ᵉ
                ( invᵉ
                  ( right-distributive-mul-add-ℤᵉ
                    ( (int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))
                    ( one-ℤᵉ)
                    ( int-ℕᵉ (succ-ℕᵉ xᵉ)))))

    dist-eqnᵉ :
      rᵉ ＝ᵉ dist-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)) ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
    dist-eqnᵉ =
      equational-reasoningᵉ
        rᵉ
        ＝ᵉ abs-ℤᵉ (int-ℕᵉ rᵉ)
          byᵉ (invᵉ (abs-int-ℕᵉ rᵉ))
        ＝ᵉ dist-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ one-ℤᵉ) *ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ (apᵉ (abs-ℤᵉ) (isolate-rem-eqnᵉ ∙ᵉ rearrange-arith-eqnᵉ))
        ＝ᵉ dist-ℤᵉ
            ( ((int-ℕᵉ (qᵉ *ℕᵉ sᵉ)) +ℤᵉ (int-ℕᵉ 1ᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ apᵉ (λ Hᵉ → dist-ℤᵉ ((Hᵉ +ℤᵉ (int-ℕᵉ 1ᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            (mul-int-ℕᵉ qᵉ sᵉ)
        ＝ᵉ dist-ℤᵉ ((int-ℕᵉ ((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ apᵉ (λ Hᵉ → dist-ℤᵉ (Hᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            (add-int-ℕᵉ (qᵉ *ℕᵉ sᵉ) 1ᵉ)
        ＝ᵉ dist-ℤᵉ (int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
          (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ apᵉ (λ Hᵉ → dist-ℤᵉ Hᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
            (mul-int-ℕᵉ ((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) (succ-ℕᵉ xᵉ))
        ＝ᵉ dist-ℤᵉ (int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
          ((int-ℕᵉ (qᵉ *ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          byᵉ apᵉ (λ Hᵉ → dist-ℤᵉ (int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
            (Hᵉ *ℤᵉ (int-ℕᵉ yᵉ)))
            (mul-int-ℕᵉ qᵉ tᵉ)
        ＝ᵉ dist-ℤᵉ (int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ)))
          (int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ))
          byᵉ apᵉ (dist-ℤᵉ (int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))))
            (mul-int-ℕᵉ (qᵉ *ℕᵉ tᵉ) yᵉ)
        ＝ᵉ dist-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
          ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
          byᵉ dist-int-ℕᵉ (((qᵉ *ℕᵉ sᵉ) +ℕᵉ 1ᵉ) *ℕᵉ (succ-ℕᵉ xᵉ))
            ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)

  sx-ty-case-splitᵉ (inrᵉ tysxᵉ) =
    (abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) ,ᵉ
      (qᵉ *ℕᵉ tᵉ) ,ᵉ invᵉ (dist-eqnᵉ))
    where
    rewrite-distᵉ : (tᵉ *ℕᵉ yᵉ) +ℕᵉ dᵉ ＝ᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
    rewrite-distᵉ =
      rewrite-right-dist-add-ℕᵉ
        ( tᵉ *ℕᵉ yᵉ)
        ( dᵉ)
        ( sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
        ( tysxᵉ)
        ( invᵉ (dist-sx-ty-eq-dᵉ) ∙ᵉ
          symmetric-dist-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)) (tᵉ *ℕᵉ yᵉ))

    quotient-min-dist-succ-x-nonzeroᵉ : is-nonzero-ℕᵉ qᵉ
    quotient-min-dist-succ-x-nonzeroᵉ iszeroᵉ =
      contradiction-le-ℕᵉ (succ-ℕᵉ xᵉ) dᵉ le-x-dᵉ leq-d-xᵉ
      where
      x-r-equalityᵉ : succ-ℕᵉ xᵉ ＝ᵉ rᵉ
      x-r-equalityᵉ =
        equational-reasoningᵉ
          succ-ℕᵉ xᵉ
          ＝ᵉ (qᵉ *ℕᵉ dᵉ) +ℕᵉ rᵉ
            byᵉ (invᵉ (eq-euclidean-division-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)))
          ＝ᵉ (0ᵉ *ℕᵉ dᵉ) +ℕᵉ rᵉ
            byᵉ (apᵉ (λ Hᵉ → (Hᵉ *ℕᵉ dᵉ) +ℕᵉ rᵉ) iszeroᵉ)
          ＝ᵉ 0 +ℕᵉ rᵉ
            byᵉ (apᵉ (_+ℕᵉ rᵉ) (left-zero-law-mul-ℕᵉ dᵉ))
          ＝ᵉ rᵉ
            byᵉ (left-unit-law-add-ℕᵉ rᵉ)

      le-x-dᵉ : le-ℕᵉ (succ-ℕᵉ xᵉ) dᵉ
      le-x-dᵉ =
        trᵉ
          ( λ nᵉ → le-ℕᵉ nᵉ dᵉ)
          ( invᵉ (x-r-equalityᵉ))
          ( remainder-min-dist-succ-x-le-min-distᵉ xᵉ yᵉ)

      x-pos-distᵉ : pos-distance-between-multiplesᵉ (succ-ℕᵉ xᵉ) yᵉ (succ-ℕᵉ xᵉ)
      x-pos-distᵉ Hᵉ =
        pair'ᵉ
          ( is-nonzero-succ-ℕᵉ xᵉ)
          ( pairᵉ 1 (pairᵉ 0 (apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ xᵉ))))

      leq-d-xᵉ : leq-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)
      leq-d-xᵉ =
        minimal-positive-distance-is-minimalᵉ (succ-ℕᵉ xᵉ) yᵉ (succ-ℕᵉ xᵉ) x-pos-distᵉ

    min-dist-succ-x-coeff-nonzeroᵉ : is-nonzero-ℕᵉ sᵉ
    min-dist-succ-x-coeff-nonzeroᵉ iszeroᵉ =
      minimal-positive-distance-nonzeroᵉ
        ( succ-ℕᵉ xᵉ)
        ( yᵉ)
        ( trᵉ
          ( is-nonzero-ℕᵉ)
          ( invᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ))
          ( is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)))
        ( d-is-zeroᵉ)
      where
      zero-additionᵉ : (tᵉ *ℕᵉ yᵉ) +ℕᵉ dᵉ ＝ᵉ 0
      zero-additionᵉ =
        equational-reasoningᵉ
          (tᵉ *ℕᵉ yᵉ) +ℕᵉ dᵉ
          ＝ᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
            byᵉ rewrite-distᵉ
          ＝ᵉ (zero-ℕᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
            byᵉ (apᵉ (_*ℕᵉ (succ-ℕᵉ xᵉ)) iszeroᵉ)
          ＝ᵉ zero-ℕᵉ
            byᵉ (left-zero-law-mul-ℕᵉ (succ-ℕᵉ xᵉ))

      d-is-zeroᵉ : is-zero-ℕᵉ dᵉ
      d-is-zeroᵉ = is-zero-right-is-zero-add-ℕᵉ (tᵉ *ℕᵉ yᵉ) dᵉ (zero-additionᵉ)

    coeff-nonnegativeᵉ : leq-ℤᵉ one-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))
    coeff-nonnegativeᵉ = trᵉ (leq-ℤᵉ one-ℤᵉ)
      (invᵉ (mul-int-ℕᵉ qᵉ sᵉ)) (leq-int-ℕᵉ 1 (qᵉ *ℕᵉ sᵉ)
        (leq-succ-le-ℕᵉ 0 (qᵉ *ℕᵉ sᵉ) (le-is-nonzero-ℕᵉ (qᵉ *ℕᵉ sᵉ)
          (is-nonzero-mul-ℕᵉ qᵉ sᵉ quotient-min-dist-succ-x-nonzeroᵉ
            min-dist-succ-x-coeff-nonzeroᵉ))))

    add-dist-eqnᵉ :
      int-ℕᵉ dᵉ ＝ᵉ
      ((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
    add-dist-eqnᵉ =
      equational-reasoningᵉ
        int-ℕᵉ dᵉ
        ＝ᵉ (neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ))) +ℤᵉ ((int-ℕᵉ (tᵉ *ℕᵉ yᵉ)) +ℤᵉ (int-ℕᵉ dᵉ))
          byᵉ invᵉ (is-retraction-left-add-neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ)) (int-ℕᵉ dᵉ))
        ＝ᵉ (neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ))) +ℤᵉ (int-ℕᵉ ((tᵉ *ℕᵉ yᵉ) +ℕᵉ dᵉ))
          byᵉ apᵉ ((neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ))) +ℤᵉ_) (add-int-ℕᵉ (tᵉ *ℕᵉ yᵉ) dᵉ)
        ＝ᵉ (neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ))) +ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ apᵉ (λ Hᵉ → (neg-ℤᵉ (int-ℕᵉ (tᵉ *ℕᵉ yᵉ))) +ℤᵉ (int-ℕᵉ Hᵉ)) rewrite-distᵉ
        ＝ᵉ (neg-ℤᵉ ((int-ℕᵉ tᵉ) *ℤᵉ (int-ℕᵉ yᵉ))) +ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( λ Hᵉ → (neg-ℤᵉ Hᵉ) +ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
              ( invᵉ (mul-int-ℕᵉ tᵉ yᵉ))
        ＝ᵉ ((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( _+ℤᵉ (int-ℕᵉ (sᵉ *ℕᵉ (succ-ℕᵉ xᵉ))))
              ( invᵉ (left-negative-law-mul-ℤᵉ (int-ℕᵉ tᵉ) (int-ℕᵉ yᵉ)))
        ＝ᵉ ((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( ((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ_)
              ( invᵉ (mul-int-ℕᵉ sᵉ (succ-ℕᵉ xᵉ)))

    isolate-rem-eqnᵉ :
      int-ℕᵉ rᵉ ＝ᵉ
      add-ℤᵉ
        ( neg-ℤᵉ
          ( mul-ℤᵉ
            ( int-ℕᵉ qᵉ)
            ( add-ℤᵉ
              ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
              ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
        ( int-ℕᵉ (succ-ℕᵉ xᵉ))
    isolate-rem-eqnᵉ =
      equational-reasoningᵉ
        int-ℕᵉ rᵉ
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( mul-ℤᵉ
                ( int-ℕᵉ qᵉ)
                ( add-ℤᵉ
                  ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( ((int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( add-ℤᵉ
              ( mul-ℤᵉ
                ( int-ℕᵉ qᵉ)
                ( add-ℤᵉ
                  ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
              ( int-ℕᵉ rᵉ))
          byᵉ invᵉ (is-retraction-left-add-neg-ℤᵉ (mul-ℤᵉ (int-ℕᵉ qᵉ)
            (((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))) (int-ℕᵉ rᵉ))
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( mul-ℤᵉ
                ( int-ℕᵉ qᵉ)
                ( add-ℤᵉ
                  ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ dᵉ)) +ℤᵉ (int-ℕᵉ rᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( mul-ℤᵉ
                      ( int-ℕᵉ qᵉ)
                      ( add-ℤᵉ
                        ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                        ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
                  ( ((int-ℕᵉ qᵉ) *ℤᵉ Hᵉ) +ℤᵉ (int-ℕᵉ rᵉ)))
              ( invᵉ add-dist-eqnᵉ)
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( ( int-ℕᵉ qᵉ) *ℤᵉ
                ( ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
                  ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( add-ℤᵉ
                ( neg-ℤᵉ
                  ( mul-ℤᵉ
                    ( int-ℕᵉ qᵉ)
                    ( add-ℤᵉ
                      ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                      ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))))
              ( minimal-positive-distance-div-succ-x-eqnᵉ xᵉ yᵉ)

    rearrange-arithᵉ :
      add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
        ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))) (int-ℕᵉ (succ-ℕᵉ xᵉ))
      ＝ᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
        (neg-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ
          (int-ℕᵉ (succ-ℕᵉ xᵉ))))
    rearrange-arithᵉ =
      equational-reasoningᵉ
        add-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))) (int-ℕᵉ (succ-ℕᵉ xᵉ))
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( add-ℤᵉ
                ( (int-ℕᵉ qᵉ) *ℤᵉ ((neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)))
                ( (int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ → (neg-ℤᵉ Hᵉ) +ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( left-distributive-mul-add-ℤᵉ
                ( int-ℕᵉ qᵉ)
                ( (neg-ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                ( (int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( add-ℤᵉ
                ( ((int-ℕᵉ qᵉ) *ℤᵉ (neg-ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ))
                ( (int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( Hᵉ +ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ ((int-ℕᵉ sᵉ) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( invᵉ (associative-mul-ℤᵉ (int-ℕᵉ qᵉ) (neg-ℤᵉ (int-ℕᵉ tᵉ)) (int-ℕᵉ yᵉ)))
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( add-ℤᵉ
                ( ((int-ℕᵉ qᵉ) *ℤᵉ (neg-ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ))
                ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( add-ℤᵉ
                      ( ((int-ℕᵉ qᵉ) *ℤᵉ (neg-ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ))
                      ( Hᵉ)))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( invᵉ (associative-mul-ℤᵉ (int-ℕᵉ qᵉ) (int-ℕᵉ sᵉ) (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ add-ℤᵉ
            ( neg-ℤᵉ
              ( add-ℤᵉ
                ( (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ))
                ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( neg-ℤᵉ
                    ( add-ℤᵉ
                      ( Hᵉ *ℤᵉ (int-ℕᵉ yᵉ))
                      ( mul-ℤᵉ
                        ( (int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))
                        ( int-ℕᵉ (succ-ℕᵉ xᵉ)))))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( right-negative-law-mul-ℤᵉ (int-ℕᵉ qᵉ) (int-ℕᵉ tᵉ))
        ＝ᵉ add-ℤᵉ
            ( add-ℤᵉ
              ( neg-ℤᵉ ((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ)))
              ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ apᵉ (_+ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (distributive-neg-add-ℤᵉ
              ((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ))) *ℤᵉ (int-ℕᵉ yᵉ))
              (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ
              (int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ add-ℤᵉ
            ( add-ℤᵉ
              ( (neg-ℤᵉ (neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)))) *ℤᵉ (int-ℕᵉ yᵉ))
              ( neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            ( int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
            ( λ Hᵉ →
              add-ℤᵉ
                ( add-ℤᵉ
                  ( Hᵉ)
                  ( neg-ℤᵉ
                    ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
                ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
            ( invᵉ
              ( left-negative-law-mul-ℤᵉ
                ( neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)))
                ( int-ℕᵉ yᵉ)))
        ＝ᵉ add-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ apᵉ (λ Hᵉ → (add-ℤᵉ ((Hᵉ *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
              (int-ℕᵉ (succ-ℕᵉ xᵉ))))
            (neg-neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)))
        ＝ᵉ add-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            ((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
          (int-ℕᵉ (succ-ℕᵉ xᵉ))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ Hᵉ)
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
              ( invᵉ
                ( left-negative-law-mul-ℤᵉ
                  ( (int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ associative-add-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
            ((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))
            (int-ℕᵉ (succ-ℕᵉ xᵉ))
        ＝ᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (((neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ))) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))) +ℤᵉ
            ((neg-ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                add-ℤᵉ
                  ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
                  ( add-ℤᵉ
                    ( mul-ℤᵉ
                      ( neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)))
                      ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
                    ( Hᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
              ( invᵉ (neg-neg-ℤᵉ one-ℤᵉ))
        ＝ᵉ add-ℤᵉ
            ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
            ( mul-ℤᵉ
              ( add-ℤᵉ
                ( neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)))
                ( neg-ℤᵉ (neg-ℤᵉ one-ℤᵉ)))
              ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ_)
              ( invᵉ
                ( right-distributive-mul-add-ℤᵉ
                  ( neg-ℤᵉ ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)))
                  ( neg-ℤᵉ (neg-ℤᵉ one-ℤᵉ))
                  ( int-ℕᵉ (succ-ℕᵉ xᵉ))))
        ＝ᵉ add-ℤᵉ
            ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
            ( mul-ℤᵉ (neg-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ
            (neg-ℤᵉ one-ℤᵉ))) (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ apᵉ (λ Hᵉ → ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
              (Hᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
              (invᵉ (distributive-neg-add-ℤᵉ
                ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) (neg-ℤᵉ one-ℤᵉ)))
        ＝ᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
          (neg-ℤᵉ (mul-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ
            (neg-ℤᵉ one-ℤᵉ)) (int-ℕᵉ (succ-ℕᵉ xᵉ))))
          byᵉ apᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ_)
            (left-negative-law-mul-ℤᵉ
              (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))
              (int-ℕᵉ (succ-ℕᵉ xᵉ)))

    dist-eqnᵉ :
      rᵉ ＝ᵉ
      dist-ℕᵉ
        ( mul-ℕᵉ
          ( abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)))
          ( succ-ℕᵉ xᵉ))
        ( (qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
    dist-eqnᵉ =
      equational-reasoningᵉ
        rᵉ
        ＝ᵉ abs-ℤᵉ (int-ℕᵉ rᵉ) byᵉ (invᵉ (abs-int-ℕᵉ rᵉ))
        ＝ᵉ abs-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ)) +ℤᵉ
            (neg-ℤᵉ ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
          byᵉ (apᵉ abs-ℤᵉ (isolate-rem-eqnᵉ ∙ᵉ rearrange-arithᵉ))
        ＝ᵉ dist-ℤᵉ ((int-ℕᵉ (qᵉ *ℕᵉ tᵉ)) *ℤᵉ (int-ℕᵉ yᵉ))
          ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ
            (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ apᵉ (λ Hᵉ → (dist-ℤᵉ (Hᵉ *ℤᵉ (int-ℕᵉ yᵉ))
            ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ
              (int-ℕᵉ (succ-ℕᵉ xᵉ)))))
              (mul-int-ℕᵉ qᵉ tᵉ)
        ＝ᵉ dist-ℤᵉ (int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ))
          ((((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)) *ℤᵉ
          (int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                dist-ℤᵉ Hᵉ
                  ( mul-ℤᵉ
                    ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))
                    ( int-ℕᵉ (succ-ℕᵉ xᵉ))))
              ( mul-int-ℕᵉ (qᵉ *ℕᵉ tᵉ) yᵉ)
        ＝ᵉ dist-ℤᵉ
            ( int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ))
            ( mul-ℤᵉ
              ( int-ℕᵉ (abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))))
              ( int-ℕᵉ (succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( λ Hᵉ →
                dist-ℤᵉ
                  ( int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ))
                  ( Hᵉ *ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))))
              ( invᵉ
                ( int-abs-is-nonnegative-ℤᵉ
                  ( ((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))
                  ( coeff-nonnegativeᵉ)))
        ＝ᵉ dist-ℤᵉ
            ( int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ))
            ( int-ℕᵉ
              ( mul-ℕᵉ
                ( abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)))
                ( succ-ℕᵉ xᵉ)))
          byᵉ
            apᵉ
              ( dist-ℤᵉ (int-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)))
              ( mul-int-ℕᵉ
                ( abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ)))
                ( succ-ℕᵉ xᵉ))
        ＝ᵉ dist-ℕᵉ ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
          ((abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))) *ℕᵉ
            (succ-ℕᵉ xᵉ))
          byᵉ dist-int-ℕᵉ
            ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
            ((abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))) *ℕᵉ
              (succ-ℕᵉ xᵉ))
        ＝ᵉ dist-ℕᵉ
          ((abs-ℤᵉ (((int-ℕᵉ qᵉ) *ℤᵉ (int-ℕᵉ sᵉ)) +ℤᵉ (neg-ℤᵉ one-ℤᵉ))) *ℕᵉ
            (succ-ℕᵉ xᵉ))
            ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
          byᵉ symmetric-dist-ℕᵉ
            ((qᵉ *ℕᵉ tᵉ) *ℕᵉ yᵉ)
            (mul-ℕᵉ (abs-ℤᵉ (add-ℤᵉ (mul-ℤᵉ (int-ℕᵉ qᵉ)
              (int-ℕᵉ sᵉ)) (neg-ℤᵉ one-ℤᵉ)))
            (succ-ℕᵉ xᵉ))

remainder-min-dist-succ-x-is-not-nonzeroᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  ¬ᵉ ( is-nonzero-ℕᵉ
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ)))
remainder-min-dist-succ-x-is-not-nonzeroᵉ xᵉ yᵉ nonzeroᵉ =
  contradiction-le-ℕᵉ
    ( remainder-euclidean-division-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( succ-ℕᵉ xᵉ))
    ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
    ( remainder-min-dist-succ-x-le-min-distᵉ xᵉ yᵉ) d-leq-remᵉ
  where
  rem-pos-distᵉ :
    pos-distance-between-multiplesᵉ
      ( succ-ℕᵉ xᵉ)
      ( yᵉ)
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ))
  rem-pos-distᵉ Hᵉ = pair'ᵉ nonzeroᵉ (remainder-min-dist-succ-x-is-distanceᵉ xᵉ yᵉ)

  d-leq-remᵉ :
    leq-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ))
  d-leq-remᵉ =
    minimal-positive-distance-is-minimalᵉ
      ( succ-ℕᵉ xᵉ)
      ( yᵉ)
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ))
      ( rem-pos-distᵉ)

remainder-min-dist-succ-x-is-zeroᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  is-zero-ℕᵉ
    ( remainder-euclidean-division-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( succ-ℕᵉ xᵉ))
remainder-min-dist-succ-x-is-zeroᵉ xᵉ yᵉ =
  is-zero-case-splitᵉ
    ( is-decidable-is-zero-ℕᵉ
      ( remainder-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ)))
  where
  is-zero-case-splitᵉ :
    ( is-zero-ℕᵉ
      ( remainder-euclidean-division-ℕᵉ
        (minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ) (succ-ℕᵉ xᵉ)) +ᵉ
      is-nonzero-ℕᵉ
      ( remainder-euclidean-division-ℕᵉ
        (minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ) (succ-ℕᵉ xᵉ))) →
      is-zero-ℕᵉ
        ( remainder-euclidean-division-ℕᵉ
          (minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ) (succ-ℕᵉ xᵉ))
  is-zero-case-splitᵉ (inlᵉ zᵉ) = zᵉ
  is-zero-case-splitᵉ (inrᵉ nzᵉ) =
    ex-falsoᵉ (remainder-min-dist-succ-x-is-not-nonzeroᵉ xᵉ yᵉ nzᵉ)

minimal-positive-distance-div-fstᵉ :
  (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ (minimal-positive-distanceᵉ xᵉ yᵉ) xᵉ
minimal-positive-distance-div-fstᵉ zero-ℕᵉ yᵉ =
  pairᵉ zero-ℕᵉ (left-zero-law-mul-ℕᵉ (minimal-positive-distanceᵉ zero-ℕᵉ yᵉ))
minimal-positive-distance-div-fstᵉ (succ-ℕᵉ xᵉ) yᵉ =
  pairᵉ
    ( quotient-euclidean-division-ℕᵉ
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ( succ-ℕᵉ xᵉ))
    ( eqnᵉ)
  where
  eqnᵉ :
    ( mul-ℕᵉ
      ( quotient-euclidean-division-ℕᵉ
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
        ( succ-ℕᵉ xᵉ))
      ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)) ＝ᵉ
    ( succ-ℕᵉ xᵉ)
  eqnᵉ =
    equational-reasoningᵉ
      mul-ℕᵉ
        ( quotient-euclidean-division-ℕᵉ
          ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
          ( succ-ℕᵉ xᵉ))
        ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
      ＝ᵉ add-ℕᵉ
          ( mul-ℕᵉ
            ( quotient-euclidean-division-ℕᵉ
              ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
              ( succ-ℕᵉ xᵉ))
            ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ))
          ( zero-ℕᵉ)
        byᵉ
          ( invᵉ
            ( right-unit-law-add-ℕᵉ
              ( ( quotient-euclidean-division-ℕᵉ
                  ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                  ( succ-ℕᵉ xᵉ)) *ℕᵉ
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ))))
      ＝ᵉ add-ℕᵉ
        ( ( quotient-euclidean-division-ℕᵉ
            ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
            ( succ-ℕᵉ xᵉ)) *ℕᵉ
          ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ))
        ( remainder-euclidean-division-ℕᵉ
          ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
          ( succ-ℕᵉ xᵉ))
        byᵉ
          ( apᵉ
            ( add-ℕᵉ
              ( mul-ℕᵉ
                ( quotient-euclidean-division-ℕᵉ
                  ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
                  ( succ-ℕᵉ xᵉ))
                ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)))
            ( invᵉ (remainder-min-dist-succ-x-is-zeroᵉ xᵉ yᵉ)))
      ＝ᵉ succ-ℕᵉ xᵉ
        byᵉ
          eq-euclidean-division-ℕᵉ
            ( minimal-positive-distanceᵉ (succ-ℕᵉ xᵉ) yᵉ)
            ( succ-ℕᵉ xᵉ)

minimal-positive-distance-div-sndᵉ :
  (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ (minimal-positive-distanceᵉ xᵉ yᵉ) yᵉ
minimal-positive-distance-div-sndᵉ xᵉ yᵉ =
  concatenate-eq-div-ℕᵉ
    ( minimal-positive-distance-symᵉ xᵉ yᵉ)
    ( minimal-positive-distance-div-fstᵉ yᵉ xᵉ)

minimal-positive-distance-div-gcd-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ (minimal-positive-distanceᵉ xᵉ yᵉ) (gcd-ℕᵉ xᵉ yᵉ)
minimal-positive-distance-div-gcd-ℕᵉ xᵉ yᵉ =
  div-gcd-is-common-divisor-ℕᵉ
    ( xᵉ)
    ( yᵉ)
    ( minimal-positive-distanceᵉ xᵉ yᵉ)
    ( pair'ᵉ
      ( minimal-positive-distance-div-fstᵉ xᵉ yᵉ)
      ( minimal-positive-distance-div-sndᵉ xᵉ yᵉ))

gcd-ℕ-div-x-multsᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ)
  (dᵉ : is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ) →
  div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) ((is-distance-between-multiples-fst-coeff-ℕᵉ dᵉ) *ℕᵉ xᵉ)
gcd-ℕ-div-x-multsᵉ xᵉ yᵉ zᵉ dᵉ =
  div-mul-ℕᵉ
    ( is-distance-between-multiples-fst-coeff-ℕᵉ dᵉ)
    ( gcd-ℕᵉ xᵉ yᵉ)
    ( xᵉ)
    ( pr1ᵉ (is-common-divisor-gcd-ℕᵉ xᵉ yᵉ))

gcd-ℕ-div-y-multsᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ)
  (dᵉ : is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ) →
  div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) ((is-distance-between-multiples-snd-coeff-ℕᵉ dᵉ) *ℕᵉ yᵉ)
gcd-ℕ-div-y-multsᵉ xᵉ yᵉ zᵉ dᵉ =
  div-mul-ℕᵉ
    ( is-distance-between-multiples-snd-coeff-ℕᵉ dᵉ)
    ( gcd-ℕᵉ xᵉ yᵉ)
    ( yᵉ)
    ( pr2ᵉ (is-common-divisor-gcd-ℕᵉ xᵉ yᵉ))

gcd-ℕ-div-dist-between-multᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → is-distance-between-multiples-ℕᵉ xᵉ yᵉ zᵉ → div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) zᵉ
gcd-ℕ-div-dist-between-multᵉ xᵉ yᵉ zᵉ distᵉ =
  sx-ty-case-splitᵉ (linear-leq-ℕᵉ (sᵉ *ℕᵉ xᵉ) (tᵉ *ℕᵉ yᵉ))
  where
  sᵉ : ℕᵉ
  sᵉ = is-distance-between-multiples-fst-coeff-ℕᵉ distᵉ
  tᵉ : ℕᵉ
  tᵉ = is-distance-between-multiples-snd-coeff-ℕᵉ distᵉ

  sx-ty-case-splitᵉ :
    (leq-ℕᵉ (sᵉ *ℕᵉ xᵉ) (tᵉ *ℕᵉ yᵉ) +ᵉ leq-ℕᵉ (tᵉ *ℕᵉ yᵉ) (sᵉ *ℕᵉ xᵉ)) →
    div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) zᵉ
  sx-ty-case-splitᵉ (inlᵉ sxtyᵉ) =
    div-right-summand-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) (sᵉ *ℕᵉ xᵉ) zᵉ
      (gcd-ℕ-div-x-multsᵉ xᵉ yᵉ zᵉ distᵉ)
      (concatenate-div-eq-ℕᵉ (gcd-ℕ-div-y-multsᵉ xᵉ yᵉ zᵉ distᵉ)
        (invᵉ rewrite-distᵉ))
    where
    rewrite-distᵉ : (sᵉ *ℕᵉ xᵉ) +ℕᵉ zᵉ ＝ᵉ tᵉ *ℕᵉ yᵉ
    rewrite-distᵉ = rewrite-right-dist-add-ℕᵉ
      (sᵉ *ℕᵉ xᵉ) zᵉ (tᵉ *ℕᵉ yᵉ) sxtyᵉ
      (invᵉ (is-distance-between-multiples-eqn-ℕᵉ distᵉ))

  sx-ty-case-splitᵉ (inrᵉ tysxᵉ) =
    div-right-summand-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) (tᵉ *ℕᵉ yᵉ) zᵉ
      (gcd-ℕ-div-y-multsᵉ xᵉ yᵉ zᵉ distᵉ)
      (concatenate-div-eq-ℕᵉ (gcd-ℕ-div-x-multsᵉ xᵉ yᵉ zᵉ distᵉ) (invᵉ rewrite-distᵉ))
    where
    rewrite-distᵉ : (tᵉ *ℕᵉ yᵉ) +ℕᵉ zᵉ ＝ᵉ sᵉ *ℕᵉ xᵉ
    rewrite-distᵉ =
      rewrite-right-dist-add-ℕᵉ (tᵉ *ℕᵉ yᵉ) zᵉ (sᵉ *ℕᵉ xᵉ) tysxᵉ
        ( invᵉ (is-distance-between-multiples-eqn-ℕᵉ distᵉ) ∙ᵉ
          symmetric-dist-ℕᵉ (sᵉ *ℕᵉ xᵉ) (tᵉ *ℕᵉ yᵉ))

    div-gcd-xᵉ : div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) (sᵉ *ℕᵉ xᵉ)
    div-gcd-xᵉ = div-mul-ℕᵉ sᵉ (gcd-ℕᵉ xᵉ yᵉ) xᵉ (pr1ᵉ (is-common-divisor-gcd-ℕᵉ xᵉ yᵉ))

gcd-ℕ-div-minimal-positive-distanceᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ) →
  div-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) (minimal-positive-distanceᵉ xᵉ yᵉ)
gcd-ℕ-div-minimal-positive-distanceᵉ xᵉ yᵉ Hᵉ =
  gcd-ℕ-div-dist-between-multᵉ
    ( xᵉ)
    ( yᵉ)
    ( minimal-positive-distanceᵉ xᵉ yᵉ)
    ( minimal-positive-distance-is-distanceᵉ xᵉ yᵉ Hᵉ)

bezouts-lemma-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ) →
  minimal-positive-distanceᵉ xᵉ yᵉ ＝ᵉ gcd-ℕᵉ xᵉ yᵉ
bezouts-lemma-ℕᵉ xᵉ yᵉ Hᵉ =
  antisymmetric-div-ℕᵉ
    ( minimal-positive-distanceᵉ xᵉ yᵉ)
    ( gcd-ℕᵉ xᵉ yᵉ)
    ( minimal-positive-distance-div-gcd-ℕᵉ xᵉ yᵉ)
    ( gcd-ℕ-div-minimal-positive-distanceᵉ xᵉ yᵉ Hᵉ)

bezouts-lemma-eqn-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ)
  (Hᵉ : is-nonzero-ℕᵉ (xᵉ +ℕᵉ yᵉ)) →
  dist-ℕᵉ
    ( (minimal-positive-distance-x-coeffᵉ xᵉ yᵉ Hᵉ) *ℕᵉ xᵉ)
    ( (minimal-positive-distance-y-coeffᵉ xᵉ yᵉ Hᵉ) *ℕᵉ yᵉ) ＝ᵉ
  gcd-ℕᵉ xᵉ yᵉ
bezouts-lemma-eqn-ℕᵉ xᵉ yᵉ Hᵉ =
  minimal-positive-distance-eqnᵉ xᵉ yᵉ Hᵉ ∙ᵉ bezouts-lemma-ℕᵉ xᵉ yᵉ Hᵉ
```