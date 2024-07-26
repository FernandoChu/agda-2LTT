# Multiplication of natural numbers

```agda
module elementary-number-theory.multiplication-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.negated-equalityᵉ
open import foundation.setsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "multiplication"ᵉ Disambiguation="naturalᵉ numbers"ᵉ Agda=mul-ℕᵉ}}
operationᵉ onᵉ theᵉ [naturalᵉ numbers](elementary-number-theory.natural-numbers.mdᵉ)
isᵉ definedᵉ byᵉ [iteratively](foundation.iterating-functions.mdᵉ) applyingᵉ
[addition](elementary-number-theory.addition-natural-numbers.mdᵉ) ofᵉ aᵉ numberᵉ to
itself.ᵉ Moreᵉ precieslyᵉ theᵉ numberᵉ `mᵉ *ᵉ n`ᵉ isᵉ definedᵉ byᵉ addingᵉ theᵉ numberᵉ `n`ᵉ to
itselfᵉ `m`ᵉ timesᵉ:

```text
  mᵉ *ᵉ nᵉ = nᵉ +ᵉ ⋯ᵉ +ᵉ nᵉ    (nᵉ addedᵉ to itselfᵉ mᵉ times).ᵉ
```

## Definition

### Multiplication

```agda
mul-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
mul-ℕᵉ 0 nᵉ = 0
mul-ℕᵉ (succ-ℕᵉ mᵉ) nᵉ = (mul-ℕᵉ mᵉ nᵉ) +ℕᵉ nᵉ

infixl 40 _*ℕᵉ_
_*ℕᵉ_ = mul-ℕᵉ

mul-ℕ'ᵉ : ℕᵉ → ℕᵉ → ℕᵉ
mul-ℕ'ᵉ xᵉ yᵉ = mul-ℕᵉ yᵉ xᵉ

ap-mul-ℕᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℕᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ *ℕᵉ yᵉ ＝ᵉ x'ᵉ *ℕᵉ y'ᵉ
ap-mul-ℕᵉ pᵉ qᵉ = ap-binaryᵉ mul-ℕᵉ pᵉ qᵉ

double-ℕᵉ : ℕᵉ → ℕᵉ
double-ℕᵉ xᵉ = 2 *ℕᵉ xᵉ

triple-ℕᵉ : ℕᵉ → ℕᵉ
triple-ℕᵉ xᵉ = 3 *ℕᵉ xᵉ
```

## Properties

```agda
abstract
  left-zero-law-mul-ℕᵉ :
    (xᵉ : ℕᵉ) → zero-ℕᵉ *ℕᵉ xᵉ ＝ᵉ zero-ℕᵉ
  left-zero-law-mul-ℕᵉ xᵉ = reflᵉ

  right-zero-law-mul-ℕᵉ :
    (xᵉ : ℕᵉ) → xᵉ *ℕᵉ zero-ℕᵉ ＝ᵉ zero-ℕᵉ
  right-zero-law-mul-ℕᵉ zero-ℕᵉ = reflᵉ
  right-zero-law-mul-ℕᵉ (succ-ℕᵉ xᵉ) =
    ( right-unit-law-add-ℕᵉ (xᵉ *ℕᵉ zero-ℕᵉ)) ∙ᵉ (right-zero-law-mul-ℕᵉ xᵉ)

abstract
  right-unit-law-mul-ℕᵉ :
    (xᵉ : ℕᵉ) → xᵉ *ℕᵉ 1 ＝ᵉ xᵉ
  right-unit-law-mul-ℕᵉ zero-ℕᵉ = reflᵉ
  right-unit-law-mul-ℕᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (right-unit-law-mul-ℕᵉ xᵉ)

  left-unit-law-mul-ℕᵉ :
    (xᵉ : ℕᵉ) → 1 *ℕᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-ℕᵉ zero-ℕᵉ = reflᵉ
  left-unit-law-mul-ℕᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (left-unit-law-mul-ℕᵉ xᵉ)

abstract
  left-successor-law-mul-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → (succ-ℕᵉ xᵉ) *ℕᵉ yᵉ ＝ᵉ (xᵉ *ℕᵉ yᵉ) +ℕᵉ yᵉ
  left-successor-law-mul-ℕᵉ xᵉ yᵉ = reflᵉ

  right-successor-law-mul-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → xᵉ *ℕᵉ (succ-ℕᵉ yᵉ) ＝ᵉ xᵉ +ℕᵉ (xᵉ *ℕᵉ yᵉ)
  right-successor-law-mul-ℕᵉ zero-ℕᵉ yᵉ = reflᵉ
  right-successor-law-mul-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ =
    ( ( apᵉ (λ tᵉ → succ-ℕᵉ (tᵉ +ℕᵉ yᵉ)) (right-successor-law-mul-ℕᵉ xᵉ yᵉ)) ∙ᵉ
      ( apᵉ succ-ℕᵉ (associative-add-ℕᵉ xᵉ (xᵉ *ℕᵉ yᵉ) yᵉ))) ∙ᵉ
    ( invᵉ (left-successor-law-add-ℕᵉ xᵉ ((xᵉ *ℕᵉ yᵉ) +ℕᵉ yᵉ)))

abstract
  commutative-mul-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → xᵉ *ℕᵉ yᵉ ＝ᵉ yᵉ *ℕᵉ xᵉ
  commutative-mul-ℕᵉ zero-ℕᵉ yᵉ = invᵉ (right-zero-law-mul-ℕᵉ yᵉ)
  commutative-mul-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ =
    ( commutative-add-ℕᵉ (xᵉ *ℕᵉ yᵉ) yᵉ) ∙ᵉ
    ( ( apᵉ (yᵉ +ℕᵉ_) (commutative-mul-ℕᵉ xᵉ yᵉ)) ∙ᵉ
      ( invᵉ (right-successor-law-mul-ℕᵉ yᵉ xᵉ)))

abstract
  left-distributive-mul-add-ℕᵉ :
    (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ *ℕᵉ (yᵉ +ℕᵉ zᵉ) ＝ᵉ (xᵉ *ℕᵉ yᵉ) +ℕᵉ (xᵉ *ℕᵉ zᵉ)
  left-distributive-mul-add-ℕᵉ zero-ℕᵉ yᵉ zᵉ = reflᵉ
  left-distributive-mul-add-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ =
    ( left-successor-law-mul-ℕᵉ xᵉ (yᵉ +ℕᵉ zᵉ)) ∙ᵉ
    ( ( apᵉ (_+ℕᵉ (yᵉ +ℕᵉ zᵉ)) (left-distributive-mul-add-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
      ( ( associative-add-ℕᵉ (xᵉ *ℕᵉ yᵉ) (xᵉ *ℕᵉ zᵉ) (yᵉ +ℕᵉ zᵉ)) ∙ᵉ
        ( ( apᵉ
            ( ( xᵉ *ℕᵉ yᵉ) +ℕᵉ_)
            ( ( invᵉ (associative-add-ℕᵉ (xᵉ *ℕᵉ zᵉ) yᵉ zᵉ)) ∙ᵉ
              ( ( apᵉ (_+ℕᵉ zᵉ) (commutative-add-ℕᵉ (xᵉ *ℕᵉ zᵉ) yᵉ)) ∙ᵉ
                ( associative-add-ℕᵉ yᵉ (xᵉ *ℕᵉ zᵉ) zᵉ)))) ∙ᵉ
          ( invᵉ (associative-add-ℕᵉ (xᵉ *ℕᵉ yᵉ) yᵉ ((xᵉ *ℕᵉ zᵉ) +ℕᵉ zᵉ))))))

abstract
  right-distributive-mul-add-ℕᵉ :
    (xᵉ yᵉ zᵉ : ℕᵉ) → (xᵉ +ℕᵉ yᵉ) *ℕᵉ zᵉ ＝ᵉ (xᵉ *ℕᵉ zᵉ) +ℕᵉ (yᵉ *ℕᵉ zᵉ)
  right-distributive-mul-add-ℕᵉ xᵉ yᵉ zᵉ =
    ( commutative-mul-ℕᵉ (xᵉ +ℕᵉ yᵉ) zᵉ) ∙ᵉ
    ( ( left-distributive-mul-add-ℕᵉ zᵉ xᵉ yᵉ) ∙ᵉ
      ( ( apᵉ (_+ℕᵉ (zᵉ *ℕᵉ yᵉ)) (commutative-mul-ℕᵉ zᵉ xᵉ)) ∙ᵉ
        ( apᵉ ((xᵉ *ℕᵉ zᵉ) +ℕᵉ_) (commutative-mul-ℕᵉ zᵉ yᵉ))))

abstract
  associative-mul-ℕᵉ :
    (xᵉ yᵉ zᵉ : ℕᵉ) → (xᵉ *ℕᵉ yᵉ) *ℕᵉ zᵉ ＝ᵉ xᵉ *ℕᵉ (yᵉ *ℕᵉ zᵉ)
  associative-mul-ℕᵉ zero-ℕᵉ yᵉ zᵉ = reflᵉ
  associative-mul-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ zᵉ =
    ( right-distributive-mul-add-ℕᵉ (xᵉ *ℕᵉ yᵉ) yᵉ zᵉ) ∙ᵉ
    ( apᵉ (_+ℕᵉ (yᵉ *ℕᵉ zᵉ)) (associative-mul-ℕᵉ xᵉ yᵉ zᵉ))

left-two-law-mul-ℕᵉ :
  (xᵉ : ℕᵉ) → 2 *ℕᵉ xᵉ ＝ᵉ xᵉ +ℕᵉ xᵉ
left-two-law-mul-ℕᵉ xᵉ =
  ( left-successor-law-mul-ℕᵉ 1 xᵉ) ∙ᵉ
  ( apᵉ (_+ℕᵉ xᵉ) (left-unit-law-mul-ℕᵉ xᵉ))

right-two-law-mul-ℕᵉ :
  (xᵉ : ℕᵉ) → xᵉ *ℕᵉ 2 ＝ᵉ xᵉ +ℕᵉ xᵉ
right-two-law-mul-ℕᵉ xᵉ =
  ( right-successor-law-mul-ℕᵉ xᵉ 1ᵉ) ∙ᵉ
  ( apᵉ (xᵉ +ℕᵉ_) (right-unit-law-mul-ℕᵉ xᵉ))

interchange-law-mul-mul-ℕᵉ : interchange-lawᵉ mul-ℕᵉ mul-ℕᵉ
interchange-law-mul-mul-ℕᵉ =
  interchange-law-commutative-and-associativeᵉ
    mul-ℕᵉ
    commutative-mul-ℕᵉ
    associative-mul-ℕᵉ

is-injective-right-mul-succ-ℕᵉ :
  (kᵉ : ℕᵉ) → is-injectiveᵉ (_*ℕᵉ (succ-ℕᵉ kᵉ))
is-injective-right-mul-succ-ℕᵉ kᵉ {zero-ℕᵉ} {zero-ℕᵉ} pᵉ = reflᵉ
is-injective-right-mul-succ-ℕᵉ kᵉ {succ-ℕᵉ mᵉ} {succ-ℕᵉ nᵉ} pᵉ =
  apᵉ succ-ℕᵉ
    ( is-injective-right-mul-succ-ℕᵉ kᵉ {mᵉ} {nᵉ}
      ( is-injective-right-add-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        ( ( invᵉ (left-successor-law-mul-ℕᵉ mᵉ (succ-ℕᵉ kᵉ))) ∙ᵉ
          ( ( pᵉ) ∙ᵉ
            ( left-successor-law-mul-ℕᵉ nᵉ (succ-ℕᵉ kᵉ))))))

is-injective-right-mul-ℕᵉ : (kᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → is-injectiveᵉ (_*ℕᵉ kᵉ)
is-injective-right-mul-ℕᵉ kᵉ Hᵉ pᵉ with
  is-successor-is-nonzero-ℕᵉ Hᵉ
... | pairᵉ lᵉ reflᵉ = is-injective-right-mul-succ-ℕᵉ lᵉ pᵉ

is-injective-left-mul-succ-ℕᵉ :
  (kᵉ : ℕᵉ) → is-injectiveᵉ ((succ-ℕᵉ kᵉ) *ℕᵉ_)
is-injective-left-mul-succ-ℕᵉ kᵉ {mᵉ} {nᵉ} pᵉ =
  is-injective-right-mul-succ-ℕᵉ kᵉ
    ( ( commutative-mul-ℕᵉ mᵉ (succ-ℕᵉ kᵉ)) ∙ᵉ
      ( pᵉ ∙ᵉ commutative-mul-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))

is-injective-left-mul-ℕᵉ :
  (kᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → is-injectiveᵉ (kᵉ *ℕᵉ_)
is-injective-left-mul-ℕᵉ kᵉ Hᵉ pᵉ with
  is-successor-is-nonzero-ℕᵉ Hᵉ
... | pairᵉ lᵉ reflᵉ = is-injective-left-mul-succ-ℕᵉ lᵉ pᵉ

is-emb-left-mul-ℕᵉ : (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → is-embᵉ (xᵉ *ℕᵉ_)
is-emb-left-mul-ℕᵉ xᵉ Hᵉ =
  is-emb-is-injectiveᵉ is-set-ℕᵉ (is-injective-left-mul-ℕᵉ xᵉ Hᵉ)

is-emb-right-mul-ℕᵉ : (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → is-embᵉ (_*ℕᵉ xᵉ)
is-emb-right-mul-ℕᵉ xᵉ Hᵉ =
  is-emb-is-injectiveᵉ is-set-ℕᵉ (is-injective-right-mul-ℕᵉ xᵉ Hᵉ)

is-nonzero-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → is-nonzero-ℕᵉ yᵉ → is-nonzero-ℕᵉ (xᵉ *ℕᵉ yᵉ)
is-nonzero-mul-ℕᵉ xᵉ yᵉ Hᵉ Kᵉ pᵉ =
  Kᵉ (is-injective-left-mul-ℕᵉ xᵉ Hᵉ (pᵉ ∙ᵉ (invᵉ (right-zero-law-mul-ℕᵉ xᵉ))))

is-nonzero-left-factor-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ (xᵉ *ℕᵉ yᵉ) → is-nonzero-ℕᵉ xᵉ
is-nonzero-left-factor-mul-ℕᵉ .zero-ℕᵉ yᵉ Hᵉ reflᵉ = Hᵉ (left-zero-law-mul-ℕᵉ yᵉ)

is-nonzero-right-factor-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ (xᵉ *ℕᵉ yᵉ) → is-nonzero-ℕᵉ yᵉ
is-nonzero-right-factor-mul-ℕᵉ xᵉ .zero-ℕᵉ Hᵉ reflᵉ = Hᵉ (right-zero-law-mul-ℕᵉ xᵉ)
```

Weᵉ concludeᵉ thatᵉ $yᵉ = 1$ᵉ ifᵉ $(x+1)yᵉ = x+1$.ᵉ

```agda
is-one-is-right-unit-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → (succ-ℕᵉ xᵉ) *ℕᵉ yᵉ ＝ᵉ succ-ℕᵉ xᵉ → is-one-ℕᵉ yᵉ
is-one-is-right-unit-mul-ℕᵉ xᵉ yᵉ pᵉ =
  is-injective-left-mul-succ-ℕᵉ xᵉ (pᵉ ∙ᵉ invᵉ (right-unit-law-mul-ℕᵉ (succ-ℕᵉ xᵉ)))

is-one-is-left-unit-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ *ℕᵉ (succ-ℕᵉ yᵉ) ＝ᵉ succ-ℕᵉ yᵉ → is-one-ℕᵉ xᵉ
is-one-is-left-unit-mul-ℕᵉ xᵉ yᵉ pᵉ =
  is-injective-right-mul-succ-ℕᵉ yᵉ (pᵉ ∙ᵉ invᵉ (left-unit-law-mul-ℕᵉ (succ-ℕᵉ yᵉ)))

is-one-right-is-one-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-one-ℕᵉ (xᵉ *ℕᵉ yᵉ) → is-one-ℕᵉ yᵉ
is-one-right-is-one-mul-ℕᵉ zero-ℕᵉ zero-ℕᵉ pᵉ = pᵉ
is-one-right-is-one-mul-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) ()
is-one-right-is-one-mul-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ pᵉ =
  is-one-right-is-one-mul-ℕᵉ xᵉ zero-ℕᵉ pᵉ
is-one-right-is-one-mul-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) pᵉ =
  apᵉ
    ( succ-ℕᵉ)
    ( is-zero-right-is-zero-add-ℕᵉ (xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) yᵉ
      ( is-injective-succ-ℕᵉ pᵉ))

is-one-left-is-one-mul-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-one-ℕᵉ (xᵉ *ℕᵉ yᵉ) → is-one-ℕᵉ xᵉ
is-one-left-is-one-mul-ℕᵉ xᵉ yᵉ pᵉ =
  is-one-right-is-one-mul-ℕᵉ yᵉ xᵉ (commutative-mul-ℕᵉ yᵉ xᵉ ∙ᵉ pᵉ)

neq-mul-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → succ-ℕᵉ mᵉ ≠ᵉ (succ-ℕᵉ mᵉ *ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
neq-mul-ℕᵉ mᵉ nᵉ pᵉ =
  neq-add-ℕᵉ
    ( succ-ℕᵉ mᵉ)
    ( ( mᵉ *ℕᵉ (succ-ℕᵉ nᵉ)) +ℕᵉ nᵉ)
    ( ( pᵉ) ∙ᵉ
      ( ( right-successor-law-mul-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ)) ∙ᵉ
        ( apᵉ ((succ-ℕᵉ mᵉ) +ℕᵉ_) (left-successor-law-mul-ℕᵉ mᵉ (succ-ℕᵉ nᵉ)))))
```

## See also

-ᵉ [Squaresᵉ ofᵉ naturalᵉ numbers](elementary-number-theory.squares-natural-numbers.mdᵉ)
-ᵉ [Cubesᵉ ofᵉ naturalᵉ numbers](elementary-number-theory.cubes-natural-numbers.mdᵉ)