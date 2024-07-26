# Addition on the rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.addition-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
```

</details>

## Idea

Weᵉ introduceᵉ
{{#conceptᵉ "addition"ᵉ Disambiguation="rationalᵉ numbers"ᵉ Agda=add-ℚᵉ}} onᵉ theᵉ
[rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) andᵉ deriveᵉ itsᵉ
basicᵉ properties.ᵉ

## Definition

```agda
add-ℚᵉ : ℚᵉ → ℚᵉ → ℚᵉ
add-ℚᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) = rational-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ yᵉ)

add-ℚ'ᵉ : ℚᵉ → ℚᵉ → ℚᵉ
add-ℚ'ᵉ xᵉ yᵉ = add-ℚᵉ yᵉ xᵉ

infixl 35 _+ℚᵉ_
_+ℚᵉ_ = add-ℚᵉ

ap-add-ℚᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℚᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ +ℚᵉ yᵉ ＝ᵉ x'ᵉ +ℚᵉ y'ᵉ
ap-add-ℚᵉ pᵉ qᵉ = ap-binaryᵉ add-ℚᵉ pᵉ qᵉ
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℚᵉ : (xᵉ : ℚᵉ) → zero-ℚᵉ +ℚᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-ℚᵉ (xᵉ ,ᵉ pᵉ) =
    eq-ℚ-sim-fraction-ℤᵉ
      ( add-fraction-ℤᵉ zero-fraction-ℤᵉ xᵉ)
      ( xᵉ)
      ( left-unit-law-add-fraction-ℤᵉ xᵉ) ∙ᵉ
    is-retraction-rational-fraction-ℚᵉ (xᵉ ,ᵉ pᵉ)

  right-unit-law-add-ℚᵉ : (xᵉ : ℚᵉ) → xᵉ +ℚᵉ zero-ℚᵉ ＝ᵉ xᵉ
  right-unit-law-add-ℚᵉ (xᵉ ,ᵉ pᵉ) =
    eq-ℚ-sim-fraction-ℤᵉ
      ( add-fraction-ℤᵉ xᵉ zero-fraction-ℤᵉ)
      ( xᵉ)
      ( right-unit-law-add-fraction-ℤᵉ xᵉ) ∙ᵉ
    is-retraction-rational-fraction-ℚᵉ (xᵉ ,ᵉ pᵉ)
```

### Addition is associative

```agda
abstract
  associative-add-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) →
    (xᵉ +ℚᵉ yᵉ) +ℚᵉ zᵉ ＝ᵉ xᵉ +ℚᵉ (yᵉ +ℚᵉ zᵉ)
  associative-add-ℚᵉ (xᵉ ,ᵉ pxᵉ) (yᵉ ,ᵉ pyᵉ) (zᵉ ,ᵉ pzᵉ) =
    equational-reasoningᵉ
      rational-fraction-ℤᵉ
        (add-fraction-ℤᵉ (pr1ᵉ (rational-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ yᵉ))) zᵉ)
      ＝ᵉ rational-fraction-ℤᵉ (add-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ yᵉ) zᵉ)
        byᵉ eq-ℚ-sim-fraction-ℤᵉ _ _
          ( sim-fraction-add-fraction-ℤᵉ
            ( symmetric-sim-fraction-ℤᵉ _ _
              ( sim-reduced-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ yᵉ)))
            ( refl-sim-fraction-ℤᵉ zᵉ))
      ＝ᵉ rational-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ (add-fraction-ℤᵉ yᵉ zᵉ))
        byᵉ eq-ℚ-sim-fraction-ℤᵉ _ _ (associative-add-fraction-ℤᵉ xᵉ yᵉ zᵉ)
      ＝ᵉ rational-fraction-ℤᵉ
          ( add-fraction-ℤᵉ xᵉ (pr1ᵉ (rational-fraction-ℤᵉ (add-fraction-ℤᵉ yᵉ zᵉ))))
        byᵉ eq-ℚ-sim-fraction-ℤᵉ _ _
          ( sim-fraction-add-fraction-ℤᵉ
            ( refl-sim-fraction-ℤᵉ xᵉ)
            ( sim-reduced-fraction-ℤᵉ (add-fraction-ℤᵉ yᵉ zᵉ)))
```

### Addition is commutative

```agda
abstract
  commutative-add-ℚᵉ :
    (xᵉ yᵉ : ℚᵉ) →
    xᵉ +ℚᵉ yᵉ ＝ᵉ yᵉ +ℚᵉ xᵉ
  commutative-add-ℚᵉ (xᵉ ,ᵉ pxᵉ) (yᵉ ,ᵉ pyᵉ) =
    eq-ℚ-sim-fraction-ℤᵉ
      ( add-fraction-ℤᵉ xᵉ yᵉ)
      ( add-fraction-ℤᵉ yᵉ xᵉ)
      ( commutative-add-fraction-ℤᵉ xᵉ yᵉ)
```

### Interchange law for addition with respect to addition

```agda
abstract
  interchange-law-add-add-ℚᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℚᵉ) → (xᵉ +ℚᵉ yᵉ) +ℚᵉ (uᵉ +ℚᵉ vᵉ) ＝ᵉ (xᵉ +ℚᵉ uᵉ) +ℚᵉ (yᵉ +ℚᵉ vᵉ)
  interchange-law-add-add-ℚᵉ =
    interchange-law-commutative-and-associativeᵉ
      add-ℚᵉ
      commutative-add-ℚᵉ
      associative-add-ℚᵉ
```

### The negative of a rational number is its additive inverse

```agda
abstract
  left-inverse-law-add-ℚᵉ : (xᵉ : ℚᵉ) → (neg-ℚᵉ xᵉ) +ℚᵉ xᵉ ＝ᵉ zero-ℚᵉ
  left-inverse-law-add-ℚᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( add-fraction-ℤᵉ (neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)) (fraction-ℚᵉ xᵉ))
      ( fraction-ℚᵉ zero-ℚᵉ)
      ( sim-is-zero-numerator-fraction-ℤᵉ
        ( add-fraction-ℤᵉ (neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)) (fraction-ℚᵉ xᵉ))
        ( fraction-ℚᵉ zero-ℚᵉ)
        ( is-zero-numerator-add-left-neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
        ( reflᵉ))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ zero-ℚᵉ)

  right-inverse-law-add-ℚᵉ : (xᵉ : ℚᵉ) → xᵉ +ℚᵉ (neg-ℚᵉ xᵉ) ＝ᵉ zero-ℚᵉ
  right-inverse-law-add-ℚᵉ xᵉ =
    commutative-add-ℚᵉ xᵉ (neg-ℚᵉ xᵉ) ∙ᵉ left-inverse-law-add-ℚᵉ xᵉ
```

### The negatives of rational numbers distribute over addition

```agda
abstract
  distributive-neg-add-ℚᵉ :
    (xᵉ yᵉ : ℚᵉ) → neg-ℚᵉ (xᵉ +ℚᵉ yᵉ) ＝ᵉ neg-ℚᵉ xᵉ +ℚᵉ neg-ℚᵉ yᵉ
  distributive-neg-add-ℚᵉ (xᵉ ,ᵉ dxpᵉ) (yᵉ ,ᵉ dypᵉ) =
    ( invᵉ (preserves-neg-rational-fraction-ℤᵉ (xᵉ +fraction-ℤᵉ yᵉ))) ∙ᵉ
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( neg-fraction-ℤᵉ (xᵉ +fraction-ℤᵉ yᵉ))
      ( add-fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ) (neg-fraction-ℤᵉ yᵉ))
      ( distributive-neg-add-fraction-ℤᵉ xᵉ yᵉ))
```

## See also

-ᵉ Theᵉ additiveᵉ groupᵉ structureᵉ onᵉ theᵉ rationalᵉ numbersᵉ isᵉ definedᵉ in
  [`elementary-number-theory.additive-group-of-rational-numbers`](elementary-number-theory.additive-group-of-rational-numbers.md).ᵉ