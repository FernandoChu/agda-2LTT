# The mediant fraction of two integer fractions

```agda
module elementary-number-theory.mediant-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "mediant"ᵉ Disambiguation="integerᵉ fractions"ᵉ Agda=mediant-fraction-ℤᵉ}}
ofᵉ twoᵉ fractionsᵉ isᵉ theᵉ quotientᵉ ofᵉ theᵉ sumᵉ ofᵉ theᵉ numeratorsᵉ byᵉ theᵉ sumᵉ ofᵉ theᵉ
denominators.ᵉ

## Definitions

### The mediant of two fractions

```agda
mediant-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → fraction-ℤᵉ
mediant-fraction-ℤᵉ (aᵉ ,ᵉ bᵉ) (cᵉ ,ᵉ dᵉ) = (add-ℤᵉ aᵉ cᵉ ,ᵉ add-positive-ℤᵉ bᵉ dᵉ)
```

## Properties

### The mediant preserves the cross-multiplication difference

```agda
cross-mul-diff-left-mediant-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) →
  Idᵉ
    ( cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ)
    ( cross-mul-diff-fraction-ℤᵉ xᵉ ( mediant-fraction-ℤᵉ xᵉ yᵉ))
cross-mul-diff-left-mediant-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ pxᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ pyᵉ) =
  equational-reasoningᵉ
  (nyᵉ *ℤᵉ dxᵉ -ℤᵉ nxᵉ *ℤᵉ dyᵉ)
  ＝ᵉ (nxᵉ *ℤᵉ dxᵉ +ℤᵉ nyᵉ *ℤᵉ dxᵉ) -ℤᵉ (nxᵉ *ℤᵉ dxᵉ +ℤᵉ nxᵉ *ℤᵉ dyᵉ)
    byᵉ invᵉ
      ( left-translation-diff-ℤᵉ
        ( mul-ℤᵉ nyᵉ dxᵉ)
        ( mul-ℤᵉ nxᵉ dyᵉ)
        ( mul-ℤᵉ nxᵉ dxᵉ))
  ＝ᵉ (nxᵉ +ℤᵉ nyᵉ) *ℤᵉ dxᵉ -ℤᵉ nxᵉ *ℤᵉ (dxᵉ +ℤᵉ dyᵉ)
    byᵉ ap-diff-ℤᵉ
      ( invᵉ (right-distributive-mul-add-ℤᵉ nxᵉ nyᵉ dxᵉ))
      ( invᵉ (left-distributive-mul-add-ℤᵉ nxᵉ dxᵉ dyᵉ))

cross-mul-diff-right-mediant-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) →
  Idᵉ
    ( cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ)
    ( cross-mul-diff-fraction-ℤᵉ (mediant-fraction-ℤᵉ xᵉ yᵉ) yᵉ)
cross-mul-diff-right-mediant-fraction-ℤᵉ (nxᵉ ,ᵉ dxᵉ ,ᵉ pxᵉ) (nyᵉ ,ᵉ dyᵉ ,ᵉ pyᵉ) =
  equational-reasoningᵉ
  (nyᵉ *ℤᵉ dxᵉ -ℤᵉ nxᵉ *ℤᵉ dyᵉ)
  ＝ᵉ (nyᵉ *ℤᵉ dxᵉ +ℤᵉ nyᵉ *ℤᵉ dyᵉ) -ℤᵉ (nxᵉ *ℤᵉ dyᵉ +ℤᵉ nyᵉ *ℤᵉ dyᵉ)
    byᵉ invᵉ
      ( right-translation-diff-ℤᵉ
        ( mul-ℤᵉ nyᵉ dxᵉ)
        ( mul-ℤᵉ nxᵉ dyᵉ)
        ( mul-ℤᵉ nyᵉ dyᵉ))
  ＝ᵉ nyᵉ *ℤᵉ (dxᵉ +ℤᵉ dyᵉ) -ℤᵉ (nxᵉ +ℤᵉ nyᵉ) *ℤᵉ dyᵉ
    byᵉ ap-diff-ℤᵉ
      ( invᵉ (left-distributive-mul-add-ℤᵉ nyᵉ dxᵉ dyᵉ))
      ( invᵉ (right-distributive-mul-add-ℤᵉ nxᵉ nyᵉ dyᵉ))
```

## External links

-ᵉ [Mediantᵉ fraction](<https://en.wikipedia.org/wiki/Mediant_(mathematics)>ᵉ) atᵉ
  Wikipediaᵉ