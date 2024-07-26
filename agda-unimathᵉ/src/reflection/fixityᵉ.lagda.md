# Fixity

```agda
module reflection.fixityᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import primitives.floatsᵉ

open import reflection.namesᵉ
```

</details>

## Idea

Theᵉ fixityᵉ ofᵉ aᵉ quotedᵉ nameᵉ isᵉ givenᵉ byᵉ

-ᵉ Anᵉ associativity,ᵉ i.e.ᵉ itᵉ isᵉ left-associative,ᵉ right-associativeᵉ orᵉ neither.ᵉ
-ᵉ Aᵉ precedence,ᵉ i.e.ᵉ itᵉ isᵉ unrelatedᵉ (itᵉ hasᵉ noᵉ precedenceᵉ) orᵉ itᵉ isᵉ relatedᵉ andᵉ
  hasᵉ aᵉ floatᵉ precedence.ᵉ

## Definition

```agda
data Associativity-Agdaᵉ : UUᵉ lzero where
  left-Associativity-Agdaᵉ : Associativity-Agdaᵉ
  right-Associativity-Agdaᵉ : Associativity-Agdaᵉ
  none-Associativity-Agdaᵉ : Associativity-Agdaᵉ

data Precedence-Agdaᵉ : UUᵉ lzero where
  related-Precedence-Agdaᵉ : Floatᵉ → Precedence-Agdaᵉ
  unrelated-Precedence-Agdaᵉ : Precedence-Agdaᵉ

data Fixity-Agdaᵉ : UUᵉ lzero where
  cons-Fixity-Agdaᵉ : Associativity-Agdaᵉ → Precedence-Agdaᵉ → Fixity-Agdaᵉ













primitive
  primQNameFixityᵉ : Name-Agdaᵉ → Fixity-Agdaᵉ
```

## Examples

```agda
_ :
  primQNameFixityᵉ (quoteᵉ add-ℤᵉ) ＝ᵉ
  cons-Fixity-Agdaᵉ none-Associativity-Agdaᵉ unrelated-Precedence-Agdaᵉ
_ = reflᵉ

_ :
  primQNameFixityᵉ (quoteᵉ (_+ℤᵉ_)) ＝ᵉ
  cons-Fixity-Agdaᵉ left-Associativity-Agdaᵉ (related-Precedence-Agdaᵉ 35.0ᵉ)
_ = reflᵉ
```