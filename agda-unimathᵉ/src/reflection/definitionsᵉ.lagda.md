# Definitions

```agda
module reflection.definitionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import reflection.abstractionsᵉ
open import reflection.argumentsᵉ
open import reflection.literalsᵉ
open import reflection.namesᵉ
open import reflection.termsᵉ
```

</details>

## Idea

Theᵉ `Definition-Agda`ᵉ typeᵉ representsᵉ aᵉ definitionᵉ in Agda.ᵉ

## Definition

```agda
data Definition-Agdaᵉ : UUᵉ lzero where
  function-Definition-Agdaᵉ : listᵉ Clause-Agdaᵉ → Definition-Agdaᵉ
  data-type-Definition-Agdaᵉ : ℕᵉ → listᵉ Name-Agdaᵉ → Definition-Agdaᵉ
  record-type-Definition-Agdaᵉ :
    Name-Agdaᵉ → listᵉ (Argument-Agdaᵉ Name-Agdaᵉ) → Definition-Agdaᵉ
  data-constructor-Definition-Agdaᵉ : Name-Agdaᵉ → Definition-Agdaᵉ
  postulate-Definition-Agdaᵉ : Definition-Agdaᵉ
  primitive-function-Definition-Agdaᵉ : Definition-Agdaᵉ
```

## Bindings

```agda







```

## Examples

### Constructors and definitions

```agda
_ : quoteTermᵉ ℕᵉ ＝ᵉ definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ
_ = reflᵉ

_ :
  quoteTermᵉ (succ-ℕᵉ zero-ℕᵉ) ＝ᵉ
  constructor-Term-Agdaᵉ
    ( quoteᵉ succ-ℕᵉ)
    ( unit-listᵉ
      ( visible-Argument-Agdaᵉ (constructor-Term-Agdaᵉ (quoteᵉ zero-ℕᵉ) nilᵉ)))
_ = reflᵉ

_ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  quoteTermᵉ (type-trunc-Propᵉ Aᵉ) ＝ᵉ
  definition-Term-Agdaᵉ
    ( quoteᵉ type-trunc-Propᵉ)
    ( consᵉ
      ( hidden-Argument-Agdaᵉ (variable-Term-Agdaᵉ 1 nilᵉ))
      ( unit-listᵉ (visible-Argument-Agdaᵉ (variable-Term-Agdaᵉ 0 nilᵉ))))
_ = reflᵉ
```

### Lambda abstractions

```agda
_ :
  quoteTermᵉ (λ (xᵉ : ℕᵉ) → xᵉ) ＝ᵉ
  lambda-Term-Agdaᵉ visible-Visibility-Argument-Agdaᵉ
    ( cons-Abstraction-Agdaᵉ "x"ᵉ (variable-Term-Agdaᵉ 0 nilᵉ))
_ = reflᵉ

_ :
  quoteTermᵉ (λ {xᵉ : ℕᵉ} (yᵉ : ℕᵉ) → xᵉ) ＝ᵉ
  lambda-Term-Agdaᵉ hidden-Visibility-Argument-Agdaᵉ
    ( cons-Abstraction-Agdaᵉ
      ( "x"ᵉ)
      ( lambda-Term-Agdaᵉ visible-Visibility-Argument-Agdaᵉ
        ( cons-Abstraction-Agdaᵉ "y"ᵉ (variable-Term-Agdaᵉ 1 nilᵉ))))
_ = reflᵉ

private
  helperᵉ : (Aᵉ : UUᵉ lzero) → Aᵉ → Aᵉ
  helperᵉ Aᵉ xᵉ = xᵉ

  _ :
    quoteTermᵉ (helperᵉ (ℕᵉ → ℕᵉ) (λ { zero-ℕᵉ → zero-ℕᵉ ; (succ-ℕᵉ xᵉ) → xᵉ})) ＝ᵉ
    definition-Term-Agdaᵉ
      ( quoteᵉ helperᵉ)
      ( consᵉ
        --ᵉ ℕᵉ → ℕᵉ
        ( visible-Argument-Agdaᵉ
          ( dependent-product-Term-Agdaᵉ
            ( visible-Argument-Agdaᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))
            ( cons-Abstraction-Agdaᵉ "_"ᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))))
        ( unit-listᵉ
          --ᵉ Theᵉ pattern matchingᵉ lambdaᵉ
          ( visible-Argument-Agdaᵉ
            ( pattern-lambda-Term-Agdaᵉ
              ( consᵉ
                --ᵉ zero-ℕᵉ clause-Clause-Agdaᵉ
                ( clause-Clause-Agdaᵉ
                  --ᵉ Noᵉ telescopeᵉ
                  ( nilᵉ)
                  --ᵉ Leftᵉ sideᵉ ofᵉ theᵉ firstᵉ lambdaᵉ caseᵉ
                  ( unit-listᵉ
                    ( visible-Argument-Agdaᵉ
                      ( constructor-Term-Agdaᵉ (quoteᵉ zero-ℕᵉ) nilᵉ)))
                  --ᵉ Rightᵉ sideᵉ ofᵉ theᵉ firstᵉ lambdaᵉ caseᵉ
                  ( constructor-Term-Agdaᵉ (quoteᵉ zero-ℕᵉ) nilᵉ))
                ( unit-listᵉ
                  --ᵉ succ-ℕᵉ clause-Clause-Agdaᵉ
                  ( clause-Clause-Agdaᵉ
                    --ᵉ Telescope-Agdaᵉ matchingᵉ theᵉ "x"ᵉ
                    ( unit-listᵉ
                      ( "x"ᵉ ,ᵉ
                        visible-Argument-Agdaᵉ
                          ( definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ)))
                    --ᵉ Leftᵉ sideᵉ ofᵉ theᵉ secondᵉ lambdaᵉ caseᵉ
                    ( unit-listᵉ
                      ( visible-Argument-Agdaᵉ
                        ( constructor-Term-Agdaᵉ
                          ( quoteᵉ succ-ℕᵉ)
                          ( unit-listᵉ
                            ( visible-Argument-Agdaᵉ (variable-Term-Agdaᵉ 0ᵉ))))))
                    --ᵉ Rightᵉ sideᵉ ofᵉ theᵉ secondᵉ lambdaᵉ caseᵉ
                    ( variable-Term-Agdaᵉ 0 nilᵉ))))
              ( nilᵉ)))))
  _ = reflᵉ

  _ :
    quoteTermᵉ (helperᵉ (emptyᵉ → ℕᵉ) (λ ())) ＝ᵉ
    definition-Term-Agdaᵉ
      ( quoteᵉ helperᵉ)
      ( consᵉ
        ( visible-Argument-Agdaᵉ
          ( dependent-product-Term-Agdaᵉ
            ( visible-Argument-Agdaᵉ (definition-Term-Agdaᵉ (quoteᵉ emptyᵉ) nilᵉ))
          ( cons-Abstraction-Agdaᵉ "_"ᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))))
        ( unit-listᵉ
          ( visible-Argument-Agdaᵉ
            --ᵉ Lambdaᵉ
            ( pattern-lambda-Term-Agdaᵉ
              ( unit-listᵉ
                --ᵉ Clause-Agdaᵉ
                ( absurd-Clause-Agdaᵉ
                  ( unit-listᵉ
                    ( "()"ᵉ ,ᵉ
                      visible-Argument-Agdaᵉ
                        ( definition-Term-Agdaᵉ (quoteᵉ emptyᵉ) nilᵉ)))
                  ( unit-listᵉ
                    ( visible-Argument-Agdaᵉ (absurd-Pattern-Agdaᵉ 0ᵉ)))))
              ( nilᵉ)))))
  _ = reflᵉ
```

### Pi terms

```agda
_ : quoteTermᵉ (ℕᵉ → ℕᵉ) ＝ᵉ
    dependent-product-Term-Agdaᵉ
      ( visible-Argument-Agdaᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))
      ( cons-Abstraction-Agdaᵉ "_"ᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))
_ = reflᵉ

_ : quoteTermᵉ ((xᵉ : ℕᵉ) → is-zero-ℕᵉ xᵉ) ＝ᵉ
    dependent-product-Term-Agdaᵉ
      ( visible-Argument-Agdaᵉ (definition-Term-Agdaᵉ (quoteᵉ ℕᵉ) nilᵉ))
      ( cons-Abstraction-Agdaᵉ "x"ᵉ
        ( definition-Term-Agdaᵉ
          ( quoteᵉ is-zero-ℕᵉ)
          ( consᵉ
            ( visible-Argument-Agdaᵉ (variable-Term-Agdaᵉ 0 nilᵉ))
            ( nilᵉ))))
_ = reflᵉ
```

### Universes

```agda
_ :
  {lᵉ : Level} →
  quoteTermᵉ (UUᵉ lᵉ) ＝ᵉ
  sort-Term-Agdaᵉ (universe-Sort-Agdaᵉ (variable-Term-Agdaᵉ 0 nilᵉ))
_ = reflᵉ

_ : quoteTermᵉ (UUᵉ (lsuc lzeroᵉ)) ＝ᵉ sort-Term-Agdaᵉ (fixed-universe-Sort-Agdaᵉ 1ᵉ)
_ = reflᵉ

_ : quoteTermᵉ (UUωᵉ) ＝ᵉ sort-Term-Agdaᵉ (fixed-large-universe-Sort-Agdaᵉ 0ᵉ)
_ = reflᵉ
```

### Literals

```agda
_ : quoteTermᵉ 3 ＝ᵉ literal-Term-Agdaᵉ (nat-Literal-Agdaᵉ 3ᵉ)
_ = reflᵉ

_ : quoteTermᵉ "hello"ᵉ ＝ᵉ literal-Term-Agdaᵉ (string-Literal-Agdaᵉ "hello"ᵉ)
_ = reflᵉ
```