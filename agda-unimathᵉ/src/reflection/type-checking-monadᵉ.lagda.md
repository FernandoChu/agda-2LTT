# The type checking monad

```agda
{-# OPTIONSᵉ --no-exact-splitᵉ #-}

module reflection.type-checking-monadᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.listsᵉ

open import primitives.stringsᵉ

open import reflection.argumentsᵉ
open import reflection.definitionsᵉ
open import reflection.metavariablesᵉ
open import reflection.namesᵉ
open import reflection.termsᵉ
```

</details>

## Idea

Theᵉ type-checkingᵉ monadᵉ `type-Type-Checker`ᵉ allowsᵉ usᵉ to interactᵉ directlyᵉ with
Agda'sᵉ typeᵉ checkingᵉ mechanism.ᵉ Additionallyᵉ to primitivesᵉ (seeᵉ below),ᵉ Agdaᵉ
includesᵉ theᵉ theᵉ keywordᵉ `unquote`ᵉ to manuallyᵉ unquoteᵉ anᵉ elementᵉ fromᵉ
`type-Type-Checkerᵉ unit`.ᵉ

## Definitions

```agda
data Error-Partᵉ : UUᵉ lzero where
  string-Error-Partᵉ : Stringᵉ → Error-Partᵉ
  term-Error-Partᵉ : Term-Agdaᵉ → Error-Partᵉ
  pattern-Error-Partᵉ : Pattern-Agdaᵉ → Error-Partᵉ
  name-Error-Partᵉ : Name-Agdaᵉ → Error-Partᵉ

postulate
  --ᵉ Theᵉ typeᵉ checkingᵉ monadᵉ
  type-Type-Checkerᵉ :
    {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
  return-Type-Checkerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → type-Type-Checkerᵉ Aᵉ
  bind-Type-Checkerᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    type-Type-Checkerᵉ Aᵉ → (Aᵉ → type-Type-Checkerᵉ Bᵉ) → type-Type-Checkerᵉ Bᵉ
  --ᵉ Triesᵉ theᵉ unifyᵉ theᵉ firstᵉ termᵉ with theᵉ secondᵉ
  unifyᵉ :
    Term-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  --ᵉ Givesᵉ anᵉ errorᵉ
  type-errorᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Error-Partᵉ → type-Type-Checkerᵉ Aᵉ
  --ᵉ Infersᵉ theᵉ typeᵉ ofᵉ aᵉ goalᵉ
  infer-typeᵉ :
    Term-Agdaᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  check-typeᵉ :
    Term-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  normalizeᵉ :
    Term-Agdaᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  reduceᵉ :
    Term-Agdaᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  --ᵉ Triesᵉ theᵉ firstᵉ computation,ᵉ ifᵉ itᵉ failsᵉ triesᵉ theᵉ secondᵉ
  catch-Type-Checkerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  quote-Type-Checkerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  unquote-Type-Checkerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Term-Agdaᵉ → type-Type-Checkerᵉ Aᵉ
  quoteω-Type-Checkerᵉ :
    {Aᵉ : UUωᵉ} → Aᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  get-contextᵉ :
    type-Type-Checkerᵉ Telescope-Agdaᵉ
  extend-contextᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    Stringᵉ → Argument-Agdaᵉ Term-Agdaᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  in-contextᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    Telescope-Agdaᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  fresh-nameᵉ :
    Stringᵉ → type-Type-Checkerᵉ Name-Agdaᵉ
  declare-definitionᵉ :
    Argument-Agdaᵉ Name-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  declare-postulateᵉ :
    Argument-Agdaᵉ Name-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  define-functionᵉ :
    Name-Agdaᵉ → listᵉ Clause-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  get-typeᵉ :
    Name-Agdaᵉ → type-Type-Checkerᵉ Term-Agdaᵉ
  get-definitionᵉ :
    Name-Agdaᵉ → type-Type-Checkerᵉ Definition-Agdaᵉ
  block-Type-Checkerᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Blocker-Agdaᵉ → type-Type-Checkerᵉ Aᵉ
  commit-Type-Checkerᵉ :
    type-Type-Checkerᵉ unitᵉ
  is-macroᵉ :
    Name-Agdaᵉ → type-Type-Checkerᵉ boolᵉ

  format-errorᵉ :
    listᵉ Error-Partᵉ → type-Type-Checkerᵉ Stringᵉ

  --ᵉ Printsᵉ theᵉ thirdᵉ argumentᵉ ifᵉ theᵉ correspondingᵉ verbosityᵉ Level isᵉ turnedᵉ
  --ᵉ onᵉ (withᵉ theᵉ -vᵉ flagᵉ to Agda).ᵉ
  debug-printᵉ :
    Stringᵉ → ℕᵉ → listᵉ Error-Partᵉ → type-Type-Checkerᵉ unitᵉ

  --ᵉ Ifᵉ 'true',ᵉ makesᵉ theᵉ followingᵉ primitivesᵉ alsoᵉ normalizeᵉ
  --ᵉ theirᵉ resultsᵉ: infer-type,ᵉ check-type,ᵉ quote-Type-Checker,ᵉ get-type,ᵉ andᵉ get-contextᵉ
  with-normalizationᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → boolᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  ask-normalizationᵉ : type-Type-Checkerᵉ boolᵉ

  --ᵉ Ifᵉ 'true',ᵉ makesᵉ theᵉ followingᵉ primitivesᵉ to reconstructᵉ hiddenᵉ argumentsᵉ:
  --ᵉ get-definition,ᵉ normalize,ᵉ reduce,ᵉ infer-type,ᵉ check-typeᵉ andᵉ get-contextᵉ
  with-reconstructedᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → boolᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  ask-reconstructedᵉ : type-Type-Checkerᵉ boolᵉ

  --ᵉ Whetherᵉ implicitᵉ argumentsᵉ atᵉ theᵉ endᵉ shouldᵉ beᵉ turnedᵉ intoᵉ metavariablesᵉ
  with-expand-lastᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → boolᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  ask-expand-lastᵉ : type-Type-Checkerᵉ boolᵉ

  --ᵉ White/blacklistᵉ specificᵉ definitionsᵉ forᵉ reductionᵉ whileᵉ executingᵉ theᵉ type-Type-Checkerᵉ computationᵉ
  --ᵉ 'true'ᵉ forᵉ whitelist,ᵉ 'false'ᵉ forᵉ blacklistᵉ
  with-reduce-definitionsᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
    boolᵉ ×ᵉ listᵉ Name-Agdaᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
  ask-reduce-definitionsᵉ :
    type-Type-Checkerᵉ (boolᵉ ×ᵉ listᵉ Name-Agdaᵉ)

  --ᵉ Failᵉ ifᵉ theᵉ givenᵉ computationᵉ givesᵉ riseᵉ to new,ᵉ unsolvedᵉ
  --ᵉ "blocking"ᵉ constraints.ᵉ
  no-constraintsᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ

  --ᵉ Runᵉ theᵉ givenᵉ type-Type-Checkerᵉ actionᵉ andᵉ returnᵉ theᵉ firstᵉ component.ᵉ Resetsᵉ to
  --ᵉ theᵉ oldᵉ type-Type-Checkerᵉ stateᵉ ifᵉ theᵉ secondᵉ componentᵉ isᵉ 'false',ᵉ orᵉ keepᵉ theᵉ
  --ᵉ newᵉ type-Type-Checkerᵉ stateᵉ ifᵉ itᵉ isᵉ 'true'.ᵉ
  run-speculativeᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → type-Type-Checkerᵉ (Aᵉ ×ᵉ boolᵉ) → type-Type-Checkerᵉ Aᵉ

  --ᵉ Getᵉ aᵉ listᵉ ofᵉ allᵉ possibleᵉ instance candidatesᵉ forᵉ theᵉ givenᵉ metavariableᵉ
  --ᵉ variableᵉ (itᵉ doesᵉ notᵉ haveᵉ to beᵉ anᵉ instance metavariable).ᵉ
  get-instancesᵉ :
    Metavariable-Agdaᵉ → type-Type-Checkerᵉ (listᵉ Term-Agdaᵉ)

  declare-dataᵉ :
    Name-Agdaᵉ → ℕᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  define-dataᵉ :
    Name-Agdaᵉ → listᵉ (Name-Agdaᵉ ×ᵉ Term-Agdaᵉ) → type-Type-Checkerᵉ unitᵉ
```

## Bindings

```agda














































```

## Monad syntax

```agda
infixl 15 _<|>ᵉ_
_<|>ᵉ_ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Aᵉ
_<|>ᵉ_ = catch-Type-Checkerᵉ

infixl 10 _>>=ᵉ_ _>>ᵉ_ _<&>ᵉ_
_>>=ᵉ_ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-Type-Checkerᵉ Aᵉ → (Aᵉ → type-Type-Checkerᵉ Bᵉ) → type-Type-Checkerᵉ Bᵉ
_>>=ᵉ_ = bind-Type-Checkerᵉ

_>>ᵉ_ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-Type-Checkerᵉ Aᵉ → type-Type-Checkerᵉ Bᵉ → type-Type-Checkerᵉ Bᵉ
xsᵉ >>ᵉ ysᵉ = bind-Type-Checkerᵉ xsᵉ (λ _ → ysᵉ)

_<&>ᵉ_ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-Type-Checkerᵉ Aᵉ → (Aᵉ → Bᵉ) → type-Type-Checkerᵉ Bᵉ
xsᵉ <&>ᵉ fᵉ = bind-Type-Checkerᵉ xsᵉ (λ xᵉ → return-Type-Checkerᵉ (fᵉ xᵉ))
```

## Examples

Theᵉ followingᵉ examplesᵉ showᵉ howᵉ theᵉ type-checkingᵉ monadᵉ canᵉ beᵉ used.ᵉ Theyᵉ wereᵉ
adaptedᵉ fromᵉ alhassy'sᵉ
[_gentleᵉ introᵉ to reflection_](https://github.com/alhassy/gentle-intro-to-reflection).ᵉ

### Unifying a goal with a constant

#### Manually

```agda
private
  num-Type-Checkerᵉ : Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  num-Type-Checkerᵉ hᵉ = unifyᵉ (quoteTermᵉ 314ᵉ) hᵉ

  _ : unquoteᵉ num-Type-Checkerᵉ ＝ᵉ 314
  _ = reflᵉ
```

#### By use of a macro

```agda
  macroᵉ
    num-Type-Checker'ᵉ : Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
    num-Type-Checker'ᵉ hᵉ = unifyᵉ (quoteTermᵉ 1ᵉ) hᵉ

  _ : num-Type-Checker'ᵉ ＝ᵉ 1
  _ = reflᵉ
```

### Modifying a term

```agda
  macroᵉ
    swap-addᵉ : Term-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
    swap-addᵉ (definition-Term-Agdaᵉ (quoteᵉ add-ℕᵉ) (consᵉ aᵉ (consᵉ bᵉ nilᵉ))) holeᵉ =
      unifyᵉ holeᵉ (definition-Term-Agdaᵉ (quoteᵉ add-ℕᵉ) (consᵉ bᵉ (consᵉ aᵉ nilᵉ)))
    {-# CATCHALLᵉ #-}
    swap-addᵉ vᵉ holeᵉ = unifyᵉ holeᵉ vᵉ

  ex1ᵉ : (aᵉ bᵉ : ℕᵉ) → swap-addᵉ (add-ℕᵉ aᵉ bᵉ) ＝ᵉ (add-ℕᵉ bᵉ aᵉ)
  ex1ᵉ aᵉ bᵉ = reflᵉ

  ex2ᵉ : (aᵉ bᵉ : ℕᵉ) → swap-addᵉ aᵉ ＝ᵉ aᵉ
  ex2ᵉ aᵉ bᵉ = reflᵉ
```

### Trying a path

Theᵉ followingᵉ exampleᵉ triesᵉ to solveᵉ aᵉ goalᵉ byᵉ using pathᵉ `p`ᵉ orᵉ `invᵉ p`.ᵉ Thisᵉ
exampleᵉ wasᵉ addaptedᵉ fromᵉ

```agda
  private
    infixr 10 _∷ᵉ_
    pattern _∷ᵉ_ xᵉ xsᵉ = consᵉ xᵉ xsᵉ

  ＝-type-infoᵉ :
    Term-Agdaᵉ →
    type-Type-Checkerᵉ
      ( Argument-Agdaᵉ Term-Agdaᵉ ×ᵉ
        ( Argument-Agdaᵉ Term-Agdaᵉ ×ᵉ
          ( Term-Agdaᵉ ×ᵉ Term-Agdaᵉ)))
  ＝-type-infoᵉ
    ( definition-Term-Agdaᵉ
      ( quoteᵉ _＝ᵉ_)
      ( 𝓁ᵉ ∷ᵉ 𝒯ᵉ ∷ᵉ (cons-Argument-Agdaᵉ _ lᵉ) ∷ᵉ (cons-Argument-Agdaᵉ _ rᵉ) ∷ᵉ nilᵉ)) =
    return-Type-Checkerᵉ (𝓁ᵉ ,ᵉ 𝒯ᵉ ,ᵉ lᵉ ,ᵉ rᵉ)
  ＝-type-infoᵉ _ =
    type-errorᵉ (unit-listᵉ (string-Error-Partᵉ "Term-Agdaᵉ isᵉ notᵉ aᵉ ＝-type."ᵉ))

  macroᵉ
    try-path!ᵉ : Term-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
    try-path!ᵉ pᵉ goalᵉ =
      ( unifyᵉ goalᵉ pᵉ) <|>ᵉ
      ( do
        p-typeᵉ ←ᵉ infer-typeᵉ pᵉ
        𝓁ᵉ ,ᵉ 𝒯ᵉ ,ᵉ lᵉ ,ᵉ rᵉ ←ᵉ ＝-type-infoᵉ p-typeᵉ
        unifyᵉ goalᵉ
          ( definition-Term-Agdaᵉ (quoteᵉ invᵉ)
            ( 𝓁ᵉ ∷ᵉ
              𝒯ᵉ ∷ᵉ
              hidden-Argument-Agdaᵉ lᵉ ∷ᵉ
              hidden-Argument-Agdaᵉ rᵉ ∷ᵉ
              visible-Argument-Agdaᵉ pᵉ ∷ᵉ
              nilᵉ)))

  module _ (aᵉ bᵉ : ℕᵉ) (pᵉ : aᵉ ＝ᵉ bᵉ) where
    ex3ᵉ : Idᵉ aᵉ bᵉ
    ex3ᵉ = try-path!ᵉ pᵉ

    ex4ᵉ : Idᵉ bᵉ aᵉ
    ex4ᵉ = try-path!ᵉ pᵉ
```

### Getting the left-hand side and right-hand side of a goal

```agda
boundary-Type-Checkerᵉ : Term-Agdaᵉ → type-Type-Checkerᵉ (Term-Agdaᵉ ×ᵉ Term-Agdaᵉ)
boundary-Type-Checkerᵉ
  ( definition-Term-Agdaᵉ
    ( quoteᵉ Idᵉ)
    ( 𝓁ᵉ ∷ᵉ 𝒯ᵉ ∷ᵉ cons-Argument-Agdaᵉ _ lᵉ ∷ᵉ cons-Argument-Agdaᵉ _ rᵉ ∷ᵉ nilᵉ)) =
  return-Type-Checkerᵉ (lᵉ ,ᵉ rᵉ)
boundary-Type-Checkerᵉ tᵉ =
  type-errorᵉ
    ( string-Error-Partᵉ "Theᵉ term\nᵉ "ᵉ ∷ᵉ
      term-Error-Partᵉ tᵉ ∷ᵉ
      string-Error-Partᵉ "\nisᵉ notᵉ aᵉ ＝-type."ᵉ ∷ᵉ
      nilᵉ)
```