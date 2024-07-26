# Precategory solver

```agda
{-# OPTIONSᵉ --no-exact-splitᵉ #-}

module reflection.precategory-solverᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import reflection.argumentsᵉ
open import reflection.termsᵉ
open import reflection.type-checking-monadᵉ
```

</details>

## Idea

Thisᵉ module definesᵉ aᵉ macro,ᵉ `solve-Precategory!`ᵉ thatᵉ solvesᵉ anyᵉ equationᵉ
betweenᵉ morphismsᵉ ofᵉ aᵉ precategory,ᵉ asᵉ longᵉ asᵉ it'sᵉ derivableᵉ fromᵉ theᵉ axiomsᵉ ofᵉ
precategories.ᵉ

Toᵉ do this,ᵉ weᵉ introduceᵉ theᵉ typeᵉ `Precategory-Expression`,ᵉ whichᵉ isᵉ aᵉ syntacticᵉ
representationᵉ ofᵉ aᵉ morphism.ᵉ Then,ᵉ notingᵉ thatᵉ everyᵉ morphismᵉ isᵉ representedᵉ byᵉ
anᵉ expressionᵉ (throughᵉ `in-Precategory-Expression`),ᵉ itᵉ willᵉ beᵉ sufficientᵉ to
proveᵉ anᵉ equalityᵉ ofᵉ expresionsᵉ to proveᵉ anᵉ equalityᵉ ofᵉ morphisms.ᵉ However,ᵉ ifᵉ
twoᵉ morphismsᵉ areᵉ equal,ᵉ thenᵉ theirᵉ normalizedᵉ expressionsᵉ areᵉ equalᵉ byᵉ
reflexivity,ᵉ soᵉ thatᵉ theᵉ problemᵉ isᵉ reducedᵉ to findingᵉ whichᵉ
`Precategory-Expression`ᵉ representsᵉ aᵉ givenᵉ morphism.ᵉ

Thisᵉ lastᵉ problem,ᵉ asᵉ wellᵉ asᵉ theᵉ applicationᵉ ofᵉ theᵉ
`solve-Precategory-Expression`ᵉ lemma,ᵉ isᵉ whatᵉ theᵉ macroᵉ automates.ᵉ

## Definition

### The syntactic representation of a morphism

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  data
    Precategory-Expressionᵉ :
      obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    id-hom-Precategory-Expressionᵉ :
      {xᵉ : obj-Precategoryᵉ Cᵉ} → Precategory-Expressionᵉ xᵉ xᵉ
    hom-Precategory-Expressionᵉ :
      {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
      hom-Precategoryᵉ Cᵉ xᵉ yᵉ → Precategory-Expressionᵉ xᵉ yᵉ
    comp-hom-Precategory-Expressionᵉ :
      {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ} →
      Precategory-Expressionᵉ yᵉ zᵉ →
      Precategory-Expressionᵉ xᵉ yᵉ →
      Precategory-Expressionᵉ xᵉ zᵉ
```

### The syntactic representation of a morphism

```agda
  in-Precategory-Expressionᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    Precategory-Expressionᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  in-Precategory-Expressionᵉ id-hom-Precategory-Expressionᵉ = id-hom-Precategoryᵉ Cᵉ
  in-Precategory-Expressionᵉ (hom-Precategory-Expressionᵉ fᵉ) = fᵉ
  in-Precategory-Expressionᵉ (comp-hom-Precategory-Expressionᵉ fᵉ gᵉ) =
    comp-hom-Precategoryᵉ Cᵉ
      ( in-Precategory-Expressionᵉ fᵉ)
      ( in-Precategory-Expressionᵉ gᵉ)
```

### The normalization of the syntactic representation of a morphism

```agda
  eval-Precategory-Expressionᵉ :
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ} →
    Precategory-Expressionᵉ yᵉ zᵉ →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ xᵉ zᵉ
  eval-Precategory-Expressionᵉ id-hom-Precategory-Expressionᵉ fᵉ = fᵉ
  eval-Precategory-Expressionᵉ (hom-Precategory-Expressionᵉ fᵉ) gᵉ =
    comp-hom-Precategoryᵉ Cᵉ fᵉ gᵉ
  eval-Precategory-Expressionᵉ (comp-hom-Precategory-Expressionᵉ fᵉ gᵉ) hᵉ =
    eval-Precategory-Expressionᵉ fᵉ (eval-Precategory-Expressionᵉ gᵉ hᵉ)

  is-sound-eval-Precategory-Expressionᵉ :
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
    (eᵉ : Precategory-Expressionᵉ yᵉ zᵉ)
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( eval-Precategory-Expressionᵉ eᵉ fᵉ) ＝ᵉ
    ( comp-hom-Precategoryᵉ Cᵉ (in-Precategory-Expressionᵉ eᵉ) fᵉ)
  is-sound-eval-Precategory-Expressionᵉ id-hom-Precategory-Expressionᵉ fᵉ =
    invᵉ (left-unit-law-comp-hom-Precategoryᵉ Cᵉ fᵉ)
  is-sound-eval-Precategory-Expressionᵉ (hom-Precategory-Expressionᵉ fᵉ) gᵉ = reflᵉ
  is-sound-eval-Precategory-Expressionᵉ (comp-hom-Precategory-Expressionᵉ fᵉ gᵉ) hᵉ =
    ( is-sound-eval-Precategory-Expressionᵉ
      ( fᵉ)
      ( eval-Precategory-Expressionᵉ gᵉ hᵉ)) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Cᵉ (in-Precategory-Expressionᵉ fᵉ))
      ( is-sound-eval-Precategory-Expressionᵉ gᵉ hᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-comp-hom-Precategoryᵉ
        Cᵉ (in-Precategory-Expressionᵉ fᵉ) (in-Precategory-Expressionᵉ gᵉ) hᵉ))

  normalize-Precategory-Expressionᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    Precategory-Expressionᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  normalize-Precategory-Expressionᵉ eᵉ =
    eval-Precategory-Expressionᵉ eᵉ (id-hom-Precategoryᵉ Cᵉ)

  is-sound-normalize-Precategory-Expressionᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    (eᵉ : Precategory-Expressionᵉ xᵉ yᵉ) →
    normalize-Precategory-Expressionᵉ eᵉ ＝ᵉ in-Precategory-Expressionᵉ eᵉ
  is-sound-normalize-Precategory-Expressionᵉ eᵉ =
    ( is-sound-eval-Precategory-Expressionᵉ eᵉ (id-hom-Precategoryᵉ Cᵉ)) ∙ᵉ
    ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ (in-Precategory-Expressionᵉ eᵉ))

  abstract
    solve-Precategory-Expressionᵉ :
      {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
      (fᵉ gᵉ : Precategory-Expressionᵉ xᵉ yᵉ) →
      normalize-Precategory-Expressionᵉ fᵉ ＝ᵉ normalize-Precategory-Expressionᵉ gᵉ →
      in-Precategory-Expressionᵉ fᵉ ＝ᵉ in-Precategory-Expressionᵉ gᵉ
    solve-Precategory-Expressionᵉ fᵉ gᵉ pᵉ =
      ( invᵉ (is-sound-normalize-Precategory-Expressionᵉ fᵉ)) ∙ᵉ
      ( pᵉ) ∙ᵉ
      ( is-sound-normalize-Precategory-Expressionᵉ gᵉ)
```

## The macro definition

### The conversion of a morphism into an expression

```agda
private
  infixr 11 _∷ᵉ_
  pattern _∷ᵉ_ xᵉ xsᵉ = consᵉ xᵉ xsᵉ
  _++ᵉ_ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → listᵉ Aᵉ → listᵉ Aᵉ
  _++ᵉ_ = concat-listᵉ
  infixr 10 _++ᵉ_

  pattern apply-pr1ᵉ xsᵉ =
    definition-Term-Agdaᵉ (quoteᵉ pr1ᵉ)
      ( hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        xsᵉ)

  pattern apply-pr2ᵉ xsᵉ =
    definition-Term-Agdaᵉ (quoteᵉ pr2ᵉ)
      ( hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        hidden-Argument-Agdaᵉ unknown-Term-Agdaᵉ ∷ᵉ
        xsᵉ)
```

### Building a term of `Precategory-Expression C x y` from a term of type `hom-Precategory C x y`

```agda
build-Precategory-Expressionᵉ : Term-Agdaᵉ → Term-Agdaᵉ
build-Precategory-Expressionᵉ
  ( apply-pr1ᵉ
    ( visible-Argument-Agdaᵉ
      ( apply-pr2ᵉ
        ( visible-Argument-Agdaᵉ
          ( apply-pr2ᵉ
            ( visible-Argument-Agdaᵉ
              ( apply-pr2ᵉ (visible-Argument-Agdaᵉ Cᵉ ∷ᵉ nilᵉ)) ∷ᵉ
              ( nilᵉ))) ∷ᵉ
            ( nilᵉ))) ∷ᵉ
          ( visible-Argument-Agdaᵉ xᵉ) ∷ᵉ
          nilᵉ)) =
  constructor-Term-Agdaᵉ (quoteᵉ id-hom-Precategory-Expressionᵉ) nilᵉ
build-Precategory-Expressionᵉ
  ( apply-pr1ᵉ
    ( visible-Argument-Agdaᵉ
      ( apply-pr1ᵉ
        ( visible-Argument-Agdaᵉ
          ( apply-pr2ᵉ
            ( visible-Argument-Agdaᵉ
              ( apply-pr2ᵉ
                (visible-Argument-Agdaᵉ Cᵉ ∷ᵉ nilᵉ)) ∷ᵉ nilᵉ))
            ∷ᵉ nilᵉ)) ∷ᵉ
      hidden-Argument-Agdaᵉ xᵉ ∷ᵉ hidden-Argument-Agdaᵉ yᵉ ∷ᵉ hidden-Argument-Agdaᵉ zᵉ ∷ᵉ
      visible-Argument-Agdaᵉ gᵉ ∷ᵉ visible-Argument-Agdaᵉ fᵉ ∷ᵉ nilᵉ)) =
  constructor-Term-Agdaᵉ
    ( quoteᵉ comp-hom-Precategory-Expressionᵉ)
    ( visible-Argument-Agdaᵉ (build-Precategory-Expressionᵉ gᵉ) ∷ᵉ
      visible-Argument-Agdaᵉ (build-Precategory-Expressionᵉ fᵉ) ∷ᵉ
      nilᵉ)
build-Precategory-Expressionᵉ fᵉ =
  constructor-Term-Agdaᵉ
    ( quoteᵉ hom-Precategory-Expressionᵉ)
    ( visible-Argument-Agdaᵉ fᵉ ∷ᵉ nilᵉ)
```

### The application of the `solve-Precategory-Expression` lemma

```agda
apply-solve-Precategory-Expressionᵉ :
  Term-Agdaᵉ → Term-Agdaᵉ → Term-Agdaᵉ → Term-Agdaᵉ
apply-solve-Precategory-Expressionᵉ catᵉ lhsᵉ rhsᵉ =
  definition-Term-Agdaᵉ
    ( quoteᵉ solve-Precategory-Expressionᵉ)
    ( replicate-hidden-Argument-Agdaᵉ 2 ++ᵉ
      visible-Argument-Agdaᵉ catᵉ ∷ᵉ
      replicate-hidden-Argument-Agdaᵉ 2 ++ᵉ
      visible-Argument-Agdaᵉ lhsᵉ ∷ᵉ
      visible-Argument-Agdaᵉ rhsᵉ ∷ᵉ
      visible-Argument-Agdaᵉ (constructor-Term-Agdaᵉ (quoteᵉ reflᵉ) nilᵉ) ∷ᵉ
      nilᵉ)
```

### The macro definition

```agda
macroᵉ
  solve-Precategory!ᵉ : Term-Agdaᵉ → Term-Agdaᵉ → type-Type-Checkerᵉ unitᵉ
  solve-Precategory!ᵉ catᵉ holeᵉ = do
    goalᵉ ←ᵉ infer-typeᵉ holeᵉ >>=ᵉ reduceᵉ
    (lhsᵉ ,ᵉ rhsᵉ) ←ᵉ boundary-Type-Checkerᵉ goalᵉ
    built-lhsᵉ ←ᵉ
      normalizeᵉ lhsᵉ >>=ᵉ (return-Type-Checkerᵉ ∘ᵉ build-Precategory-Expressionᵉ)
    built-rhsᵉ ←ᵉ
      normalizeᵉ rhsᵉ >>=ᵉ (return-Type-Checkerᵉ ∘ᵉ build-Precategory-Expressionᵉ)
    unifyᵉ holeᵉ (apply-solve-Precategory-Expressionᵉ catᵉ built-lhsᵉ built-rhsᵉ)
```

## Examples

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ}
  where

  private
    _ :
      {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
      {fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ} →
      fᵉ ＝ᵉ fᵉ
    _ = solve-Precategory!ᵉ Cᵉ

    _ :
      {xᵉ : obj-Precategoryᵉ Cᵉ} →
      id-hom-Precategoryᵉ Cᵉ {xᵉ} ＝ᵉ id-hom-Precategoryᵉ Cᵉ {xᵉ}
    _ = solve-Precategory!ᵉ Cᵉ

    _ :
      {aᵉ bᵉ cᵉ : obj-Precategoryᵉ Cᵉ}
      {fᵉ : hom-Precategoryᵉ Cᵉ aᵉ bᵉ}
      {gᵉ : hom-Precategoryᵉ Cᵉ bᵉ cᵉ} →
      (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ
    _ = solve-Precategory!ᵉ Cᵉ

    _ :
      {aᵉ bᵉ cᵉ dᵉ : obj-Precategoryᵉ Cᵉ}
      {fᵉ : hom-Precategoryᵉ Cᵉ aᵉ bᵉ}
      {gᵉ : hom-Precategoryᵉ Cᵉ bᵉ cᵉ} →
      {hᵉ : hom-Precategoryᵉ Cᵉ cᵉ dᵉ} →
      comp-hom-Precategoryᵉ Cᵉ hᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ (comp-hom-Precategoryᵉ Cᵉ hᵉ gᵉ) fᵉ
    _ = solve-Precategory!ᵉ Cᵉ

    _ :
      {aᵉ bᵉ cᵉ dᵉ : obj-Precategoryᵉ Cᵉ}
      {fᵉ : hom-Precategoryᵉ Cᵉ aᵉ bᵉ}
      {gᵉ : hom-Precategoryᵉ Cᵉ bᵉ cᵉ} →
      {hᵉ : hom-Precategoryᵉ Cᵉ cᵉ dᵉ} →
      comp-hom-Precategoryᵉ Cᵉ
        ( comp-hom-Precategoryᵉ Cᵉ hᵉ (id-hom-Precategoryᵉ Cᵉ))
        ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Precategoryᵉ Cᵉ
        ( comp-hom-Precategoryᵉ Cᵉ hᵉ gᵉ)
        ( comp-hom-Precategoryᵉ Cᵉ (id-hom-Precategoryᵉ Cᵉ) fᵉ)
    _ = solve-Precategory!ᵉ Cᵉ
```