# Rational real numbers

```agda
module real-numbers.rational-real-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.strict-inequality-rational-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.conjunctionᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import real-numbers.dedekind-real-numbersᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [rationals](elementary-number-theory.rational-numbers.mdᵉ) `ℚ`ᵉ
[embeds](foundation-core.embeddings.mdᵉ) intoᵉ theᵉ typeᵉ ofᵉ
[Dedekindᵉ reals](real-numbers.dedekind-real-numbers.mdᵉ) `ℝ`.ᵉ Weᵉ callᵉ numbersᵉ in
theᵉ [image](foundation.images.mdᵉ) ofᵉ thisᵉ embeddingᵉ
{{#conceptᵉ "rationalᵉ realᵉ numbers"ᵉ Agda=Rational-ℝ}}.ᵉ

## Definitions

### Strict inequality on rationals gives Dedekind cuts

```agda
is-dedekind-cut-le-ℚᵉ :
  (xᵉ : ℚᵉ) →
  is-dedekind-cutᵉ
    (λ (qᵉ : ℚᵉ) → le-ℚ-Propᵉ qᵉ xᵉ)
    (λ (rᵉ : ℚᵉ) → le-ℚ-Propᵉ xᵉ rᵉ)
is-dedekind-cut-le-ℚᵉ xᵉ =
  ( exists-lesser-ℚᵉ xᵉ ,ᵉ exists-greater-ℚᵉ xᵉ) ,ᵉ
  ( ( λ (qᵉ : ℚᵉ) →
      dense-le-ℚᵉ qᵉ xᵉ ,ᵉ
      elim-existsᵉ
        ( le-ℚ-Propᵉ qᵉ xᵉ)
        ( λ rᵉ (Hᵉ ,ᵉ H'ᵉ) → transitive-le-ℚᵉ qᵉ rᵉ xᵉ H'ᵉ Hᵉ)) ,ᵉ
    ( λ (rᵉ : ℚᵉ) →
      αᵉ xᵉ rᵉ ∘ᵉ dense-le-ℚᵉ xᵉ rᵉ ,ᵉ
      elim-existsᵉ
        ( le-ℚ-Propᵉ xᵉ rᵉ)
        ( λ qᵉ (Hᵉ ,ᵉ H'ᵉ) → transitive-le-ℚᵉ xᵉ qᵉ rᵉ Hᵉ H'ᵉ))) ,ᵉ
  ( λ (qᵉ : ℚᵉ) (Hᵉ ,ᵉ H'ᵉ) → asymmetric-le-ℚᵉ qᵉ xᵉ Hᵉ H'ᵉ) ,ᵉ
  ( located-le-ℚᵉ xᵉ)
  where
    αᵉ :
      (aᵉ bᵉ : ℚᵉ) →
      existsᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ aᵉ rᵉ ∧ᵉ le-ℚ-Propᵉ rᵉ bᵉ) →
      existsᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ rᵉ bᵉ ∧ᵉ le-ℚ-Propᵉ aᵉ rᵉ)
    αᵉ aᵉ bᵉ =
      elim-existsᵉ
        ( ∃ᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ rᵉ bᵉ ∧ᵉ le-ℚ-Propᵉ aᵉ rᵉ))
        ( λ rᵉ ( pᵉ ,ᵉ qᵉ) → intro-existsᵉ rᵉ ( qᵉ ,ᵉ pᵉ))
```

### The canonical map from `ℚ` to `ℝ`

```agda
real-ℚᵉ : ℚᵉ → ℝᵉ lzero
real-ℚᵉ xᵉ =
  real-dedekind-cutᵉ
    ( λ (qᵉ : ℚᵉ) → le-ℚ-Propᵉ qᵉ xᵉ)
    ( λ (rᵉ : ℚᵉ) → le-ℚ-Propᵉ xᵉ rᵉ)
    ( is-dedekind-cut-le-ℚᵉ xᵉ)
```

### The property of being a rational real number

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ) (pᵉ : ℚᵉ)
  where

  is-rational-ℝ-Propᵉ : Propᵉ lᵉ
  is-rational-ℝ-Propᵉ =
    (¬'ᵉ (lower-cut-ℝᵉ xᵉ pᵉ)) ∧ᵉ (¬'ᵉ (upper-cut-ℝᵉ xᵉ pᵉ))

  is-rational-ℝᵉ : UUᵉ lᵉ
  is-rational-ℝᵉ = type-Propᵉ is-rational-ℝ-Propᵉ
```

```agda
all-eq-is-rational-ℝᵉ :
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ) (pᵉ qᵉ : ℚᵉ) →
  is-rational-ℝᵉ xᵉ pᵉ →
  is-rational-ℝᵉ xᵉ qᵉ →
  pᵉ ＝ᵉ qᵉ
all-eq-is-rational-ℝᵉ xᵉ pᵉ qᵉ Hᵉ H'ᵉ =
  trichotomy-le-ℚᵉ pᵉ qᵉ left-caseᵉ idᵉ right-caseᵉ
  where
  left-caseᵉ : le-ℚᵉ pᵉ qᵉ → pᵉ ＝ᵉ qᵉ
  left-caseᵉ Iᵉ =
    ex-falsoᵉ
      ( elim-disjunctionᵉ
        ( empty-Propᵉ)
        ( pr1ᵉ Hᵉ)
        ( pr2ᵉ H'ᵉ)
        ( is-located-lower-upper-cut-ℝᵉ xᵉ pᵉ qᵉ Iᵉ))

  right-caseᵉ : le-ℚᵉ qᵉ pᵉ → pᵉ ＝ᵉ qᵉ
  right-caseᵉ Iᵉ =
    ex-falsoᵉ
      ( elim-disjunctionᵉ
        ( empty-Propᵉ)
        ( pr1ᵉ H'ᵉ)
        ( pr2ᵉ Hᵉ)
        ( is-located-lower-upper-cut-ℝᵉ xᵉ qᵉ pᵉ Iᵉ))

is-prop-rational-realᵉ : {lᵉ : Level} (xᵉ : ℝᵉ lᵉ) → is-propᵉ (Σᵉ ℚᵉ (is-rational-ℝᵉ xᵉ))
is-prop-rational-realᵉ xᵉ =
  is-prop-all-elements-equalᵉ
    ( λ pᵉ qᵉ →
      eq-type-subtypeᵉ
        ( is-rational-ℝ-Propᵉ xᵉ)
        ( all-eq-is-rational-ℝᵉ xᵉ (pr1ᵉ pᵉ) (pr1ᵉ qᵉ) (pr2ᵉ pᵉ) (pr2ᵉ qᵉ)))
```

### The subtype of rational reals

```agda
subtype-rational-realᵉ : {lᵉ : Level} → ℝᵉ lᵉ → Propᵉ lᵉ
subtype-rational-realᵉ xᵉ =
  Σᵉ ℚᵉ (is-rational-ℝᵉ xᵉ) ,ᵉ is-prop-rational-realᵉ xᵉ

Rational-ℝᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Rational-ℝᵉ lᵉ =
  type-subtypeᵉ subtype-rational-realᵉ

module _
  {lᵉ : Level} (xᵉ : Rational-ℝᵉ lᵉ)
  where

  real-rational-ℝᵉ : ℝᵉ lᵉ
  real-rational-ℝᵉ = pr1ᵉ xᵉ

  rational-rational-ℝᵉ : ℚᵉ
  rational-rational-ℝᵉ = pr1ᵉ (pr2ᵉ xᵉ)

  is-rational-rational-ℝᵉ : is-rational-ℝᵉ real-rational-ℝᵉ rational-rational-ℝᵉ
  is-rational-rational-ℝᵉ = pr2ᵉ (pr2ᵉ xᵉ)
```

## Properties

### The real embedding of a rational number is rational

```agda
is-rational-real-ℚᵉ : (pᵉ : ℚᵉ) → is-rational-ℝᵉ (real-ℚᵉ pᵉ) pᵉ
is-rational-real-ℚᵉ pᵉ = (irreflexive-le-ℚᵉ pᵉ ,ᵉ irreflexive-le-ℚᵉ pᵉ)
```

### Rational real numbers are embedded rationals

```agda
eq-real-rational-is-rational-ℝᵉ :
  (xᵉ : ℝᵉ lzero) (qᵉ : ℚᵉ) (Hᵉ : is-rational-ℝᵉ xᵉ qᵉ) → real-ℚᵉ qᵉ ＝ᵉ xᵉ
eq-real-rational-is-rational-ℝᵉ xᵉ qᵉ Hᵉ =
  eq-eq-lower-cut-ℝᵉ
    ( real-ℚᵉ qᵉ)
    ( xᵉ)
    ( eq-has-same-elements-subtypeᵉ
      ( λ pᵉ → le-ℚ-Propᵉ pᵉ qᵉ)
      ( lower-cut-ℝᵉ xᵉ)
      ( λ rᵉ →
        pairᵉ
          ( λ Iᵉ →
            elim-disjunctionᵉ
              ( lower-cut-ℝᵉ xᵉ rᵉ)
              ( idᵉ)
              ( λ H'ᵉ → ex-falsoᵉ (pr2ᵉ Hᵉ H'ᵉ))
              ( is-located-lower-upper-cut-ℝᵉ xᵉ rᵉ qᵉ Iᵉ))
          ( trichotomy-le-ℚᵉ rᵉ qᵉ
            ( λ Iᵉ _ → Iᵉ)
            ( λ Eᵉ H'ᵉ → ex-falsoᵉ (pr1ᵉ (trᵉ (is-rational-ℝᵉ xᵉ) (invᵉ Eᵉ) Hᵉ) H'ᵉ))
            ( λ Iᵉ H'ᵉ → ex-falsoᵉ (pr1ᵉ Hᵉ (le-lower-cut-ℝᵉ xᵉ qᵉ rᵉ Iᵉ H'ᵉ))))))
```

### The cannonical map from rationals to rational reals

```agda
rational-real-ℚᵉ : ℚᵉ → Rational-ℝᵉ lzero
rational-real-ℚᵉ qᵉ = (real-ℚᵉ qᵉ ,ᵉ qᵉ ,ᵉ is-rational-real-ℚᵉ qᵉ)
```

### The rationals and rational reals are equivalent

```agda
is-section-rational-real-ℚᵉ :
  (qᵉ : ℚᵉ) →
  rational-rational-ℝᵉ (rational-real-ℚᵉ qᵉ) ＝ᵉ qᵉ
is-section-rational-real-ℚᵉ qᵉ = reflᵉ

is-retraction-rational-real-ℚᵉ :
  (xᵉ : Rational-ℝᵉ lzero) →
  rational-real-ℚᵉ (rational-rational-ℝᵉ xᵉ) ＝ᵉ xᵉ
is-retraction-rational-real-ℚᵉ (xᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) =
  eq-type-subtypeᵉ
    subtype-rational-realᵉ
    ( apᵉ real-ℚᵉ αᵉ ∙ᵉ eq-real-rational-is-rational-ℝᵉ xᵉ qᵉ Hᵉ)
  where
    αᵉ : rational-rational-ℝᵉ (xᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) ＝ᵉ qᵉ
    αᵉ = reflᵉ

equiv-rational-realᵉ : Rational-ℝᵉ lzero ≃ᵉ ℚᵉ
pr1ᵉ equiv-rational-realᵉ = rational-rational-ℝᵉ
pr2ᵉ equiv-rational-realᵉ =
  section-rational-rational-ℝᵉ ,ᵉ retraction-rational-rational-ℝᵉ
  where
  section-rational-rational-ℝᵉ : sectionᵉ rational-rational-ℝᵉ
  section-rational-rational-ℝᵉ =
    (rational-real-ℚᵉ ,ᵉ is-section-rational-real-ℚᵉ)

  retraction-rational-rational-ℝᵉ : retractionᵉ rational-rational-ℝᵉ
  retraction-rational-rational-ℝᵉ =
    (rational-real-ℚᵉ ,ᵉ is-retraction-rational-real-ℚᵉ)
```