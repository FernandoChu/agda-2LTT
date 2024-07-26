# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.strict-inequality-rational-numbersᵉ

open import foundation.binary-transportᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.complements-subtypesᵉ
open import foundation.conjunctionᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-typesᵉ
open import foundation.universal-quantificationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "Dedekindᵉ cut"ᵉ Agda=is-dedekind-cutᵉ WD="dedekindᵉ cut"ᵉ WDID=Q851333ᵉ}}
consistsᵉ ofᵉ aᵉ [pair](foundation.dependent-pair-types.mdᵉ) `(Lᵉ ,ᵉ U)`ᵉ ofᵉ
[subtypes](foundation-core.subtypes.mdᵉ) ofᵉ
[theᵉ rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) `ℚ`,ᵉ
satisfyingᵉ theᵉ followingᵉ fourᵉ conditionsᵉ

1.ᵉ _Inhabitedness_.ᵉ Bothᵉ `L`ᵉ andᵉ `U`ᵉ areᵉ
   [inhabited](foundation.inhabited-subtypes.mdᵉ) subtypesᵉ ofᵉ `ℚ`.ᵉ
2.ᵉ _Roundedness_.ᵉ Aᵉ rationalᵉ numberᵉ `q`ᵉ isᵉ in `L`ᵉ
   [ifᵉ andᵉ onlyᵉ if](foundation.logical-equivalences.mdᵉ) thereᵉ
   [exists](foundation.existential-quantification.mdᵉ) `qᵉ <ᵉ r`ᵉ suchᵉ thatᵉ `rᵉ ∈ᵉ L`,ᵉ
   andᵉ aᵉ rationalᵉ numberᵉ `r`ᵉ isᵉ in `U`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ thereᵉ existsᵉ `qᵉ <ᵉ r`ᵉ suchᵉ
   thatᵉ `qᵉ ∈ᵉ U`.ᵉ
3.ᵉ _Disjointness_.ᵉ `L`ᵉ andᵉ `U`ᵉ areᵉ disjointᵉ subsetsᵉ ofᵉ `ℚ`.ᵉ
4.ᵉ _Locatedness_.ᵉ Ifᵉ `qᵉ <ᵉ r`ᵉ thenᵉ `qᵉ ∈ᵉ L`ᵉ orᵉ `rᵉ ∈ᵉ U`.ᵉ

Theᵉ typeᵉ ofᵉ {{#conceptᵉ "Dedekindᵉ realᵉ numbers"ᵉ Agda=ℝᵉ}} isᵉ theᵉ typeᵉ ofᵉ allᵉ
Dedekindᵉ cuts.ᵉ Theᵉ Dedekindᵉ realᵉ numbersᵉ willᵉ beᵉ takenᵉ asᵉ theᵉ standardᵉ
definitionᵉ ofᵉ theᵉ realᵉ numbersᵉ in theᵉ `agda-unimath`ᵉ library.ᵉ

## Definition

### Dedekind cuts

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : subtypeᵉ l1ᵉ ℚᵉ) (Uᵉ : subtypeᵉ l2ᵉ ℚᵉ)
  where

  is-dedekind-cut-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-dedekind-cut-Propᵉ =
    conjunction-Propᵉ
      ( (∃ᵉ ℚᵉ Lᵉ) ∧ᵉ (∃ᵉ ℚᵉ Uᵉ))
      ( conjunction-Propᵉ
        ( conjunction-Propᵉ
          ( ∀'ᵉ ℚᵉ ( λ qᵉ → Lᵉ qᵉ ⇔ᵉ ∃ᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ qᵉ rᵉ ∧ᵉ Lᵉ rᵉ)))
          ( ∀'ᵉ ℚᵉ ( λ rᵉ → Uᵉ rᵉ ⇔ᵉ ∃ᵉ ℚᵉ (λ qᵉ → le-ℚ-Propᵉ qᵉ rᵉ ∧ᵉ Uᵉ qᵉ))))
        ( conjunction-Propᵉ
          ( ∀'ᵉ ℚᵉ (λ qᵉ → ¬'ᵉ (Lᵉ qᵉ ∧ᵉ Uᵉ qᵉ)))
          ( ∀'ᵉ ℚᵉ (λ qᵉ → ∀'ᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ qᵉ rᵉ ⇒ᵉ (Lᵉ qᵉ ∨ᵉ Uᵉ rᵉ))))))

  is-dedekind-cutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-dedekind-cutᵉ = type-Propᵉ is-dedekind-cut-Propᵉ

  is-prop-is-dedekind-cutᵉ : is-propᵉ is-dedekind-cutᵉ
  is-prop-is-dedekind-cutᵉ = is-prop-type-Propᵉ is-dedekind-cut-Propᵉ
```

### The Dedekind real numbers

```agda
ℝᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
ℝᵉ lᵉ = Σᵉ (subtypeᵉ lᵉ ℚᵉ) (λ Lᵉ → Σᵉ (subtypeᵉ lᵉ ℚᵉ) (is-dedekind-cutᵉ Lᵉ))

real-dedekind-cutᵉ : {lᵉ : Level} (Lᵉ Uᵉ : subtypeᵉ lᵉ ℚᵉ) → is-dedekind-cutᵉ Lᵉ Uᵉ → ℝᵉ lᵉ
real-dedekind-cutᵉ Lᵉ Uᵉ Hᵉ = Lᵉ ,ᵉ Uᵉ ,ᵉ Hᵉ

module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ)
  where

  lower-cut-ℝᵉ : subtypeᵉ lᵉ ℚᵉ
  lower-cut-ℝᵉ = pr1ᵉ xᵉ

  upper-cut-ℝᵉ : subtypeᵉ lᵉ ℚᵉ
  upper-cut-ℝᵉ = pr1ᵉ (pr2ᵉ xᵉ)

  is-in-lower-cut-ℝᵉ : ℚᵉ → UUᵉ lᵉ
  is-in-lower-cut-ℝᵉ = is-in-subtypeᵉ lower-cut-ℝᵉ

  is-in-upper-cut-ℝᵉ : ℚᵉ → UUᵉ lᵉ
  is-in-upper-cut-ℝᵉ = is-in-subtypeᵉ upper-cut-ℝᵉ

  is-dedekind-cut-cut-ℝᵉ : is-dedekind-cutᵉ lower-cut-ℝᵉ upper-cut-ℝᵉ
  is-dedekind-cut-cut-ℝᵉ = pr2ᵉ (pr2ᵉ xᵉ)

  is-inhabited-lower-cut-ℝᵉ : existsᵉ ℚᵉ lower-cut-ℝᵉ
  is-inhabited-lower-cut-ℝᵉ = pr1ᵉ (pr1ᵉ is-dedekind-cut-cut-ℝᵉ)

  is-inhabited-upper-cut-ℝᵉ : existsᵉ ℚᵉ upper-cut-ℝᵉ
  is-inhabited-upper-cut-ℝᵉ = pr2ᵉ (pr1ᵉ is-dedekind-cut-cut-ℝᵉ)

  is-rounded-lower-cut-ℝᵉ :
    (qᵉ : ℚᵉ) →
    is-in-lower-cut-ℝᵉ qᵉ ↔ᵉ
    existsᵉ ℚᵉ (λ rᵉ → (le-ℚ-Propᵉ qᵉ rᵉ) ∧ᵉ (lower-cut-ℝᵉ rᵉ))
  is-rounded-lower-cut-ℝᵉ =
    pr1ᵉ (pr1ᵉ (pr2ᵉ is-dedekind-cut-cut-ℝᵉ))

  is-rounded-upper-cut-ℝᵉ :
    (rᵉ : ℚᵉ) →
    is-in-upper-cut-ℝᵉ rᵉ ↔ᵉ
    existsᵉ ℚᵉ (λ qᵉ → (le-ℚ-Propᵉ qᵉ rᵉ) ∧ᵉ (upper-cut-ℝᵉ qᵉ))
  is-rounded-upper-cut-ℝᵉ =
    pr2ᵉ (pr1ᵉ (pr2ᵉ is-dedekind-cut-cut-ℝᵉ))

  is-disjoint-cut-ℝᵉ : (qᵉ : ℚᵉ) → ¬ᵉ (is-in-lower-cut-ℝᵉ qᵉ ×ᵉ is-in-upper-cut-ℝᵉ qᵉ)
  is-disjoint-cut-ℝᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ is-dedekind-cut-cut-ℝᵉ))

  is-located-lower-upper-cut-ℝᵉ :
    (qᵉ rᵉ : ℚᵉ) → le-ℚᵉ qᵉ rᵉ →
    type-disjunction-Propᵉ (lower-cut-ℝᵉ qᵉ) (upper-cut-ℝᵉ rᵉ)
  is-located-lower-upper-cut-ℝᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ is-dedekind-cut-cut-ℝᵉ))

  cut-ℝᵉ : subtypeᵉ lᵉ ℚᵉ
  cut-ℝᵉ qᵉ =
    coproduct-Propᵉ
      ( lower-cut-ℝᵉ qᵉ)
      ( upper-cut-ℝᵉ qᵉ)
      ( ev-pairᵉ ( is-disjoint-cut-ℝᵉ qᵉ))

  is-in-cut-ℝᵉ : ℚᵉ → UUᵉ lᵉ
  is-in-cut-ℝᵉ = is-in-subtypeᵉ cut-ℝᵉ
```

## Properties

### The Dedekind real numbers form a set

```agda
abstract
  is-set-ℝᵉ : (lᵉ : Level) → is-setᵉ (ℝᵉ lᵉ)
  is-set-ℝᵉ lᵉ =
    is-set-Σᵉ
      ( is-set-function-typeᵉ (is-trunc-Truncated-Typeᵉ neg-one-𝕋ᵉ))
      ( λ xᵉ →
        is-set-Σᵉ
          ( is-set-function-typeᵉ (is-trunc-Truncated-Typeᵉ neg-one-𝕋ᵉ))
          ( λ yᵉ →
            ( is-set-is-propᵉ
              ( is-prop-type-Propᵉ
                ( is-dedekind-cut-Propᵉ xᵉ yᵉ)))))

ℝ-Setᵉ : (lᵉ : Level) → Setᵉ (lsuc lᵉ)
ℝ-Setᵉ lᵉ = ℝᵉ lᵉ ,ᵉ is-set-ℝᵉ lᵉ
```

## Properties of lower/upper Dedekind cuts

### Lower and upper Dedekind cuts are closed under the standard ordering on the rationals

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ) (pᵉ qᵉ : ℚᵉ)
  where

  le-lower-cut-ℝᵉ :
    le-ℚᵉ pᵉ qᵉ →
    is-in-lower-cut-ℝᵉ xᵉ qᵉ →
    is-in-lower-cut-ℝᵉ xᵉ pᵉ
  le-lower-cut-ℝᵉ Hᵉ H'ᵉ =
    ind-trunc-Propᵉ
      ( λ sᵉ → lower-cut-ℝᵉ xᵉ pᵉ)
      ( rec-coproductᵉ
          ( idᵉ)
          ( λ Iᵉ → ex-falsoᵉ (is-disjoint-cut-ℝᵉ xᵉ qᵉ (H'ᵉ ,ᵉ Iᵉ))))
      ( is-located-lower-upper-cut-ℝᵉ xᵉ pᵉ qᵉ Hᵉ)

  leq-lower-cut-ℝᵉ :
    leq-ℚᵉ pᵉ qᵉ →
    is-in-lower-cut-ℝᵉ xᵉ qᵉ →
    is-in-lower-cut-ℝᵉ xᵉ pᵉ
  leq-lower-cut-ℝᵉ Hᵉ H'ᵉ =
    rec-coproductᵉ
      ( λ sᵉ → le-lower-cut-ℝᵉ sᵉ H'ᵉ)
      ( λ Iᵉ →
        trᵉ
          ( is-in-lower-cut-ℝᵉ xᵉ)
          ( antisymmetric-leq-ℚᵉ qᵉ pᵉ Iᵉ Hᵉ)
          ( H'ᵉ))
      ( decide-le-leq-ℚᵉ pᵉ qᵉ)

  le-upper-cut-ℝᵉ :
    le-ℚᵉ pᵉ qᵉ →
    is-in-upper-cut-ℝᵉ xᵉ pᵉ →
    is-in-upper-cut-ℝᵉ xᵉ qᵉ
  le-upper-cut-ℝᵉ Hᵉ H'ᵉ =
    ind-trunc-Propᵉ
      ( λ sᵉ → upper-cut-ℝᵉ xᵉ qᵉ)
      ( rec-coproductᵉ
        ( λ Iᵉ → ex-falsoᵉ (is-disjoint-cut-ℝᵉ xᵉ pᵉ ( Iᵉ ,ᵉ H'ᵉ)))
        ( idᵉ))
      ( is-located-lower-upper-cut-ℝᵉ xᵉ pᵉ qᵉ Hᵉ)

  leq-upper-cut-ℝᵉ :
    leq-ℚᵉ pᵉ qᵉ →
    is-in-upper-cut-ℝᵉ xᵉ pᵉ →
    is-in-upper-cut-ℝᵉ xᵉ qᵉ
  leq-upper-cut-ℝᵉ Hᵉ H'ᵉ =
    rec-coproductᵉ
      ( λ sᵉ → le-upper-cut-ℝᵉ sᵉ H'ᵉ)
      ( λ Iᵉ →
        trᵉ
          ( is-in-upper-cut-ℝᵉ xᵉ)
          ( antisymmetric-leq-ℚᵉ pᵉ qᵉ Hᵉ Iᵉ)
          ( H'ᵉ))
      ( decide-le-leq-ℚᵉ pᵉ qᵉ)
```

### Elements of the lower cut are lower bounds of the upper cut

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ) (pᵉ qᵉ : ℚᵉ)
  where

  le-lower-upper-cut-ℝᵉ :
    is-in-lower-cut-ℝᵉ xᵉ pᵉ →
    is-in-upper-cut-ℝᵉ xᵉ qᵉ →
    le-ℚᵉ pᵉ qᵉ
  le-lower-upper-cut-ℝᵉ Hᵉ H'ᵉ =
    rec-coproductᵉ
      ( idᵉ)
      ( λ Iᵉ →
        ex-falsoᵉ
          ( is-disjoint-cut-ℝᵉ xᵉ pᵉ
              ( Hᵉ ,ᵉ leq-upper-cut-ℝᵉ xᵉ qᵉ pᵉ Iᵉ H'ᵉ)))
      ( decide-le-leq-ℚᵉ pᵉ qᵉ)
```

### Characterisation of each cut by the other

#### The lower cut is the subtype of rationals bounded above by some element of the complement of the upper cut

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ)
  where

  is-lower-complement-upper-cut-ℝ-Propᵉ : (pᵉ qᵉ : ℚᵉ) → Propᵉ lᵉ
  is-lower-complement-upper-cut-ℝ-Propᵉ pᵉ qᵉ =
    ( le-ℚ-Propᵉ pᵉ qᵉ) ∧ᵉ (¬'ᵉ (upper-cut-ℝᵉ xᵉ qᵉ))

  lower-complement-upper-cut-ℝᵉ : subtypeᵉ lᵉ ℚᵉ
  lower-complement-upper-cut-ℝᵉ pᵉ =
    ∃ᵉ ℚᵉ (is-lower-complement-upper-cut-ℝ-Propᵉ pᵉ)
```

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ)
  where

  subset-lower-cut-lower-complement-upper-cut-ℝᵉ :
    lower-complement-upper-cut-ℝᵉ xᵉ ⊆ᵉ lower-cut-ℝᵉ xᵉ
  subset-lower-cut-lower-complement-upper-cut-ℝᵉ pᵉ =
    elim-existsᵉ
      ( lower-cut-ℝᵉ xᵉ pᵉ)
      ( λ qᵉ Iᵉ →
        map-right-unit-law-disjunction-is-empty-Propᵉ
          ( lower-cut-ℝᵉ xᵉ pᵉ)
          ( upper-cut-ℝᵉ xᵉ qᵉ)
          ( pr2ᵉ Iᵉ)
          ( is-located-lower-upper-cut-ℝᵉ xᵉ pᵉ qᵉ ( pr1ᵉ Iᵉ)))

  subset-lower-complement-upper-cut-lower-cut-ℝᵉ :
    lower-cut-ℝᵉ xᵉ ⊆ᵉ lower-complement-upper-cut-ℝᵉ xᵉ
  subset-lower-complement-upper-cut-lower-cut-ℝᵉ pᵉ Hᵉ =
    elim-existsᵉ
      ( lower-complement-upper-cut-ℝᵉ xᵉ pᵉ)
      ( λ qᵉ Iᵉ →
        intro-existsᵉ
          ( qᵉ)
          ( map-productᵉ
            ( idᵉ)
            ( λ Lᵉ Uᵉ → is-disjoint-cut-ℝᵉ xᵉ qᵉ (Lᵉ ,ᵉ Uᵉ))
            ( Iᵉ)))
      ( pr1ᵉ (is-rounded-lower-cut-ℝᵉ xᵉ pᵉ) Hᵉ)

  eq-lower-cut-lower-complement-upper-cut-ℝᵉ :
    lower-complement-upper-cut-ℝᵉ xᵉ ＝ᵉ lower-cut-ℝᵉ xᵉ
  eq-lower-cut-lower-complement-upper-cut-ℝᵉ =
    antisymmetric-leq-subtypeᵉ
      ( lower-complement-upper-cut-ℝᵉ xᵉ)
      ( lower-cut-ℝᵉ xᵉ)
      ( subset-lower-cut-lower-complement-upper-cut-ℝᵉ)
      ( subset-lower-complement-upper-cut-lower-cut-ℝᵉ)
```

#### The upper cut is the subtype of rationals bounded below by some element of the complement of the lower cut

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ)
  where

  is-upper-complement-lower-cut-ℝ-Propᵉ : (qᵉ pᵉ : ℚᵉ) → Propᵉ lᵉ
  is-upper-complement-lower-cut-ℝ-Propᵉ qᵉ pᵉ =
    (le-ℚ-Propᵉ pᵉ qᵉ) ∧ᵉ (¬'ᵉ (lower-cut-ℝᵉ xᵉ pᵉ))

  upper-complement-lower-cut-ℝᵉ : subtypeᵉ lᵉ ℚᵉ
  upper-complement-lower-cut-ℝᵉ qᵉ =
    ∃ᵉ ℚᵉ (is-upper-complement-lower-cut-ℝ-Propᵉ qᵉ)
```

```agda
module _
  {lᵉ : Level} (xᵉ : ℝᵉ lᵉ)
  where

  subset-upper-cut-upper-complement-lower-cut-ℝᵉ :
    upper-complement-lower-cut-ℝᵉ xᵉ ⊆ᵉ upper-cut-ℝᵉ xᵉ
  subset-upper-cut-upper-complement-lower-cut-ℝᵉ qᵉ =
    elim-existsᵉ
      ( upper-cut-ℝᵉ xᵉ qᵉ)
      ( λ pᵉ Iᵉ →
        map-left-unit-law-disjunction-is-empty-Propᵉ
          ( lower-cut-ℝᵉ xᵉ pᵉ)
          ( upper-cut-ℝᵉ xᵉ qᵉ)
          ( pr2ᵉ Iᵉ)
          ( is-located-lower-upper-cut-ℝᵉ xᵉ pᵉ qᵉ ( pr1ᵉ Iᵉ)))

  subset-upper-complement-lower-cut-upper-cut-ℝᵉ :
    upper-cut-ℝᵉ xᵉ ⊆ᵉ upper-complement-lower-cut-ℝᵉ xᵉ
  subset-upper-complement-lower-cut-upper-cut-ℝᵉ qᵉ Hᵉ =
    elim-existsᵉ
      ( upper-complement-lower-cut-ℝᵉ xᵉ qᵉ)
      ( λ pᵉ Iᵉ →
        intro-existsᵉ
          ( pᵉ)
          ( map-productᵉ
            ( idᵉ)
            ( λ Uᵉ Lᵉ → is-disjoint-cut-ℝᵉ xᵉ pᵉ (Lᵉ ,ᵉ Uᵉ))
            ( Iᵉ)))
      ( pr1ᵉ (is-rounded-upper-cut-ℝᵉ xᵉ qᵉ) Hᵉ)

  eq-upper-cut-upper-complement-lower-cut-ℝᵉ :
    upper-complement-lower-cut-ℝᵉ xᵉ ＝ᵉ upper-cut-ℝᵉ xᵉ
  eq-upper-cut-upper-complement-lower-cut-ℝᵉ =
    antisymmetric-leq-subtypeᵉ
      ( upper-complement-lower-cut-ℝᵉ xᵉ)
      ( upper-cut-ℝᵉ xᵉ)
      ( subset-upper-cut-upper-complement-lower-cut-ℝᵉ)
      ( subset-upper-complement-lower-cut-upper-cut-ℝᵉ)
```

### The lower/upper cut of a real determines the other

```agda
module _
  {lᵉ : Level} (xᵉ yᵉ : ℝᵉ lᵉ)
  where

  subset-lower-cut-upper-cut-ℝᵉ :
    upper-cut-ℝᵉ yᵉ ⊆ᵉ upper-cut-ℝᵉ xᵉ → lower-cut-ℝᵉ xᵉ ⊆ᵉ lower-cut-ℝᵉ yᵉ
  subset-lower-cut-upper-cut-ℝᵉ Hᵉ =
    binary-trᵉ
      ( _⊆ᵉ_)
      ( eq-lower-cut-lower-complement-upper-cut-ℝᵉ xᵉ)
      ( eq-lower-cut-lower-complement-upper-cut-ℝᵉ yᵉ)
      ( λ pᵉ →
        elim-existsᵉ
          ( lower-complement-upper-cut-ℝᵉ yᵉ pᵉ)
          ( λ qᵉ → intro-existsᵉ qᵉ ∘ᵉ totᵉ (λ _ Kᵉ → Kᵉ ∘ᵉ Hᵉ qᵉ)))

  subset-upper-cut-lower-cut-ℝᵉ :
    lower-cut-ℝᵉ xᵉ ⊆ᵉ lower-cut-ℝᵉ yᵉ → upper-cut-ℝᵉ yᵉ ⊆ᵉ upper-cut-ℝᵉ xᵉ
  subset-upper-cut-lower-cut-ℝᵉ Hᵉ =
    binary-trᵉ
      ( _⊆ᵉ_)
      ( eq-upper-cut-upper-complement-lower-cut-ℝᵉ yᵉ)
      ( eq-upper-cut-upper-complement-lower-cut-ℝᵉ xᵉ)
      ( λ qᵉ →
        elim-existsᵉ
          ( upper-complement-lower-cut-ℝᵉ xᵉ qᵉ)
          ( λ pᵉ → intro-existsᵉ pᵉ ∘ᵉ totᵉ (λ _ Kᵉ → Kᵉ ∘ᵉ Hᵉ pᵉ)))

module _
  {lᵉ : Level} (xᵉ yᵉ : ℝᵉ lᵉ)
  where

  eq-lower-cut-eq-upper-cut-ℝᵉ :
    upper-cut-ℝᵉ xᵉ ＝ᵉ upper-cut-ℝᵉ yᵉ → lower-cut-ℝᵉ xᵉ ＝ᵉ lower-cut-ℝᵉ yᵉ
  eq-lower-cut-eq-upper-cut-ℝᵉ Hᵉ =
    antisymmetric-leq-subtypeᵉ
      ( lower-cut-ℝᵉ xᵉ)
      ( lower-cut-ℝᵉ yᵉ)
      ( subset-lower-cut-upper-cut-ℝᵉ xᵉ yᵉ
        ( pr2ᵉ ∘ᵉ has-same-elements-eq-subtypeᵉ
          ( upper-cut-ℝᵉ xᵉ)
          ( upper-cut-ℝᵉ yᵉ)
          ( Hᵉ)))
      ( subset-lower-cut-upper-cut-ℝᵉ yᵉ xᵉ
        ( pr1ᵉ ∘ᵉ has-same-elements-eq-subtypeᵉ
          ( upper-cut-ℝᵉ xᵉ)
          ( upper-cut-ℝᵉ yᵉ)
          ( Hᵉ)))

  eq-upper-cut-eq-lower-cut-ℝᵉ :
    lower-cut-ℝᵉ xᵉ ＝ᵉ lower-cut-ℝᵉ yᵉ → upper-cut-ℝᵉ xᵉ ＝ᵉ upper-cut-ℝᵉ yᵉ
  eq-upper-cut-eq-lower-cut-ℝᵉ Hᵉ =
    antisymmetric-leq-subtypeᵉ
      ( upper-cut-ℝᵉ xᵉ)
      ( upper-cut-ℝᵉ yᵉ)
      ( subset-upper-cut-lower-cut-ℝᵉ yᵉ xᵉ
        ( pr2ᵉ ∘ᵉ has-same-elements-eq-subtypeᵉ
          ( lower-cut-ℝᵉ xᵉ)
          ( lower-cut-ℝᵉ yᵉ)
          ( Hᵉ)))
      ( subset-upper-cut-lower-cut-ℝᵉ xᵉ yᵉ
        ( pr1ᵉ ∘ᵉ has-same-elements-eq-subtypeᵉ
          ( lower-cut-ℝᵉ xᵉ)
          ( lower-cut-ℝᵉ yᵉ)
          ( Hᵉ)))
```

### The map from a real number to its lower cut is an embedding

```agda
module _
  {lᵉ : Level} (Lᵉ : subtypeᵉ lᵉ ℚᵉ)
  where

  has-upper-cut-Propᵉ : Propᵉ (lsuc lᵉ)
  has-upper-cut-Propᵉ =
    pairᵉ
      ( Σᵉ (subtypeᵉ lᵉ ℚᵉ) (is-dedekind-cutᵉ Lᵉ))
      ( is-prop-all-elements-equalᵉ
        ( λ Uᵉ U'ᵉ →
          eq-type-subtypeᵉ
            ( is-dedekind-cut-Propᵉ Lᵉ)
            ( eq-upper-cut-eq-lower-cut-ℝᵉ
              ( pairᵉ Lᵉ Uᵉ)
              ( pairᵉ Lᵉ U'ᵉ)
              ( reflᵉ))))

is-emb-lower-cutᵉ : {lᵉ : Level} → is-embᵉ (lower-cut-ℝᵉ {lᵉ})
is-emb-lower-cutᵉ = is-emb-inclusion-subtypeᵉ has-upper-cut-Propᵉ
```

### Two real numbers with the same lower/upper cut are equal

```agda
module _
  {lᵉ : Level} (xᵉ yᵉ : ℝᵉ lᵉ)
  where

  eq-eq-lower-cut-ℝᵉ : lower-cut-ℝᵉ xᵉ ＝ᵉ lower-cut-ℝᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-eq-lower-cut-ℝᵉ = eq-type-subtypeᵉ has-upper-cut-Propᵉ

  eq-eq-upper-cut-ℝᵉ : upper-cut-ℝᵉ xᵉ ＝ᵉ upper-cut-ℝᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-eq-upper-cut-ℝᵉ = eq-eq-lower-cut-ℝᵉ ∘ᵉ (eq-lower-cut-eq-upper-cut-ℝᵉ xᵉ yᵉ)
```

## References

Thisᵉ pageᵉ followsᵉ partsᵉ ofᵉ Sectionᵉ 11.2ᵉ in {{#citeᵉ UF13}}.ᵉ

{{#bibliographyᵉ}}

## External links

-ᵉ [DedekindReals.Type](https://www.cs.bham.ac.uk/~mhe/TypeTopology/DedekindReals.Type.htmlᵉ)
  atᵉ TypeTopologyᵉ
-ᵉ [Dedekindᵉ cut](https://ncatlab.org/nlab/show/Dedekind+cutᵉ) atᵉ $n$Labᵉ
-ᵉ [Dedekindᵉ cut](https://en.wikipedia.org/wiki/Dedekind_cutᵉ) atᵉ Wikipediaᵉ
-ᵉ [Constructionᵉ ofᵉ theᵉ realᵉ numbersᵉ byᵉ Dedekindᵉ cuts](https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cutsᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Dedekindᵉ cut](https://www.britannica.com/science/Dedekind-cutᵉ) atᵉ Britannicaᵉ