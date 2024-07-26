# Double negation

```agda
module foundation.double-negationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Definition

Weᵉ defineᵉ doubleᵉ negationᵉ andᵉ tripleᵉ negationᵉ

```agda
infix 25 ¬¬ᵉ_ ¬¬¬ᵉ_

¬¬ᵉ_ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
¬¬ᵉ Pᵉ = ¬ᵉ (¬ᵉ Pᵉ)

¬¬¬ᵉ_ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
¬¬¬ᵉ Pᵉ = ¬ᵉ (¬ᵉ (¬ᵉ Pᵉ))
```

Weᵉ alsoᵉ defineᵉ theᵉ introductionᵉ ruleᵉ forᵉ doubleᵉ negation,ᵉ andᵉ theᵉ actionᵉ onᵉ mapsᵉ
ofᵉ doubleᵉ negation.ᵉ

```agda
intro-double-negationᵉ : {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → Pᵉ → ¬¬ᵉ Pᵉ
intro-double-negationᵉ pᵉ fᵉ = fᵉ pᵉ

map-double-negationᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} → (Pᵉ → Qᵉ) → ¬¬ᵉ Pᵉ → ¬¬ᵉ Qᵉ
map-double-negationᵉ fᵉ = map-negᵉ (map-negᵉ fᵉ)
```

## Properties

### The double negation of a type is a proposition

```agda
double-negation-type-Propᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → Propᵉ lᵉ
double-negation-type-Propᵉ Aᵉ = neg-type-Propᵉ (¬ᵉ Aᵉ)

double-negation-Propᵉ :
  {lᵉ : Level} (Pᵉ : Propᵉ lᵉ) → Propᵉ lᵉ
double-negation-Propᵉ Pᵉ = double-negation-type-Propᵉ (type-Propᵉ Pᵉ)

is-prop-double-negationᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ (¬¬ᵉ Aᵉ)
is-prop-double-negationᵉ = is-prop-negᵉ

infix 25 ¬¬'ᵉ_

¬¬'ᵉ_ : {lᵉ : Level} (Pᵉ : Propᵉ lᵉ) → Propᵉ lᵉ
¬¬'ᵉ_ = double-negation-Propᵉ
```

### Double negations of classical laws

```agda
double-negation-double-negation-elimᵉ :
  {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → ¬¬ᵉ (¬¬ᵉ Pᵉ → Pᵉ)
double-negation-double-negation-elimᵉ {Pᵉ = Pᵉ} fᵉ =
  ( λ (npᵉ : ¬ᵉ Pᵉ) → fᵉ (λ (nnpᵉ : ¬¬ᵉ Pᵉ) → ex-falsoᵉ (nnpᵉ npᵉ)))
  ( λ (pᵉ : Pᵉ) → fᵉ (λ (nnpᵉ : ¬¬ᵉ Pᵉ) → pᵉ))

double-negation-Peirces-lawᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} → ¬¬ᵉ (((Pᵉ → Qᵉ) → Pᵉ) → Pᵉ)
double-negation-Peirces-lawᵉ {Pᵉ = Pᵉ} fᵉ =
  ( λ (npᵉ : ¬ᵉ Pᵉ) → fᵉ (λ hᵉ → hᵉ (λ pᵉ → ex-falsoᵉ (npᵉ pᵉ))))
  ( λ (pᵉ : Pᵉ) → fᵉ (λ _ → pᵉ))

double-negation-linearity-implicationᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} →
  ¬¬ᵉ ((Pᵉ → Qᵉ) +ᵉ (Qᵉ → Pᵉ))
double-negation-linearity-implicationᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ =
  ( λ (npᵉ : ¬ᵉ Pᵉ) →
    map-negᵉ (inlᵉ {Aᵉ = Pᵉ → Qᵉ} {Bᵉ = Qᵉ → Pᵉ}) fᵉ (λ pᵉ → ex-falsoᵉ (npᵉ pᵉ)))
  ( λ (pᵉ : Pᵉ) → map-negᵉ (inrᵉ {Aᵉ = Pᵉ → Qᵉ} {Bᵉ = Qᵉ → Pᵉ}) fᵉ (λ _ → pᵉ))
```

### Cases of double negation elimination

```agda
double-negation-elim-negᵉ : {lᵉ : Level} (Pᵉ : UUᵉ lᵉ) → ¬¬¬ᵉ Pᵉ → ¬ᵉ Pᵉ
double-negation-elim-negᵉ Pᵉ fᵉ pᵉ = fᵉ (λ gᵉ → gᵉ pᵉ)

double-negation-elim-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} →
  ¬¬ᵉ ((¬¬ᵉ Pᵉ) ×ᵉ (¬¬ᵉ Qᵉ)) → (¬¬ᵉ Pᵉ) ×ᵉ (¬¬ᵉ Qᵉ)
pr1ᵉ (double-negation-elim-productᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ) =
  double-negation-elim-negᵉ (¬ᵉ Pᵉ) (map-double-negationᵉ pr1ᵉ fᵉ)
pr2ᵉ (double-negation-elim-productᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ) =
  double-negation-elim-negᵉ (¬ᵉ Qᵉ) (map-double-negationᵉ pr2ᵉ fᵉ)

double-negation-elim-expᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} →
  ¬¬ᵉ (Pᵉ → ¬¬ᵉ Qᵉ) → (Pᵉ → ¬¬ᵉ Qᵉ)
double-negation-elim-expᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ pᵉ =
  double-negation-elim-negᵉ
    ( ¬ᵉ Qᵉ)
    ( map-double-negationᵉ (λ (gᵉ : Pᵉ → ¬¬ᵉ Qᵉ) → gᵉ pᵉ) fᵉ)

double-negation-elim-for-allᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : Pᵉ → UUᵉ l2ᵉ} →
  ¬¬ᵉ ((pᵉ : Pᵉ) → ¬¬ᵉ (Qᵉ pᵉ)) → (pᵉ : Pᵉ) → ¬¬ᵉ (Qᵉ pᵉ)
double-negation-elim-for-allᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ pᵉ =
  double-negation-elim-negᵉ
    ( ¬ᵉ (Qᵉ pᵉ))
    ( map-double-negationᵉ (λ (gᵉ : (uᵉ : Pᵉ) → ¬¬ᵉ (Qᵉ uᵉ)) → gᵉ pᵉ) fᵉ)
```

### Maps into double negations extend along `intro-double-negation`

```agda
double-negation-extendᵉ :
  {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} →
  (Pᵉ → ¬¬ᵉ Qᵉ) → (¬¬ᵉ Pᵉ → ¬¬ᵉ Qᵉ)
double-negation-extendᵉ {Pᵉ = Pᵉ} {Qᵉ = Qᵉ} fᵉ =
  double-negation-elim-negᵉ (¬ᵉ Qᵉ) ∘ᵉ (map-double-negationᵉ fᵉ)
```

### The double negation of a type is logically equivalent to the double negation of its propositional truncation

```agda
abstract
  double-negation-double-negation-type-trunc-Propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → ¬¬ᵉ (type-trunc-Propᵉ Aᵉ) → ¬¬ᵉ Aᵉ
  double-negation-double-negation-type-trunc-Propᵉ Aᵉ =
    double-negation-extendᵉ
      ( map-universal-property-trunc-Propᵉ
        ( double-negation-type-Propᵉ Aᵉ)
        ( intro-double-negationᵉ))

abstract
  double-negation-type-trunc-Prop-double-negationᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → ¬¬ᵉ Aᵉ → ¬¬ᵉ (type-trunc-Propᵉ Aᵉ)
  double-negation-type-trunc-Prop-double-negationᵉ =
    map-double-negationᵉ unit-trunc-Propᵉ
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}