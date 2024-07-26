# Negation

```agda
module foundation.negationᵉ where

open import foundation-core.negationᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ Curry-Howardᵉ interpretationᵉ ofᵉ negationᵉ in typeᵉ theoryᵉ isᵉ theᵉ interpretationᵉ
ofᵉ theᵉ propositionᵉ `Pᵉ ⇒ᵉ ⊥`ᵉ using propositionsᵉ asᵉ types.ᵉ Thus,ᵉ theᵉ negationᵉ ofᵉ aᵉ
typeᵉ `A`ᵉ isᵉ theᵉ typeᵉ `Aᵉ → empty`.ᵉ

## Properties

### The negation of a type is a proposition

```agda
is-prop-negᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ (¬ᵉ Aᵉ)
is-prop-negᵉ {Aᵉ = Aᵉ} = is-prop-function-typeᵉ is-prop-emptyᵉ

neg-type-Propᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l1ᵉ
neg-type-Propᵉ Aᵉ = ¬ᵉ Aᵉ ,ᵉ is-prop-negᵉ

neg-Propᵉ : {l1ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ l1ᵉ
neg-Propᵉ Pᵉ = neg-type-Propᵉ (type-Propᵉ Pᵉ)

type-neg-Propᵉ : {l1ᵉ : Level} → Propᵉ l1ᵉ → UUᵉ l1ᵉ
type-neg-Propᵉ Pᵉ = type-Propᵉ (neg-Propᵉ Pᵉ)

infix 25 ¬'ᵉ_

¬'ᵉ_ : {l1ᵉ : Level} → Propᵉ l1ᵉ → Propᵉ l1ᵉ
¬'ᵉ_ = neg-Propᵉ
```

### Reductio ad absurdum

```agda
reductio-ad-absurdumᵉ : {l1ᵉ l2ᵉ : Level} {Pᵉ : UUᵉ l1ᵉ} {Qᵉ : UUᵉ l2ᵉ} → Pᵉ → ¬ᵉ Pᵉ → Qᵉ
reductio-ad-absurdumᵉ pᵉ npᵉ = ex-falsoᵉ (npᵉ pᵉ)
```

### Equivalent types have equivalent negations

```agda
equiv-negᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
  (Xᵉ ≃ᵉ Yᵉ) → (¬ᵉ Xᵉ ≃ᵉ ¬ᵉ Yᵉ)
equiv-negᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} eᵉ =
  equiv-iff'ᵉ
    ( neg-type-Propᵉ Xᵉ)
    ( neg-type-Propᵉ Yᵉ)
    ( pairᵉ (map-negᵉ (map-inv-equivᵉ eᵉ)) (map-negᵉ (map-equivᵉ eᵉ)))
```

### Negation has no fixed points

```agda
no-fixed-points-negᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → ¬ᵉ (Aᵉ ↔ᵉ ¬ᵉ Aᵉ)
no-fixed-points-negᵉ Aᵉ (fᵉ ,ᵉ gᵉ) =
  ( λ (hᵉ : ¬ᵉ Aᵉ) → hᵉ (gᵉ hᵉ)) (λ (aᵉ : Aᵉ) → fᵉ aᵉ aᵉ)

abstract
  no-fixed-points-neg-Propᵉ :
    {lᵉ : Level} (Pᵉ : Propᵉ lᵉ) → ¬ᵉ (type-Propᵉ Pᵉ ↔ᵉ ¬ᵉ (type-Propᵉ Pᵉ))
  no-fixed-points-neg-Propᵉ Pᵉ = no-fixed-points-negᵉ (type-Propᵉ Pᵉ)
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [negation](https://ncatlab.org/nlab/show/negationᵉ) atᵉ $n$Labᵉ
-ᵉ [Negation](https://en.wikipedia.org/wiki/Negationᵉ) atᵉ Wikipediaᵉ