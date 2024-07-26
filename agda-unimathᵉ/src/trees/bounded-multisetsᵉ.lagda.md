# Bounded multisets

```agda
module trees.bounded-multisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import trees.empty-multisetsᵉ
open import trees.multisetsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Aᵉ [multiset](trees.multisets.mdᵉ) `X`ᵉ isᵉ saidᵉ to beᵉ ofᵉ **naturalᵉ height**ᵉ `0`ᵉ ifᵉ
`X`ᵉ hasᵉ noᵉ elements,ᵉ andᵉ ofᵉ naturalᵉ heightᵉ `n+1`ᵉ ifᵉ everyᵉ
[element](trees.elementhood-relation-w-types.mdᵉ) in `X`ᵉ isᵉ ofᵉ naturalᵉ heightᵉ
`n`.ᵉ Multisetsᵉ ofᵉ finiteᵉ naturalᵉ heightᵉ areᵉ saidᵉ to beᵉ **naturallyᵉ bounded**.ᵉ

Noteᵉ thatᵉ finiteᵉ multisets,ᵉ whichᵉ consistᵉ ofᵉ finitelyᵉ manyᵉ elements,ᵉ eachᵉ ofᵉ
whichᵉ areᵉ finiteᵉ multisets,ᵉ areᵉ automaticallyᵉ naturallyᵉ bounded.ᵉ Nonfiniteᵉ
multisets,ᵉ however,ᵉ needᵉ notᵉ beᵉ naturallyᵉ bounded.ᵉ

Weᵉ alsoᵉ noteᵉ thatᵉ thereᵉ shouldᵉ existᵉ aᵉ moreᵉ generalᵉ notionᵉ ofᵉ height,ᵉ in whichᵉ
heightsᵉ areᵉ measuredᵉ byᵉ upwardsᵉ closedᵉ subsetsᵉ ofᵉ theᵉ naturalᵉ numbers.ᵉ Thisᵉ isᵉ
whyᵉ weᵉ speakᵉ ofᵉ _naturallyᵉ_ boundedᵉ multisetsᵉ here.ᵉ Onᵉ theᵉ otherᵉ hand,ᵉ everyᵉ
multisetᵉ isᵉ boundedᵉ in thisᵉ moreᵉ generalᵉ sense,ᵉ andᵉ thisᵉ boundᵉ isᵉ unique.ᵉ

## Definitions

### The predicate of being a multiset of natural height `n`

```agda
module _
  {lᵉ : Level}
  where

  is-of-natural-height-𝕍ᵉ : ℕᵉ → 𝕍ᵉ lᵉ → UUᵉ lᵉ
  is-of-natural-height-𝕍ᵉ zero-ℕᵉ Xᵉ =
    is-empty-𝕍ᵉ Xᵉ
  is-of-natural-height-𝕍ᵉ (succ-ℕᵉ nᵉ) (tree-𝕎ᵉ Xᵉ Yᵉ) =
    (xᵉ : Xᵉ) → is-of-natural-height-𝕍ᵉ nᵉ (Yᵉ xᵉ)

  is-prop-is-of-natural-height-𝕍ᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : 𝕍ᵉ lᵉ) → is-propᵉ (is-of-natural-height-𝕍ᵉ nᵉ Xᵉ)
  is-prop-is-of-natural-height-𝕍ᵉ zero-ℕᵉ = is-property-is-empty-𝕍ᵉ
  is-prop-is-of-natural-height-𝕍ᵉ (succ-ℕᵉ nᵉ) (tree-𝕎ᵉ Xᵉ Yᵉ) =
    is-prop-Πᵉ (λ xᵉ → is-prop-is-of-natural-height-𝕍ᵉ nᵉ (Yᵉ xᵉ))

  is-of-natural-height-prop-𝕍ᵉ : ℕᵉ → 𝕍ᵉ lᵉ → Propᵉ lᵉ
  is-of-natural-height-prop-𝕍ᵉ nᵉ Xᵉ =
    ( is-of-natural-height-𝕍ᵉ nᵉ Xᵉ ,ᵉ is-prop-is-of-natural-height-𝕍ᵉ nᵉ Xᵉ)
```

### Explicitly bounded multisets

Anᵉ **explicitlyᵉ boundedᵉ multiset**ᵉ isᵉ aᵉ multisetᵉ ofᵉ specifiedᵉ naturalᵉ height.ᵉ
Noteᵉ that,ᵉ asᵉ weᵉ willᵉ showᵉ below,ᵉ everyᵉ multisetᵉ ofᵉ naturalᵉ heightᵉ `n`ᵉ isᵉ alsoᵉ aᵉ
multisetᵉ ofᵉ naturalᵉ heightᵉ `nᵉ +ᵉ 1`,ᵉ soᵉ theᵉ typeᵉ ofᵉ naturalᵉ numbersᵉ `n`ᵉ equippedᵉ
with aᵉ proofᵉ thatᵉ `X`ᵉ isᵉ ofᵉ naturalᵉ heightᵉ `n`ᵉ isᵉ farᵉ fromᵉ aᵉ proposition.ᵉ

```agda
Explicitly-Bounded-𝕍ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Explicitly-Bounded-𝕍ᵉ lᵉ =
  Σᵉ (𝕍ᵉ lᵉ) (λ Xᵉ → Σᵉ ℕᵉ (λ nᵉ → is-of-natural-height-𝕍ᵉ nᵉ Xᵉ))
```

### Bounded multisets

Aᵉ **boundedᵉ multiset**ᵉ isᵉ aᵉ multisetᵉ forᵉ whichᵉ aᵉ naturalᵉ boundᵉ
[merelyᵉ exists](foundation.existential-quantification.mdᵉ)

```agda
data
  Bounded-𝕍ᵉ (lᵉ : Level) : ℕᵉ → UUᵉ (lsuc lᵉ)
  where
  empty-multiset-Bounded-𝕍ᵉ : Bounded-𝕍ᵉ lᵉ 0
  tree-multiset-Bounded-𝕍ᵉ :
    {nᵉ : ℕᵉ} {Xᵉ : UUᵉ lᵉ} (Yᵉ : Xᵉ → Bounded-𝕍ᵉ lᵉ nᵉ) → Bounded-𝕍ᵉ lᵉ (succ-ℕᵉ nᵉ)

Bounded-𝕍'ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Bounded-𝕍'ᵉ lᵉ =
  Σᵉ (𝕍ᵉ lᵉ) (λ Xᵉ → existsᵉ ℕᵉ (λ nᵉ → is-of-natural-height-prop-𝕍ᵉ nᵉ Xᵉ))
```

## Properties

### The empty multiset is of any natural height

```agda
module _
  {lᵉ : Level}
  where

  is-of-natural-height-is-empty-𝕍ᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : 𝕍ᵉ lᵉ) → is-empty-𝕍ᵉ Xᵉ → is-of-natural-height-𝕍ᵉ nᵉ Xᵉ
  is-of-natural-height-is-empty-𝕍ᵉ zero-ℕᵉ Xᵉ Hᵉ = Hᵉ
  is-of-natural-height-is-empty-𝕍ᵉ (succ-ℕᵉ nᵉ) (tree-𝕎ᵉ Xᵉ Yᵉ) Hᵉ xᵉ = ex-falsoᵉ (Hᵉ xᵉ)
```

### A multiset of natural height `n` is a multiset of natural height `n + 1`

```agda
module _
  {lᵉ : Level}
  where

  is-of-natural-height-succ-𝕍ᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : 𝕍ᵉ lᵉ) →
    is-of-natural-height-𝕍ᵉ nᵉ Xᵉ → is-of-natural-height-𝕍ᵉ (succ-ℕᵉ nᵉ) Xᵉ
  is-of-natural-height-succ-𝕍ᵉ zero-ℕᵉ Xᵉ Hᵉ =
    is-of-natural-height-is-empty-𝕍ᵉ 1 Xᵉ Hᵉ
  is-of-natural-height-succ-𝕍ᵉ (succ-ℕᵉ nᵉ) (tree-𝕎ᵉ Xᵉ Yᵉ) Hᵉ xᵉ =
    is-of-natural-height-succ-𝕍ᵉ nᵉ (Yᵉ xᵉ) (Hᵉ xᵉ)
```