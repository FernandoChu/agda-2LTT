# Trivial rings

```agda
module ring-theory.trivial-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Trivialᵉ ringsᵉ areᵉ ringsᵉ in whichᵉ `0ᵉ = 1`.ᵉ

## Definition

```agda
is-trivial-ring-Propᵉ : {lᵉ : Level} → Ringᵉ lᵉ → Propᵉ lᵉ
is-trivial-ring-Propᵉ Rᵉ =
  Id-Propᵉ (set-Ringᵉ Rᵉ) (zero-Ringᵉ Rᵉ) (one-Ringᵉ Rᵉ)

is-trivial-Ringᵉ : {lᵉ : Level} → Ringᵉ lᵉ → UUᵉ lᵉ
is-trivial-Ringᵉ Rᵉ = type-Propᵉ (is-trivial-ring-Propᵉ Rᵉ)

is-prop-is-trivial-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → is-propᵉ (is-trivial-Ringᵉ Rᵉ)
is-prop-is-trivial-Ringᵉ Rᵉ = is-prop-type-Propᵉ (is-trivial-ring-Propᵉ Rᵉ)

is-nontrivial-ring-Propᵉ : {lᵉ : Level} → Ringᵉ lᵉ → Propᵉ lᵉ
is-nontrivial-ring-Propᵉ Rᵉ =
  neg-Propᵉ (is-trivial-ring-Propᵉ Rᵉ)

is-nontrivial-Ringᵉ : {lᵉ : Level} → Ringᵉ lᵉ → UUᵉ lᵉ
is-nontrivial-Ringᵉ Rᵉ = type-Propᵉ (is-nontrivial-ring-Propᵉ Rᵉ)

is-prop-is-nontrivial-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → is-propᵉ (is-nontrivial-Ringᵉ Rᵉ)
is-prop-is-nontrivial-Ringᵉ Rᵉ = is-prop-type-Propᵉ (is-nontrivial-ring-Propᵉ Rᵉ)
```

## Properties

### The carrier type of a trivial ring is contractible

```agda
is-contr-is-trivial-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) →
  is-trivial-Ringᵉ Rᵉ →
  is-contrᵉ (type-Ringᵉ Rᵉ)
pr1ᵉ (is-contr-is-trivial-Ringᵉ Rᵉ pᵉ) = zero-Ringᵉ Rᵉ
pr2ᵉ (is-contr-is-trivial-Ringᵉ Rᵉ pᵉ) xᵉ =
  equational-reasoningᵉ
    zero-Ringᵉ Rᵉ
      ＝ᵉ mul-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ) xᵉ
        byᵉ invᵉ (left-zero-law-mul-Ringᵉ Rᵉ xᵉ)
      ＝ᵉ mul-Ringᵉ Rᵉ (one-Ringᵉ Rᵉ) xᵉ
        byᵉ ap-binaryᵉ (mul-Ringᵉ Rᵉ) pᵉ reflᵉ
      ＝ᵉ xᵉ
        byᵉ left-unit-law-mul-Ringᵉ Rᵉ xᵉ
```

### Invertible elements of nontrivial rings are not equal to zero

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (Hᵉ : is-nontrivial-Ringᵉ Rᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  where

  is-nonzero-is-invertible-element-nontrivial-Ringᵉ :
    is-invertible-element-Ringᵉ Rᵉ xᵉ → zero-Ringᵉ Rᵉ ≠ᵉ xᵉ
  is-nonzero-is-invertible-element-nontrivial-Ringᵉ (yᵉ ,ᵉ Pᵉ ,ᵉ _) Kᵉ =
    Hᵉ ( ( invᵉ (left-zero-law-mul-Ringᵉ Rᵉ yᵉ)) ∙ᵉ
        ( apᵉ (mul-Ring'ᵉ Rᵉ yᵉ) Kᵉ) ∙ᵉ
        ( Pᵉ))
```