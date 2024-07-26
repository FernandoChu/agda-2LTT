# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.prime-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.nilpotent-elements-ringsᵉ
```

</details>

## Idea

Theᵉ **nilradical**ᵉ ofᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) isᵉ theᵉ
[ideal](commutative-algebra.ideals-commutative-rings.mdᵉ) consistingᵉ ofᵉ allᵉ
[nilpotentᵉ elements](ring-theory.nilpotent-elements-rings.md).ᵉ

## Definitions

```agda
subset-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) → subset-Commutative-Ringᵉ lᵉ Aᵉ
subset-nilradical-Commutative-Ringᵉ Aᵉ =
  is-nilpotent-element-ring-Propᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  contains-zero-subset-Commutative-Ringᵉ Aᵉ
    ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
contains-zero-nilradical-Commutative-Ringᵉ Aᵉ = intro-existsᵉ 1 reflᵉ
```

### The nilradical is closed under addition

```agda
is-closed-under-addition-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  is-closed-under-addition-subset-Commutative-Ringᵉ Aᵉ
    ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
is-closed-under-addition-nilradical-Commutative-Ringᵉ Aᵉ {xᵉ} {yᵉ} =
  is-nilpotent-add-Ringᵉ
    ( ring-Commutative-Ringᵉ Aᵉ)
    ( xᵉ)
    ( yᵉ)
    ( commutative-mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
```

### The nilradical is closed under negatives

```agda
is-closed-under-negatives-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  is-closed-under-negatives-subset-Commutative-Ringᵉ Aᵉ
    ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
is-closed-under-negatives-nilradical-Commutative-Ringᵉ Aᵉ xᵉ =
  is-nilpotent-element-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) xᵉ
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Aᵉ
      ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
  is-closed-under-right-multiplication-nilradical-Commutative-Ringᵉ xᵉ yᵉ =
    is-nilpotent-element-mul-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( xᵉ)
      ( yᵉ)
      ( commutative-mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)

  is-closed-under-left-multiplication-nilradical-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Aᵉ
      ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
  is-closed-under-left-multiplication-nilradical-Commutative-Ringᵉ xᵉ yᵉ =
    is-nilpotent-element-mul-Ring'ᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( yᵉ)
      ( xᵉ)
      ( commutative-mul-Commutative-Ringᵉ Aᵉ yᵉ xᵉ)
```

### The nilradical ideal

```agda
nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) → ideal-Commutative-Ringᵉ lᵉ Aᵉ
nilradical-Commutative-Ringᵉ Aᵉ =
  ideal-right-ideal-Commutative-Ringᵉ Aᵉ
    ( subset-nilradical-Commutative-Ringᵉ Aᵉ)
    ( contains-zero-nilradical-Commutative-Ringᵉ Aᵉ)
    ( is-closed-under-addition-nilradical-Commutative-Ringᵉ Aᵉ)
    ( is-closed-under-negatives-nilradical-Commutative-Ringᵉ Aᵉ)
    ( is-closed-under-right-multiplication-nilradical-Commutative-Ringᵉ Aᵉ)
```

### The nilradical is contained in every radical ideal

```agda
is-in-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ) → type-Commutative-Ringᵉ Rᵉ → UUᵉ lᵉ
is-in-nilradical-Commutative-Ringᵉ Rᵉ =
  is-in-ideal-Commutative-Ringᵉ Rᵉ (nilradical-Commutative-Ringᵉ Rᵉ)

is-contained-in-radical-ideal-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ lᵉ Rᵉ) (xᵉ : type-Commutative-Ringᵉ Rᵉ) →
  is-in-nilradical-Commutative-Ringᵉ Rᵉ xᵉ →
  is-in-radical-ideal-Commutative-Ringᵉ Rᵉ Iᵉ xᵉ
is-contained-in-radical-ideal-nilradical-Commutative-Ringᵉ Rᵉ Iᵉ xᵉ pᵉ =
  apply-universal-property-trunc-Propᵉ pᵉ
    ( subset-radical-ideal-Commutative-Ringᵉ Rᵉ Iᵉ xᵉ)
    ( λ (nᵉ ,ᵉ pᵉ) → is-radical-radical-ideal-Commutative-Ringᵉ Rᵉ Iᵉ xᵉ nᵉ
    (is-closed-under-eq-radical-ideal-Commutative-Ring'ᵉ Rᵉ Iᵉ
    (contains-zero-radical-ideal-Commutative-Ringᵉ Rᵉ Iᵉ) pᵉ))
```

### The nilradical is contained in every prime ideal

```agda
is-contained-in-prime-ideal-nilradical-Commutative-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  (Pᵉ : prime-ideal-Commutative-Ringᵉ lᵉ Rᵉ) (xᵉ : type-Commutative-Ringᵉ Rᵉ) →
  is-in-nilradical-Commutative-Ringᵉ Rᵉ xᵉ →
  is-in-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ
is-contained-in-prime-ideal-nilradical-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ pᵉ =
  is-in-prime-ideal-is-in-radical-ideal-Commutative-Ringᵉ Rᵉ Pᵉ xᵉ
    ( is-contained-in-radical-ideal-nilradical-Commutative-Ringᵉ Rᵉ
      ( radical-ideal-prime-ideal-Commutative-Ringᵉ Rᵉ Pᵉ) xᵉ pᵉ)
```