# The nilradical of a commutative semiring

```agda
module commutative-algebra.nilradicals-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.subsets-commutative-semiringsᵉ

open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.nilpotent-elements-semiringsᵉ
```

</details>

## Idea

Theᵉ **nilradical**ᵉ ofᵉ aᵉ commutativeᵉ semiringᵉ isᵉ theᵉ idealᵉ consistingᵉ ofᵉ allᵉ
nilpotentᵉ elements.ᵉ

## Definitions

```agda
subset-nilradical-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) → subset-Commutative-Semiringᵉ lᵉ Aᵉ
subset-nilradical-Commutative-Semiringᵉ Aᵉ =
  is-nilpotent-element-semiring-Propᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

## Properties

### The nilradical contains zero

```agda
contains-zero-nilradical-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) →
  contains-zero-subset-Commutative-Semiringᵉ Aᵉ
    ( subset-nilradical-Commutative-Semiringᵉ Aᵉ)
contains-zero-nilradical-Commutative-Semiringᵉ Aᵉ = intro-existsᵉ 1 reflᵉ
```

### The nilradical is closed under addition

```agda
is-closed-under-add-nilradical-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) →
  is-closed-under-addition-subset-Commutative-Semiringᵉ Aᵉ
    ( subset-nilradical-Commutative-Semiringᵉ Aᵉ)
is-closed-under-add-nilradical-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ =
  is-nilpotent-add-Semiringᵉ
    ( semiring-Commutative-Semiringᵉ Aᵉ)
    ( xᵉ)
    ( yᵉ)
    ( commutative-mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ)
```

### The nilradical is closed under multiplication with ring elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  is-closed-under-right-multiplication-nilradical-Commutative-Semiringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Semiringᵉ Aᵉ
      ( subset-nilradical-Commutative-Semiringᵉ Aᵉ)
  is-closed-under-right-multiplication-nilradical-Commutative-Semiringᵉ xᵉ yᵉ =
    is-nilpotent-element-mul-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( xᵉ)
      ( yᵉ)
      ( commutative-mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ)

  is-closed-under-left-multiplication-nilradical-Commutative-Semiringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Semiringᵉ Aᵉ
      ( subset-nilradical-Commutative-Semiringᵉ Aᵉ)
  is-closed-under-left-multiplication-nilradical-Commutative-Semiringᵉ xᵉ yᵉ =
    is-nilpotent-element-mul-Semiring'ᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( yᵉ)
      ( xᵉ)
      ( commutative-mul-Commutative-Semiringᵉ Aᵉ yᵉ xᵉ)
```