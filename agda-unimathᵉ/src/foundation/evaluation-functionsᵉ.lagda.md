# Evaluation of functions

```agda
module foundation.evaluation-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ overᵉ `A`ᵉ andᵉ let `aᵉ : A`ᵉ beᵉ anᵉ element.ᵉ Theᵉ
{{#conceptᵉ "evaluationᵉ function"ᵉ Agda=evᵉ}} atᵉ `a`ᵉ

```text
  evᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Bᵉ aᵉ
```

isᵉ theᵉ mapᵉ givenᵉ byᵉ `fᵉ ↦ᵉ fᵉ a`,ᵉ evaluatingᵉ dependentᵉ functionsᵉ atᵉ `a`.ᵉ

## Definitions

### The evaluation function

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ)
  where

  evᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Bᵉ aᵉ
  evᵉ fᵉ = fᵉ aᵉ
```

### The evaluation function with an explicit type family

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  where

  ev-dependent-functionᵉ : ((xᵉ : Aᵉ) → Bᵉ xᵉ) → Bᵉ aᵉ
  ev-dependent-functionᵉ = evᵉ aᵉ
```

### The evaluation function for nondependent functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  where

  ev-functionᵉ : (Aᵉ → Bᵉ) → Bᵉ
  ev-functionᵉ = evᵉ aᵉ
```

### The evaluation function of implicit functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ)
  where

  ev-implicit-functionᵉ : ({xᵉ : Aᵉ} → Bᵉ xᵉ) → Bᵉ aᵉ
  ev-implicit-functionᵉ fᵉ = fᵉ {aᵉ}
```

### The evaluation function of implicit functions, specified with an explicit type family

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (aᵉ : Aᵉ)
  where

  ev-implicit-function'ᵉ : ({xᵉ : Aᵉ} → Bᵉ xᵉ) → Bᵉ aᵉ
  ev-implicit-function'ᵉ = ev-implicit-functionᵉ aᵉ
```

## See also

-ᵉ Theᵉ
  [actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
  ofᵉ theᵉ evaluationᵉ mapᵉ isᵉ theᵉ functionᵉ `aᵉ ↦ᵉ λ pᵉ → htpy-eqᵉ pᵉ a`ᵉ definedᵉ in
  [Functionᵉ extensionality](foundation.function-extensionality.md).ᵉ