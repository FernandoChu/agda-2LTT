# Precomposition of functions

```agda
module foundation-core.precomposition-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ **precompositionᵉ function**ᵉ byᵉ
`f`ᵉ

```text
  -ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → Xᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → hᵉ (fᵉ x)`.ᵉ

## Definitions

### The precomposition operation on ordinary functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  precompᵉ : (Bᵉ → Cᵉ) → (Aᵉ → Cᵉ)
  precompᵉ = _∘ᵉ fᵉ
```