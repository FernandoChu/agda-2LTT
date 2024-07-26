# Postcomposition of functions

```agda
module foundation-core.postcomposition-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import foundation-core.postcomposition-dependent-functionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ mapᵉ `fᵉ : Xᵉ → Y`ᵉ andᵉ aᵉ typeᵉ `A`,ᵉ theᵉ
{{#conceptᵉ "postcompositionᵉ function"ᵉ Agda=postcompᵉ}}

```text
  fᵉ ∘ᵉ -ᵉ : (Aᵉ → Xᵉ) → (Aᵉ → Yᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → fᵉ (hᵉ x)`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  where

  postcompᵉ : (Xᵉ → Yᵉ) → (Aᵉ → Xᵉ) → (Aᵉ → Yᵉ)
  postcompᵉ fᵉ = postcomp-Πᵉ Aᵉ fᵉ
```