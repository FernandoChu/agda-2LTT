# Dedekind finite sets

```agda
module univalent-combinatorics.dedekind-finite-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Dedekindᵉ finiteᵉ setsᵉ areᵉ setsᵉ `X`ᵉ with theᵉ propertyᵉ thatᵉ everyᵉ embeddingᵉ `Xᵉ ↪ᵉ X`ᵉ
isᵉ anᵉ equivalence.ᵉ

## Definition

```agda
is-dedekind-finite-set-Propᵉ : {lᵉ : Level} → Setᵉ lᵉ → Propᵉ lᵉ
is-dedekind-finite-set-Propᵉ Xᵉ =
  Π-Propᵉ
    ( type-Setᵉ Xᵉ → type-Setᵉ Xᵉ)
    ( λ fᵉ → function-Propᵉ (is-embᵉ fᵉ) (is-equiv-Propᵉ fᵉ))

is-dedekind-finite-setᵉ : {lᵉ : Level} → Setᵉ lᵉ → UUᵉ lᵉ
is-dedekind-finite-setᵉ Xᵉ = type-Propᵉ (is-dedekind-finite-set-Propᵉ Xᵉ)

𝔽-Dedekindᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
𝔽-Dedekindᵉ lᵉ = Σᵉ (Setᵉ lᵉ) is-dedekind-finite-setᵉ

module _
  {lᵉ : Level} (Xᵉ : 𝔽-Dedekindᵉ lᵉ)
  where

  set-𝔽-Dedekindᵉ : Setᵉ lᵉ
  set-𝔽-Dedekindᵉ = pr1ᵉ Xᵉ

  type-𝔽-Dedekindᵉ : UUᵉ lᵉ
  type-𝔽-Dedekindᵉ = type-Setᵉ set-𝔽-Dedekindᵉ

  is-set-type-𝔽-Dedekindᵉ : is-setᵉ type-𝔽-Dedekindᵉ
  is-set-type-𝔽-Dedekindᵉ = is-set-type-Setᵉ set-𝔽-Dedekindᵉ

  is-dedekind-finite-set-𝔽-Dedekindᵉ : is-dedekind-finite-setᵉ set-𝔽-Dedekindᵉ
  is-dedekind-finite-set-𝔽-Dedekindᵉ = pr2ᵉ Xᵉ
```