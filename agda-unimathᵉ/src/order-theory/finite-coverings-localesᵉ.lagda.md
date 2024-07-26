# Finite coverings in locales

```agda
module order-theory.finite-coverings-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.coverings-localesᵉ
open import order-theory.localesᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ **finiteᵉ covering**ᵉ ofᵉ anᵉ objectᵉ `u`ᵉ in aᵉ [locale](order-theory.locales.mdᵉ) isᵉ
aᵉ [finite](univalent-combinatorics.finite-types.mdᵉ) familyᵉ ofᵉ objectsᵉ whoseᵉ joinᵉ
isᵉ `u`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Localeᵉ l1ᵉ l2ᵉ) (uᵉ : type-Localeᵉ Lᵉ)
  where

  is-finite-covering-Localeᵉ : (vᵉ : covering-Localeᵉ Lᵉ uᵉ) → UUᵉ l2ᵉ
  is-finite-covering-Localeᵉ vᵉ = is-finiteᵉ (indexing-type-covering-Localeᵉ Lᵉ vᵉ)

  finite-covering-Localeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  finite-covering-Localeᵉ =
    Σᵉ ( 𝔽ᵉ l2ᵉ)
      ( λ Iᵉ →
        Σᵉ ( type-𝔽ᵉ Iᵉ → type-Localeᵉ Lᵉ)
          ( is-covering-Localeᵉ Lᵉ uᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Localeᵉ l1ᵉ l2ᵉ)
  {uᵉ : type-Localeᵉ Lᵉ} (vᵉ : finite-covering-Localeᵉ Lᵉ uᵉ)
  where

  indexing-type-finite-covering-Localeᵉ : UUᵉ l2ᵉ
  indexing-type-finite-covering-Localeᵉ = type-𝔽ᵉ (pr1ᵉ vᵉ)

  covering-family-finite-covering-Localeᵉ :
    indexing-type-finite-covering-Localeᵉ → type-Localeᵉ Lᵉ
  covering-family-finite-covering-Localeᵉ = pr1ᵉ (pr2ᵉ vᵉ)

  is-covering-finite-covering-Localeᵉ :
    is-covering-Localeᵉ Lᵉ uᵉ covering-family-finite-covering-Localeᵉ
  is-covering-finite-covering-Localeᵉ = pr2ᵉ (pr2ᵉ vᵉ)

  covering-finite-covering-Localeᵉ : covering-Localeᵉ Lᵉ uᵉ
  pr1ᵉ covering-finite-covering-Localeᵉ = indexing-type-finite-covering-Localeᵉ
  pr1ᵉ (pr2ᵉ covering-finite-covering-Localeᵉ) =
    covering-family-finite-covering-Localeᵉ
  pr2ᵉ (pr2ᵉ covering-finite-covering-Localeᵉ) = is-covering-finite-covering-Localeᵉ

  is-finite-covering-covering-Localeᵉ :
    is-finite-covering-Localeᵉ Lᵉ uᵉ covering-finite-covering-Localeᵉ
  is-finite-covering-covering-Localeᵉ = is-finite-type-𝔽ᵉ (pr1ᵉ vᵉ)
```