# Coverings in locales

```agda
module order-theory.coverings-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.localesᵉ
```

</details>

## Idea

Aᵉ **covering**ᵉ ofᵉ anᵉ objectᵉ `u`ᵉ in aᵉ [locale](order-theory.locales.mdᵉ) isᵉ aᵉ
familyᵉ ofᵉ objectsᵉ whoseᵉ joinᵉ isᵉ `u`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Localeᵉ l1ᵉ l2ᵉ) (uᵉ : type-Localeᵉ Lᵉ)
  where

  is-covering-Localeᵉ : {Iᵉ : UUᵉ l2ᵉ} → (Iᵉ → type-Localeᵉ Lᵉ) → UUᵉ l1ᵉ
  is-covering-Localeᵉ xᵉ = (uᵉ ＝ᵉ sup-Localeᵉ Lᵉ xᵉ)

  covering-Localeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  covering-Localeᵉ =
    Σᵉ ( UUᵉ l2ᵉ)
      ( λ Iᵉ →
        Σᵉ ( Iᵉ → type-Localeᵉ Lᵉ)
          ( is-covering-Localeᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Localeᵉ l1ᵉ l2ᵉ)
  {uᵉ : type-Localeᵉ Lᵉ} (vᵉ : covering-Localeᵉ Lᵉ uᵉ)
  where

  indexing-type-covering-Localeᵉ : UUᵉ l2ᵉ
  indexing-type-covering-Localeᵉ = pr1ᵉ vᵉ

  covering-family-covering-Localeᵉ :
    indexing-type-covering-Localeᵉ → type-Localeᵉ Lᵉ
  covering-family-covering-Localeᵉ = pr1ᵉ (pr2ᵉ vᵉ)

  is-covering-covering-Localeᵉ :
    is-covering-Localeᵉ Lᵉ uᵉ covering-family-covering-Localeᵉ
  is-covering-covering-Localeᵉ = pr2ᵉ (pr2ᵉ vᵉ)
```