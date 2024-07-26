# Sheargroups

```agda
module group-theory.sheargroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definition

```agda
Sheargroupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Sheargroupᵉ lᵉ =
  Σᵉ ( Setᵉ lᵉ)
    ( λ Xᵉ →
      Σᵉ ( type-Setᵉ Xᵉ)
        ( λ eᵉ →
          Σᵉ (type-Setᵉ Xᵉ → type-Setᵉ Xᵉ → type-Setᵉ Xᵉ)
            ( λ mᵉ →
              ( (xᵉ : type-Setᵉ Xᵉ) → Idᵉ (mᵉ eᵉ xᵉ) xᵉ) ×ᵉ
              ( ( (xᵉ : type-Setᵉ Xᵉ) → Idᵉ (mᵉ xᵉ xᵉ) eᵉ) ×ᵉ
                ( (xᵉ yᵉ zᵉ : type-Setᵉ Xᵉ) →
                  Idᵉ (mᵉ xᵉ (mᵉ yᵉ zᵉ)) (mᵉ (mᵉ (mᵉ xᵉ (mᵉ yᵉ eᵉ)) eᵉ) zᵉ))))))
```