# Furstenberg groups

```agda
module group-theory.furstenberg-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definition

```agda
Furstenberg-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Furstenberg-Groupᵉ lᵉ =
  Σᵉ ( Setᵉ lᵉ)
    ( λ Xᵉ →
      ( type-trunc-Propᵉ (type-Setᵉ Xᵉ)) ×ᵉ
      ( Σᵉ ( type-Setᵉ Xᵉ → type-Setᵉ Xᵉ → type-Setᵉ Xᵉ)
          ( λ μᵉ →
            ( (xᵉ yᵉ zᵉ : type-Setᵉ Xᵉ) → Idᵉ (μᵉ (μᵉ xᵉ zᵉ) (μᵉ yᵉ zᵉ)) (μᵉ xᵉ yᵉ)) ×ᵉ
            ( Σᵉ ( type-Setᵉ Xᵉ → type-Setᵉ Xᵉ → type-Setᵉ Xᵉ)
                ( λ δᵉ → (xᵉ yᵉ : type-Setᵉ Xᵉ) → Idᵉ (μᵉ xᵉ (δᵉ xᵉ yᵉ)) yᵉ)))))
```