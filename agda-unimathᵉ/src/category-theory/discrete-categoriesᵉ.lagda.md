# Discrete categories

```agda
module category-theory.discrete-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

### Discrete precategories

Anyᵉ setᵉ inducesᵉ aᵉ discreteᵉ categoryᵉ whoseᵉ objectsᵉ areᵉ elementsᵉ ofᵉ theᵉ setᵉ andᵉ
whichᵉ containsᵉ no-nonidentityᵉ morphisms.ᵉ

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  discrete-precategory-Setᵉ : Precategoryᵉ lᵉ lᵉ
  discrete-precategory-Setᵉ =
    make-Precategoryᵉ
      ( type-Setᵉ Xᵉ)
      ( λ xᵉ yᵉ → set-Propᵉ (Id-Propᵉ Xᵉ xᵉ yᵉ))
      ( λ pᵉ qᵉ → qᵉ ∙ᵉ pᵉ)
      ( λ xᵉ → reflᵉ)
      ( λ hᵉ gᵉ fᵉ → invᵉ (assocᵉ fᵉ gᵉ hᵉ))
      ( λ _ → right-unitᵉ)
      ( λ _ → left-unitᵉ)
```