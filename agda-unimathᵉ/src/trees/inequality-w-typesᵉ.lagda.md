# Inequality on W-types

```agda
module trees.inequality-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ elementhoodᵉ relationᵉ onᵉ W-typesᵉ inducesᵉ aᵉ strictᵉ ordering.ᵉ

## Definition

### Strict inequality on W-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  infix 6 _<-𝕎ᵉ_

  data _<-𝕎ᵉ_ (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ) where
    le-∈-𝕎ᵉ : {yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ ∈-𝕎ᵉ yᵉ → xᵉ <-𝕎ᵉ yᵉ
    propagate-le-𝕎ᵉ : {yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → yᵉ ∈-𝕎ᵉ zᵉ → xᵉ <-𝕎ᵉ yᵉ → xᵉ <-𝕎ᵉ zᵉ
```

### Inequality on W-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  infix 6 _≤-𝕎ᵉ_

  data _≤-𝕎ᵉ_ (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ) where
    refl-leq-𝕎ᵉ : xᵉ ≤-𝕎ᵉ xᵉ
    propagate-leq-𝕎ᵉ : {yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → yᵉ ∈-𝕎ᵉ zᵉ → xᵉ ≤-𝕎ᵉ yᵉ → xᵉ ≤-𝕎ᵉ zᵉ

  leq-∈-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ ∈-𝕎ᵉ yᵉ → xᵉ ≤-𝕎ᵉ yᵉ
  leq-∈-𝕎ᵉ Hᵉ = propagate-leq-𝕎ᵉ Hᵉ refl-leq-𝕎ᵉ
```

### Walks in W-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  data walk-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ) where
    rootᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → walk-𝕎ᵉ wᵉ
    consᵉ :
      (aᵉ : Aᵉ) (fᵉ : Bᵉ aᵉ → 𝕎ᵉ Aᵉ Bᵉ) (bᵉ : Bᵉ aᵉ) →
      walk-𝕎ᵉ (fᵉ bᵉ) → walk-𝕎ᵉ (tree-𝕎ᵉ aᵉ fᵉ)

  length-walk-𝕎ᵉ : (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → walk-𝕎ᵉ wᵉ → ℕᵉ
  length-walk-𝕎ᵉ wᵉ (rootᵉ .wᵉ) = zero-ℕᵉ
  length-walk-𝕎ᵉ .(tree-𝕎ᵉ aᵉ fᵉ) (consᵉ aᵉ fᵉ bᵉ pᵉ) = succ-ℕᵉ (length-walk-𝕎ᵉ (fᵉ bᵉ) pᵉ)
```

## Properties

### The strict ordering on W-types is transitive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  transitive-le-𝕎ᵉ : {xᵉ yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → yᵉ <-𝕎ᵉ zᵉ → xᵉ <-𝕎ᵉ yᵉ → xᵉ <-𝕎ᵉ zᵉ
  transitive-le-𝕎ᵉ {xᵉ = xᵉ} {yᵉ} {zᵉ} (le-∈-𝕎ᵉ Hᵉ) Kᵉ =
    propagate-le-𝕎ᵉ Hᵉ Kᵉ
  transitive-le-𝕎ᵉ {xᵉ = xᵉ} {yᵉ} {zᵉ} (propagate-le-𝕎ᵉ Lᵉ Hᵉ) Kᵉ =
    propagate-le-𝕎ᵉ Lᵉ (transitive-le-𝕎ᵉ Hᵉ Kᵉ)
```

### The strict ordering on W-types is irreflexive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  irreflexive-le-𝕎ᵉ :
    {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} → ¬ᵉ (xᵉ <-𝕎ᵉ xᵉ)
  irreflexive-le-𝕎ᵉ {xᵉ = xᵉ} (le-∈-𝕎ᵉ Hᵉ) = irreflexive-∈-𝕎ᵉ xᵉ Hᵉ
  irreflexive-le-𝕎ᵉ {xᵉ = tree-𝕎ᵉ xᵉ αᵉ} (propagate-le-𝕎ᵉ (pairᵉ bᵉ reflᵉ) Hᵉ) =
    irreflexive-le-𝕎ᵉ {xᵉ = αᵉ bᵉ} (transitive-le-𝕎ᵉ Hᵉ (le-∈-𝕎ᵉ (pairᵉ bᵉ reflᵉ)))
```

### The strict ordering on W-types is asymmetric

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  asymmetric-le-𝕎ᵉ :
    {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ <-𝕎ᵉ yᵉ → yᵉ <-𝕎ᵉ xᵉ → emptyᵉ
  asymmetric-le-𝕎ᵉ Hᵉ Kᵉ = irreflexive-le-𝕎ᵉ (transitive-le-𝕎ᵉ Hᵉ Kᵉ)
```

### Transitivity of `≤-𝕎`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  transitive-leq-𝕎ᵉ :
    {xᵉ yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ ≤-𝕎ᵉ yᵉ → yᵉ ≤-𝕎ᵉ zᵉ → xᵉ ≤-𝕎ᵉ zᵉ
  transitive-leq-𝕎ᵉ Hᵉ refl-leq-𝕎ᵉ = Hᵉ
  transitive-leq-𝕎ᵉ Hᵉ (propagate-leq-𝕎ᵉ eᵉ Kᵉ) =
    propagate-leq-𝕎ᵉ eᵉ (transitive-leq-𝕎ᵉ Hᵉ Kᵉ)
```