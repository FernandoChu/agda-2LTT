# Ranks of elements in W-types

```agda
module trees.ranks-of-elements-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.inequality-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ W-typeᵉ `𝕎ᵉ Aᵉ B`.ᵉ Weᵉ sayᵉ thatᵉ theᵉ **rank**ᵉ
ofᵉ `x`ᵉ isᵉ atᵉ mostᵉ theᵉ rankᵉ ofᵉ `y`ᵉ ifᵉ forᵉ everyᵉ elementᵉ `x'ᵉ ∈ᵉ x`ᵉ andᵉ forᵉ everyᵉ
elementᵉ `y'ᵉ ∈ᵉ y`ᵉ theᵉ rankᵉ ofᵉ `x'`ᵉ isᵉ atᵉ mostᵉ theᵉ rankᵉ ofᵉ `y'`.ᵉ

## Definition

### Rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  _≼-𝕎-Propᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  (tree-𝕎ᵉ xᵉ αᵉ) ≼-𝕎-Propᵉ (tree-𝕎ᵉ yᵉ βᵉ) =
    Π-Propᵉ (Bᵉ xᵉ) (λ bᵉ → ∃ᵉ (Bᵉ yᵉ) (λ cᵉ → (αᵉ bᵉ) ≼-𝕎-Propᵉ (βᵉ cᵉ)))

  _≼-𝕎ᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ≼-𝕎ᵉ yᵉ = type-Propᵉ (xᵉ ≼-𝕎-Propᵉ yᵉ)

  _≈-𝕎-Propᵉ_ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ≈-𝕎-Propᵉ yᵉ = product-Propᵉ (xᵉ ≼-𝕎-Propᵉ yᵉ) (yᵉ ≼-𝕎-Propᵉ xᵉ)

  _≈-𝕎ᵉ_ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ≈-𝕎ᵉ yᵉ = type-Propᵉ (xᵉ ≈-𝕎-Propᵉ yᵉ)
```

### Strict rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  _≺-𝕎-Propᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ≺-𝕎-Propᵉ yᵉ =
    ∃ᵉ (Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (λ wᵉ → wᵉ ∈-𝕎ᵉ yᵉ)) (λ tᵉ → xᵉ ≼-𝕎-Propᵉ (pr1ᵉ tᵉ))

  _≺-𝕎ᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ ≺-𝕎ᵉ yᵉ = type-Propᵉ (xᵉ ≺-𝕎-Propᵉ yᵉ)

  in-lower-set-≺-𝕎-Propᵉ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  in-lower-set-≺-𝕎-Propᵉ xᵉ yᵉ = yᵉ ≺-𝕎-Propᵉ xᵉ

  in-lower-set-≺-𝕎ᵉ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  in-lower-set-≺-𝕎ᵉ xᵉ yᵉ = yᵉ ≺-𝕎ᵉ xᵉ

  has-same-lower-set-≺-𝕎ᵉ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-same-lower-set-≺-𝕎ᵉ xᵉ yᵉ = (zᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (zᵉ ≺-𝕎ᵉ xᵉ) ×ᵉ (zᵉ ≺-𝕎ᵉ yᵉ)
```

### Strong rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  _strong-≼-𝕎-Propᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ strong-≼-𝕎-Propᵉ yᵉ =
    Π-Propᵉ
      ( 𝕎ᵉ Aᵉ Bᵉ)
      ( λ uᵉ →
        Π-Propᵉ
          ( uᵉ ∈-𝕎ᵉ xᵉ)
          ( λ Hᵉ →
            ∃ᵉ ( 𝕎ᵉ Aᵉ Bᵉ)
              ( λ vᵉ →
                ∃ᵉ (vᵉ ∈-𝕎ᵉ yᵉ) (λ Kᵉ → uᵉ ≼-𝕎-Propᵉ vᵉ))))

  _strong-≼-𝕎ᵉ_ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xᵉ strong-≼-𝕎ᵉ yᵉ = type-Propᵉ (xᵉ strong-≼-𝕎-Propᵉ yᵉ)
```

## Properties

### Reflexivity of rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  refl-≼-𝕎ᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → xᵉ ≼-𝕎ᵉ xᵉ
  refl-≼-𝕎ᵉ (tree-𝕎ᵉ xᵉ αᵉ) bᵉ = unit-trunc-Propᵉ (pairᵉ bᵉ (refl-≼-𝕎ᵉ (αᵉ bᵉ)))
```

### Transitivity of rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  transitive-≼-𝕎ᵉ : {xᵉ yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ≼-𝕎ᵉ yᵉ) → (yᵉ ≼-𝕎ᵉ zᵉ) → (xᵉ ≼-𝕎ᵉ zᵉ)
  transitive-≼-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} {tree-𝕎ᵉ yᵉ βᵉ} {tree-𝕎ᵉ zᵉ γᵉ} Hᵉ Kᵉ aᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ aᵉ)
      ( ∃ᵉ (Bᵉ zᵉ) (λ cᵉ → (αᵉ aᵉ) ≼-𝕎-Propᵉ (γᵉ cᵉ)))
      ( λ tᵉ →
        apply-universal-property-trunc-Propᵉ
          ( Kᵉ (pr1ᵉ tᵉ))
          ( ∃ᵉ (Bᵉ zᵉ) (λ cᵉ → (αᵉ aᵉ) ≼-𝕎-Propᵉ (γᵉ cᵉ)))
          ( λ sᵉ →
            unit-trunc-Propᵉ
              ( pairᵉ
                ( pr1ᵉ sᵉ)
                ( transitive-≼-𝕎ᵉ
                  { αᵉ aᵉ}
                  { βᵉ (pr1ᵉ tᵉ)}
                  { γᵉ (pr1ᵉ sᵉ)}
                  ( pr2ᵉ tᵉ)
                  ( pr2ᵉ sᵉ)))))
```

### Rank comparison is equivalent to strong rank comparison

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  strong-≼-≼-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ≼-𝕎ᵉ yᵉ) → (xᵉ strong-≼-𝕎ᵉ yᵉ)
  strong-≼-≼-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} {tree-𝕎ᵉ yᵉ βᵉ} Hᵉ .(αᵉ bᵉ) (pairᵉ bᵉ reflᵉ) =
    apply-universal-property-trunc-Propᵉ (Hᵉ bᵉ)
      ( ∃ᵉ ( 𝕎ᵉ Aᵉ Bᵉ)
          ( (λ vᵉ → ∃ᵉ (vᵉ ∈-𝕎ᵉ tree-𝕎ᵉ yᵉ βᵉ) (λ hvᵉ → (αᵉ bᵉ) ≼-𝕎-Propᵉ vᵉ))))
      ( fᵉ)
      where
      fᵉ :
        Σᵉ (Bᵉ yᵉ) (λ cᵉ → pr1ᵉ (αᵉ bᵉ ≼-𝕎-Propᵉ βᵉ cᵉ)) →
        existsᵉ
          ( 𝕎ᵉ Aᵉ Bᵉ)
          ( λ vᵉ → ∃ᵉ (vᵉ ∈-𝕎ᵉ tree-𝕎ᵉ yᵉ βᵉ) (λ hvᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ vᵉ))
      fᵉ (pairᵉ cᵉ Kᵉ) =
        intro-existsᵉ (βᵉ cᵉ) ( intro-existsᵉ (pairᵉ cᵉ reflᵉ) Kᵉ)

  ≼-strong-≼-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ strong-≼-𝕎ᵉ yᵉ) → (xᵉ ≼-𝕎ᵉ yᵉ)
  ≼-strong-≼-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} {tree-𝕎ᵉ yᵉ βᵉ} Hᵉ bᵉ =
    apply-universal-property-trunc-Propᵉ
      ( Hᵉ (αᵉ bᵉ) (bᵉ ,ᵉ reflᵉ))
      ( ∃ᵉ (Bᵉ yᵉ) (λ cᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ βᵉ cᵉ))
      ( fᵉ)
    where
    fᵉ :
      Σᵉ ( 𝕎ᵉ Aᵉ Bᵉ)
        ( λ vᵉ → existsᵉ (vᵉ ∈-𝕎ᵉ tree-𝕎ᵉ yᵉ βᵉ) (λ Kᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ vᵉ)) →
      existsᵉ (Bᵉ yᵉ) (λ cᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ βᵉ cᵉ)
    fᵉ (pairᵉ vᵉ Kᵉ) =
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( ∃ᵉ (Bᵉ yᵉ) (λ cᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ βᵉ cᵉ))
          ( gᵉ)
      where
      gᵉ :
        (vᵉ ∈-𝕎ᵉ tree-𝕎ᵉ yᵉ βᵉ) ×ᵉ (αᵉ bᵉ ≼-𝕎ᵉ vᵉ) →
        existsᵉ (Bᵉ yᵉ) (λ cᵉ → αᵉ bᵉ ≼-𝕎-Propᵉ βᵉ cᵉ)
      gᵉ (pairᵉ (pairᵉ cᵉ pᵉ) Mᵉ) = intro-existsᵉ cᵉ (trᵉ (λ tᵉ → αᵉ bᵉ ≼-𝕎ᵉ tᵉ) (invᵉ pᵉ) Mᵉ)
```

### If `x ∈ y` then the rank of `x` is at most the rank of `y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  ≼-∈-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ∈-𝕎ᵉ yᵉ) → (xᵉ ≼-𝕎ᵉ yᵉ)
  ≼-∈-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} {tree-𝕎ᵉ yᵉ βᵉ} (pairᵉ vᵉ pᵉ) uᵉ =
    intro-existsᵉ
      ( vᵉ)
      ( trᵉ
        ( λ tᵉ → αᵉ uᵉ ≼-𝕎ᵉ tᵉ)
        ( invᵉ pᵉ)
        ( ≼-∈-𝕎ᵉ {αᵉ uᵉ} {tree-𝕎ᵉ xᵉ αᵉ} (pairᵉ uᵉ reflᵉ)))
```

### If `x ∈ y` then the rank of `x` is strictly lower than the rank of `y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  ≼-le-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ <-𝕎ᵉ yᵉ) → (xᵉ ≼-𝕎ᵉ yᵉ)
  ≼-le-𝕎ᵉ {xᵉ} {yᵉ} (le-∈-𝕎ᵉ Hᵉ) = ≼-∈-𝕎ᵉ Hᵉ
  ≼-le-𝕎ᵉ {xᵉ} {yᵉ} (propagate-le-𝕎ᵉ {yᵉ = y'ᵉ} Kᵉ Hᵉ) =
    transitive-≼-𝕎ᵉ {xᵉ = xᵉ} {yᵉ = y'ᵉ} {yᵉ} (≼-le-𝕎ᵉ Hᵉ) (≼-∈-𝕎ᵉ Kᵉ)
```

### If `x ∈ y` then the rank of `y` is not lower than the rank of `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  not-≼-∈-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ∈-𝕎ᵉ yᵉ) → ¬ᵉ (yᵉ ≼-𝕎ᵉ xᵉ)
  not-≼-∈-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} {tree-𝕎ᵉ yᵉ βᵉ} (pairᵉ bᵉ pᵉ) Kᵉ =
    apply-universal-property-trunc-Propᵉ (Kᵉ bᵉ) (empty-Propᵉ) fᵉ
    where
    fᵉ : Σᵉ (Bᵉ xᵉ) (λ cᵉ → βᵉ bᵉ ≼-𝕎ᵉ αᵉ cᵉ) → emptyᵉ
    fᵉ (pairᵉ cᵉ Lᵉ) =
      not-≼-∈-𝕎ᵉ {αᵉ cᵉ} {βᵉ bᵉ} (trᵉ (λ tᵉ → αᵉ cᵉ ∈-𝕎ᵉ tᵉ) (invᵉ pᵉ) (pairᵉ cᵉ reflᵉ)) Lᵉ
```

### If `x ∈ y` then the rank of `y` is not strictly below the rank of `x`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  not-≼-le-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ <-𝕎ᵉ yᵉ) → ¬ᵉ (yᵉ ≼-𝕎ᵉ xᵉ)
  not-≼-le-𝕎ᵉ {xᵉ} {yᵉ} (le-∈-𝕎ᵉ Hᵉ) = not-≼-∈-𝕎ᵉ {xᵉ = xᵉ} {yᵉ} Hᵉ
  not-≼-le-𝕎ᵉ {xᵉ} {yᵉ} (propagate-le-𝕎ᵉ {yᵉ = y'ᵉ} Hᵉ Kᵉ) Lᵉ =
    not-≼-∈-𝕎ᵉ {xᵉ = y'ᵉ} {yᵉ} Hᵉ (transitive-≼-𝕎ᵉ {xᵉ = yᵉ} {xᵉ} {y'ᵉ} Lᵉ (≼-le-𝕎ᵉ Kᵉ))
```

### Constants are elements of least rank

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-least-≼-constant-𝕎ᵉ :
    {xᵉ : Aᵉ} (hᵉ : is-emptyᵉ (Bᵉ xᵉ)) (wᵉ : 𝕎ᵉ Aᵉ Bᵉ) → constant-𝕎ᵉ xᵉ hᵉ ≼-𝕎ᵉ wᵉ
  is-least-≼-constant-𝕎ᵉ hᵉ (tree-𝕎ᵉ yᵉ βᵉ) xᵉ = ex-falsoᵉ (hᵉ xᵉ)

  is-least-≼-is-constant-𝕎ᵉ :
    {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} → is-constant-𝕎ᵉ xᵉ → (yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → xᵉ ≼-𝕎ᵉ yᵉ
  is-least-≼-is-constant-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} Hᵉ (tree-𝕎ᵉ yᵉ βᵉ) zᵉ =
    ex-falsoᵉ (Hᵉ zᵉ)

  is-constant-is-least-≼-𝕎ᵉ :
    {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} → ((yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → xᵉ ≼-𝕎ᵉ yᵉ) → is-constant-𝕎ᵉ xᵉ
  is-constant-is-least-≼-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} Hᵉ bᵉ =
    not-≼-∈-𝕎ᵉ {xᵉ = αᵉ bᵉ} {tree-𝕎ᵉ xᵉ αᵉ} (pairᵉ bᵉ reflᵉ) (Hᵉ (αᵉ bᵉ))
```

### If the rank of `x` is strictly below the rank of `y`, then the rank of `x` is at most the rank of `y`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  ≼-≺-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ≺-𝕎ᵉ yᵉ) → (xᵉ ≼-𝕎ᵉ yᵉ)
  ≼-≺-𝕎ᵉ {xᵉ} {yᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ (xᵉ ≼-𝕎-Propᵉ yᵉ) fᵉ
    where
    fᵉ : Σᵉ (Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (λ wᵉ → wᵉ ∈-𝕎ᵉ yᵉ)) (λ tᵉ → xᵉ ≼-𝕎ᵉ pr1ᵉ tᵉ) → (xᵉ ≼-𝕎ᵉ yᵉ)
    fᵉ (pairᵉ (pairᵉ wᵉ Kᵉ) Lᵉ) = transitive-≼-𝕎ᵉ {xᵉ = xᵉ} {wᵉ} {yᵉ} Lᵉ (≼-∈-𝕎ᵉ Kᵉ)
```

### Strict rank comparison is transitive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  transitive-≺-𝕎ᵉ : {xᵉ yᵉ zᵉ : 𝕎ᵉ Aᵉ Bᵉ} → (xᵉ ≺-𝕎ᵉ yᵉ) → (yᵉ ≺-𝕎ᵉ zᵉ) → (xᵉ ≺-𝕎ᵉ zᵉ)
  transitive-≺-𝕎ᵉ {xᵉ} {yᵉ} {zᵉ} Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ (xᵉ ≺-𝕎-Propᵉ zᵉ) fᵉ
    where
    fᵉ : Σᵉ (Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (λ wᵉ → wᵉ ∈-𝕎ᵉ yᵉ)) (λ tᵉ → xᵉ ≼-𝕎ᵉ pr1ᵉ tᵉ) → xᵉ ≺-𝕎ᵉ zᵉ
    fᵉ (pairᵉ (pairᵉ wᵉ Lᵉ) Mᵉ) =
      apply-universal-property-trunc-Propᵉ Kᵉ (xᵉ ≺-𝕎-Propᵉ zᵉ) gᵉ
      where
      gᵉ : Σᵉ (Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (λ wᵉ → wᵉ ∈-𝕎ᵉ zᵉ)) (λ tᵉ → yᵉ ≼-𝕎ᵉ pr1ᵉ tᵉ) → xᵉ ≺-𝕎ᵉ zᵉ
      gᵉ (pairᵉ (pairᵉ vᵉ Pᵉ) Qᵉ) =
        intro-existsᵉ
          ( pairᵉ vᵉ Pᵉ)
          ( transitive-≼-𝕎ᵉ {xᵉ = xᵉ} {wᵉ} {vᵉ} Mᵉ
            ( transitive-≼-𝕎ᵉ {xᵉ = wᵉ} {yᵉ} {vᵉ} (≼-∈-𝕎ᵉ Lᵉ) Qᵉ))
```

### Strict rank comparison is irreflexive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  irreflexive-≺-𝕎ᵉ : {xᵉ : 𝕎ᵉ Aᵉ Bᵉ} → ¬ᵉ (xᵉ ≺-𝕎ᵉ xᵉ)
  irreflexive-≺-𝕎ᵉ {tree-𝕎ᵉ xᵉ αᵉ} Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ empty-Propᵉ fᵉ
    where
    fᵉ :
      ¬ᵉ ( Σᵉ ( Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (λ wᵉ → wᵉ ∈-𝕎ᵉ tree-𝕎ᵉ xᵉ αᵉ))
            ( λ tᵉ → tree-𝕎ᵉ xᵉ αᵉ ≼-𝕎ᵉ pr1ᵉ tᵉ))
    fᵉ (pairᵉ (pairᵉ wᵉ Kᵉ) Lᵉ) = not-≼-∈-𝕎ᵉ {xᵉ = wᵉ} {tree-𝕎ᵉ xᵉ αᵉ} Kᵉ Lᵉ
```