# Similarity of elements in large preorders

```agda
module order-theory.similarity-of-elements-large-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-preordersᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [largeᵉ preorder](order-theory.large-preorders.mdᵉ)
`P`ᵉ areᵉ saidᵉ to beᵉ **similar**ᵉ ifᵉ bothᵉ `xᵉ ≤ᵉ y`ᵉ andᵉ `yᵉ ≤ᵉ x`ᵉ hold.ᵉ

Inᵉ informalᵉ writingᵉ weᵉ willᵉ useᵉ theᵉ notationᵉ `xᵉ ≈ᵉ y`ᵉ to assertᵉ thatᵉ `x`ᵉ andᵉ `y`ᵉ
areᵉ similarᵉ elementsᵉ in aᵉ preorderᵉ `P`.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  sim-prop-Large-Preorderᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Preorderᵉ Pᵉ l2ᵉ) →
    Propᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ)
  sim-prop-Large-Preorderᵉ xᵉ yᵉ =
    product-Propᵉ
      ( leq-prop-Large-Preorderᵉ Pᵉ xᵉ yᵉ)
      ( leq-prop-Large-Preorderᵉ Pᵉ yᵉ xᵉ)

  sim-Large-Preorderᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Preorderᵉ Pᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ)
  sim-Large-Preorderᵉ xᵉ yᵉ = type-Propᵉ (sim-prop-Large-Preorderᵉ xᵉ yᵉ)

  is-prop-sim-Large-Preorderᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Preorderᵉ Pᵉ l2ᵉ) →
    is-propᵉ (sim-Large-Preorderᵉ xᵉ yᵉ)
  is-prop-sim-Large-Preorderᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (sim-prop-Large-Preorderᵉ xᵉ yᵉ)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  refl-sim-Large-Preorderᵉ :
    is-reflexive-Large-Relationᵉ (type-Large-Preorderᵉ Pᵉ) (sim-Large-Preorderᵉ Pᵉ)
  pr1ᵉ (refl-sim-Large-Preorderᵉ xᵉ) = refl-leq-Large-Preorderᵉ Pᵉ xᵉ
  pr2ᵉ (refl-sim-Large-Preorderᵉ xᵉ) = refl-leq-Large-Preorderᵉ Pᵉ xᵉ
```

### The similarity relation is transitive

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  transitive-sim-Large-Preorderᵉ :
    is-transitive-Large-Relationᵉ (type-Large-Preorderᵉ Pᵉ) (sim-Large-Preorderᵉ Pᵉ)
  pr1ᵉ (transitive-sim-Large-Preorderᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ) =
    transitive-leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ zᵉ (pr1ᵉ Hᵉ) (pr1ᵉ Kᵉ)
  pr2ᵉ (transitive-sim-Large-Preorderᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ) =
    transitive-leq-Large-Preorderᵉ Pᵉ zᵉ yᵉ xᵉ (pr2ᵉ Kᵉ) (pr2ᵉ Hᵉ)
```

### The similarity relation is symmetric

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  symmetric-sim-Large-Preorderᵉ :
    is-symmetric-Large-Relationᵉ (type-Large-Preorderᵉ Pᵉ) (sim-Large-Preorderᵉ Pᵉ)
  pr1ᵉ (symmetric-sim-Large-Preorderᵉ _ _ Hᵉ) = pr2ᵉ Hᵉ
  pr2ᵉ (symmetric-sim-Large-Preorderᵉ _ _ Hᵉ) = pr1ᵉ Hᵉ
```

### Equal elements are similar

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αᵉ βᵉ)
  where

  sim-eq-Large-Preorderᵉ :
    {lᵉ : Level} {xᵉ yᵉ : type-Large-Preorderᵉ Pᵉ lᵉ} →
    xᵉ ＝ᵉ yᵉ → sim-Large-Preorderᵉ Pᵉ xᵉ yᵉ
  sim-eq-Large-Preorderᵉ reflᵉ = refl-sim-Large-Preorderᵉ Pᵉ _
```