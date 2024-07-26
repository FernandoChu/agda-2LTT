# Negated equality

```agda
module foundation.negated-equalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ areᵉ **notᵉ equal**ᵉ wheneverᵉ `¬ᵉ (xᵉ ＝ᵉ y)`ᵉ isᵉ inhabited.ᵉ

## Definition

```agda
nonequalᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → Aᵉ → UUᵉ lᵉ
nonequalᵉ xᵉ yᵉ = ¬ᵉ (xᵉ ＝ᵉ yᵉ)

infix 6 _≠ᵉ_
_≠ᵉ_ = nonequalᵉ
```

## Properties

### Nonequality is a property

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-prop-nonequalᵉ : {xᵉ yᵉ : Aᵉ} → is-propᵉ (xᵉ ≠ᵉ yᵉ)
  is-prop-nonequalᵉ = is-prop-negᵉ

  nonequal-Propᵉ : (xᵉ yᵉ : Aᵉ) → Propᵉ lᵉ
  pr1ᵉ (nonequal-Propᵉ xᵉ yᵉ) = xᵉ ≠ᵉ yᵉ
  pr2ᵉ (nonequal-Propᵉ xᵉ yᵉ) = is-prop-nonequalᵉ
```

### Nonequality is antireflexive

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-antireflexive-nonequalᵉ : (aᵉ : Aᵉ) → ¬ᵉ (aᵉ ≠ᵉ aᵉ)
  is-antireflexive-nonequalᵉ aᵉ dᵉ = dᵉ reflᵉ

  is-consistent-nonequalᵉ : (aᵉ bᵉ : Aᵉ) → (aᵉ ＝ᵉ bᵉ) → ¬ᵉ (aᵉ ≠ᵉ bᵉ)
  is-consistent-nonequalᵉ aᵉ bᵉ pᵉ dᵉ = dᵉ pᵉ
```

### Nonequality is symmetric

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-symmetric-nonequalᵉ : is-symmetricᵉ (nonequalᵉ {Aᵉ = Aᵉ})
  is-symmetric-nonequalᵉ aᵉ bᵉ = map-negᵉ invᵉ
```

### If two functions are nonequal at a point, they are nonequal as functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  nonequal-Πᵉ : (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) (aᵉ : Aᵉ) → fᵉ aᵉ ≠ᵉ gᵉ aᵉ → fᵉ ≠ᵉ gᵉ
  nonequal-Πᵉ fᵉ gᵉ aᵉ = map-negᵉ (λ hᵉ → htpy-eqᵉ hᵉ aᵉ)
```

### If either component of two pairs are nonequal, the pairs are nonequal

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  nonequal-pr1ᵉ : (uᵉ vᵉ : Σᵉ Aᵉ Bᵉ) → pr1ᵉ uᵉ ≠ᵉ pr1ᵉ vᵉ → uᵉ ≠ᵉ vᵉ
  nonequal-pr1ᵉ uᵉ vᵉ = map-negᵉ (apᵉ pr1ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  nonequal-product-pr2ᵉ : (uᵉ vᵉ : Aᵉ ×ᵉ Bᵉ) → pr2ᵉ uᵉ ≠ᵉ pr2ᵉ vᵉ → uᵉ ≠ᵉ vᵉ
  nonequal-product-pr2ᵉ uᵉ vᵉ = map-negᵉ (apᵉ pr2ᵉ)
```

### If there is a reflexive relation that does not relate `a` and `b`, then they are nonequal

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  nonequal-reflexive-relationᵉ :
    (Rᵉ : Relationᵉ l2ᵉ Aᵉ) → is-reflexiveᵉ Rᵉ → (aᵉ bᵉ : Aᵉ) → ¬ᵉ (Rᵉ aᵉ bᵉ) → aᵉ ≠ᵉ bᵉ
  nonequal-reflexive-relationᵉ Rᵉ is-refl-Rᵉ aᵉ .aᵉ rᵉ reflᵉ = rᵉ (is-refl-Rᵉ aᵉ)
```

### If there is any family on `A` that is inhabited over one term but not the other, then they are nonequal

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  nonequal-leibnizᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → (aᵉ bᵉ : Aᵉ) → Bᵉ aᵉ → ¬ᵉ (Bᵉ bᵉ) → aᵉ ≠ᵉ bᵉ
  nonequal-leibnizᵉ Bᵉ aᵉ .aᵉ a'ᵉ b'ᵉ reflᵉ = b'ᵉ a'ᵉ

  nonequal-leibniz'ᵉ : (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → (aᵉ bᵉ : Aᵉ) → ¬ᵉ (Bᵉ aᵉ) → Bᵉ bᵉ → aᵉ ≠ᵉ bᵉ
  nonequal-leibniz'ᵉ Bᵉ aᵉ .aᵉ a'ᵉ b'ᵉ reflᵉ = a'ᵉ b'ᵉ
```

## See also

-ᵉ [Apartnessᵉ relations](foundation.apartness-relations.mdᵉ)