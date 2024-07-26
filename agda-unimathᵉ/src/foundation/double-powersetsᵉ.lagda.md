# Double powersets

```agda
module foundation.double-powersetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.powersetsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ

open import order-theory.large-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Definitions

### The double powerset

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level)
  where

  double-powerset-Large-Posetᵉ :
    UUᵉ l1ᵉ →
    Large-Posetᵉ
      ( λ l3ᵉ → l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
      ( λ l3ᵉ l4ᵉ → l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  double-powerset-Large-Posetᵉ Aᵉ = powerset-Large-Posetᵉ (powersetᵉ l2ᵉ Aᵉ)

  double-powerset-Posetᵉ :
    (lᵉ : Level) → UUᵉ l1ᵉ → Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lᵉ)
  double-powerset-Posetᵉ lᵉ Aᵉ =
    poset-Large-Posetᵉ (double-powerset-Large-Posetᵉ Aᵉ) lᵉ

  double-powersetᵉ : (l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  double-powersetᵉ l3ᵉ Aᵉ = type-Posetᵉ (double-powerset-Posetᵉ l3ᵉ Aᵉ)
```

## Operations on the double powerset

### Intersections of subtypes of powersets

```agda
intersection-double-powersetᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  double-powersetᵉ l2ᵉ l3ᵉ Aᵉ → powersetᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ) Aᵉ
intersection-double-powersetᵉ Fᵉ aᵉ =
  Π-Propᵉ (type-subtypeᵉ Fᵉ) (λ Xᵉ → inclusion-subtypeᵉ Fᵉ Xᵉ aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Fᵉ : double-powersetᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  inclusion-intersection-double-powersetᵉ :
    (Xᵉ : type-subtypeᵉ Fᵉ) →
    intersection-double-powersetᵉ Fᵉ ⊆ᵉ inclusion-subtypeᵉ Fᵉ Xᵉ
  inclusion-intersection-double-powersetᵉ Xᵉ aᵉ fᵉ = fᵉ Xᵉ

  universal-property-intersection-double-powersetᵉ :
    {lᵉ : Level} (Pᵉ : powersetᵉ lᵉ Aᵉ)
    (Hᵉ : (Xᵉ : type-subtypeᵉ Fᵉ) → Pᵉ ⊆ᵉ inclusion-subtypeᵉ Fᵉ Xᵉ) →
    Pᵉ ⊆ᵉ intersection-double-powersetᵉ Fᵉ
  universal-property-intersection-double-powersetᵉ Pᵉ Hᵉ aᵉ pᵉ Xᵉ = Hᵉ Xᵉ aᵉ pᵉ
```

### Unions of subtypes of powersets

```agda
union-double-powersetᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  double-powersetᵉ l2ᵉ l3ᵉ Aᵉ → powersetᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ) Aᵉ
union-double-powersetᵉ Fᵉ aᵉ =
  ∃ᵉ (type-subtypeᵉ Fᵉ) (λ Xᵉ → inclusion-subtypeᵉ Fᵉ Xᵉ aᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Fᵉ : double-powersetᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  type-union-double-powersetᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  type-union-double-powersetᵉ = type-subtypeᵉ (union-double-powersetᵉ Fᵉ)

  inclusion-union-double-powersetᵉ :
    (Xᵉ : type-subtypeᵉ Fᵉ) → inclusion-subtypeᵉ Fᵉ Xᵉ ⊆ᵉ union-double-powersetᵉ Fᵉ
  inclusion-union-double-powersetᵉ Xᵉ aᵉ = intro-existsᵉ Xᵉ

  universal-property-union-double-powersetᵉ :
    {lᵉ : Level} (Pᵉ : powersetᵉ lᵉ Aᵉ)
    (Hᵉ : (Xᵉ : type-subtypeᵉ Fᵉ) → inclusion-subtypeᵉ Fᵉ Xᵉ ⊆ᵉ Pᵉ) →
    union-double-powersetᵉ Fᵉ ⊆ᵉ Pᵉ
  universal-property-union-double-powersetᵉ Pᵉ Hᵉ aᵉ =
    map-universal-property-trunc-Propᵉ
      ( Pᵉ aᵉ)
      ( λ Xᵉ → Hᵉ (pr1ᵉ Xᵉ) aᵉ (pr2ᵉ Xᵉ))
```