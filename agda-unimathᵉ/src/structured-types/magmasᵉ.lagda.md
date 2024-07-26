# Magmas

```agda
module structured-types.magmasᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "magma"ᵉ Agda=Magmaᵉ}} isᵉ aᵉ typeᵉ [equipped](foundation.structure.mdᵉ)
with aᵉ binaryᵉ operation.ᵉ

## Definition

```agda
Magmaᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Magmaᵉ lᵉ = Σᵉ (UUᵉ lᵉ) (λ Aᵉ → Aᵉ → Aᵉ → Aᵉ)

module _
  {lᵉ : Level} (Mᵉ : Magmaᵉ lᵉ)
  where

  type-Magmaᵉ : UUᵉ lᵉ
  type-Magmaᵉ = pr1ᵉ Mᵉ

  mul-Magmaᵉ : type-Magmaᵉ → type-Magmaᵉ → type-Magmaᵉ
  mul-Magmaᵉ = pr2ᵉ Mᵉ

  mul-Magma'ᵉ : type-Magmaᵉ → type-Magmaᵉ → type-Magmaᵉ
  mul-Magma'ᵉ xᵉ yᵉ = mul-Magmaᵉ yᵉ xᵉ
```

## Structures

### Unital magmas

```agda
is-unital-Magmaᵉ : {lᵉ : Level} (Mᵉ : Magmaᵉ lᵉ) → UUᵉ lᵉ
is-unital-Magmaᵉ Mᵉ = is-unitalᵉ (mul-Magmaᵉ Mᵉ)

Unital-Magmaᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Unital-Magmaᵉ lᵉ = Σᵉ (Magmaᵉ lᵉ) is-unital-Magmaᵉ

magma-Unital-Magmaᵉ :
  {lᵉ : Level} → Unital-Magmaᵉ lᵉ → Magmaᵉ lᵉ
magma-Unital-Magmaᵉ Mᵉ = pr1ᵉ Mᵉ

is-unital-magma-Unital-Magmaᵉ :
  {lᵉ : Level} (Mᵉ : Unital-Magmaᵉ lᵉ) → is-unital-Magmaᵉ (magma-Unital-Magmaᵉ Mᵉ)
is-unital-magma-Unital-Magmaᵉ Mᵉ = pr2ᵉ Mᵉ
```

### Semigroups

```agda
is-semigroup-Magmaᵉ : {lᵉ : Level} → Magmaᵉ lᵉ → UUᵉ lᵉ
is-semigroup-Magmaᵉ Mᵉ =
  (xᵉ yᵉ zᵉ : type-Magmaᵉ Mᵉ) →
  Idᵉ (mul-Magmaᵉ Mᵉ (mul-Magmaᵉ Mᵉ xᵉ yᵉ) zᵉ) (mul-Magmaᵉ Mᵉ xᵉ (mul-Magmaᵉ Mᵉ yᵉ zᵉ))
```

### Commutative magmas

```agda
is-commutative-Magmaᵉ : {lᵉ : Level} → Magmaᵉ lᵉ → UUᵉ lᵉ
is-commutative-Magmaᵉ Mᵉ =
  (xᵉ yᵉ : type-Magmaᵉ Mᵉ) → Idᵉ (mul-Magmaᵉ Mᵉ xᵉ yᵉ) (mul-Magmaᵉ Mᵉ yᵉ xᵉ)
```

### The structure of a commutative monoid on magmas

```agda
is-commutative-monoid-Magmaᵉ : {lᵉ : Level} → Magmaᵉ lᵉ → UUᵉ lᵉ
is-commutative-monoid-Magmaᵉ Mᵉ =
  ((is-semigroup-Magmaᵉ Mᵉ) ×ᵉ (is-unital-Magmaᵉ Mᵉ)) ×ᵉ (is-commutative-Magmaᵉ Mᵉ)

unit-is-commutative-monoid-Magmaᵉ :
  {lᵉ : Level} (Mᵉ : Magmaᵉ lᵉ) → is-commutative-monoid-Magmaᵉ Mᵉ → type-Magmaᵉ Mᵉ
unit-is-commutative-monoid-Magmaᵉ Mᵉ Hᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ Hᵉ))
```