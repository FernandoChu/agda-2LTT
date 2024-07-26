# Mere lifting properties

```agda
module orthogonal-factorization-systems.mere-lifting-propertiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Givenᵉ twoᵉ maps,ᵉ `fᵉ : Aᵉ → X`ᵉ andᵉ `gᵉ : Bᵉ → Y`,ᵉ weᵉ sayᵉ thatᵉ `f`ᵉ hasᵉ theᵉ **mereᵉ leftᵉ
liftingᵉ property**ᵉ with respectᵉ to `g`ᵉ andᵉ thatᵉ `g`ᵉ hasᵉ theᵉ **mereᵉ rightᵉ liftingᵉ
property**ᵉ with respectᵉ to `f`ᵉ ifᵉ theᵉ
[pullback-hom](orthogonal-factorization-systems.pullback-hom.mdᵉ) isᵉ
[surjective](foundation.surjective-maps.md).ᵉ Thisᵉ meansᵉ thatᵉ theᵉ typeᵉ ofᵉ
[liftingᵉ operations](orthogonal-factorization-systems.lifting-operations.mdᵉ)
betweenᵉ `f`ᵉ andᵉ `g`ᵉ isᵉ merelyᵉ [inhabited](foundation.inhabited-types.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  mere-diagonal-liftᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  mere-diagonal-liftᵉ = is-surjectiveᵉ (pullback-homᵉ fᵉ gᵉ)
```

## Properties

### Mere lifting properties are properties

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Yᵉ)
  where

  is-prop-mere-diagonal-liftᵉ : is-propᵉ (mere-diagonal-liftᵉ fᵉ gᵉ)
  is-prop-mere-diagonal-liftᵉ = is-prop-is-surjectiveᵉ (pullback-homᵉ fᵉ gᵉ)

  mere-diagonal-lift-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  mere-diagonal-lift-Propᵉ = is-surjective-Propᵉ (pullback-homᵉ fᵉ gᵉ)
```