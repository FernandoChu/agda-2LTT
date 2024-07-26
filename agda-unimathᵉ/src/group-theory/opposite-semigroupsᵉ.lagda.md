# The opposite of a semigroup

```agda
module group-theory.opposite-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ **oppositeᵉ ofᵉ aᵉ [semigroup](group-theory.semigroups.md)**ᵉ `G`ᵉ with
multiplicationᵉ `μ`ᵉ isᵉ aᵉ semigroupᵉ with theᵉ sameᵉ underlyingᵉ
[set](foundation-core.sets.mdᵉ) asᵉ `G`ᵉ andᵉ multiplicationᵉ givenᵉ byᵉ `xᵉ yᵉ ↦ᵉ μᵉ yᵉ x`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  set-op-Semigroupᵉ : Setᵉ lᵉ
  set-op-Semigroupᵉ = set-Semigroupᵉ Gᵉ

  type-op-Semigroupᵉ : UUᵉ lᵉ
  type-op-Semigroupᵉ = type-Setᵉ set-op-Semigroupᵉ

  mul-op-Semigroupᵉ : type-op-Semigroupᵉ → type-op-Semigroupᵉ → type-op-Semigroupᵉ
  mul-op-Semigroupᵉ xᵉ yᵉ = mul-Semigroupᵉ Gᵉ yᵉ xᵉ

  associative-mul-op-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-op-Semigroupᵉ) →
    mul-Semigroupᵉ Gᵉ zᵉ (mul-Semigroupᵉ Gᵉ yᵉ xᵉ) ＝ᵉ
    mul-Semigroupᵉ Gᵉ (mul-Semigroupᵉ Gᵉ zᵉ yᵉ) xᵉ
  associative-mul-op-Semigroupᵉ xᵉ yᵉ zᵉ = invᵉ (associative-mul-Semigroupᵉ Gᵉ zᵉ yᵉ xᵉ)

  op-Semigroupᵉ : Semigroupᵉ lᵉ
  pr1ᵉ op-Semigroupᵉ = set-op-Semigroupᵉ
  pr1ᵉ (pr2ᵉ op-Semigroupᵉ) = mul-op-Semigroupᵉ
  pr2ᵉ (pr2ᵉ op-Semigroupᵉ) = associative-mul-op-Semigroupᵉ
```