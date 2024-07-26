# The opposite of a group

```agda
module group-theory.opposite-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.opposite-semigroupsᵉ
```

</details>

## Idea

Theᵉ **oppositeᵉ ofᵉ aᵉ [group](group-theory.groups.md)**ᵉ `G`ᵉ with multiplicationᵉ
`μ`ᵉ isᵉ aᵉ groupᵉ with theᵉ sameᵉ underlyingᵉ [set](foundation-core.sets.mdᵉ) asᵉ `G`ᵉ
andᵉ multiplicationᵉ givenᵉ byᵉ `xᵉ yᵉ ↦ᵉ μᵉ yᵉ x`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-unital-op-Groupᵉ : is-unital-Semigroupᵉ (op-Semigroupᵉ (semigroup-Groupᵉ Gᵉ))
  pr1ᵉ is-unital-op-Groupᵉ = unit-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ is-unital-op-Groupᵉ) = right-unit-law-mul-Groupᵉ Gᵉ
  pr2ᵉ (pr2ᵉ is-unital-op-Groupᵉ) = left-unit-law-mul-Groupᵉ Gᵉ

  is-group-op-Groupᵉ : is-group-Semigroupᵉ (op-Semigroupᵉ (semigroup-Groupᵉ Gᵉ))
  pr1ᵉ is-group-op-Groupᵉ = is-unital-op-Groupᵉ
  pr1ᵉ (pr2ᵉ is-group-op-Groupᵉ) = inv-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ is-group-op-Groupᵉ)) = right-inverse-law-mul-Groupᵉ Gᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ is-group-op-Groupᵉ)) = left-inverse-law-mul-Groupᵉ Gᵉ

  op-Groupᵉ : Groupᵉ lᵉ
  pr1ᵉ op-Groupᵉ = op-Semigroupᵉ (semigroup-Groupᵉ Gᵉ)
  pr2ᵉ op-Groupᵉ = is-group-op-Groupᵉ
```

## Properties

### The opposite group of `G` is isomorphic to `G`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  equiv-inv-Groupᵉ : equiv-Groupᵉ Gᵉ (op-Groupᵉ Gᵉ)
  pr1ᵉ equiv-inv-Groupᵉ = equiv-equiv-inv-Groupᵉ Gᵉ
  pr2ᵉ equiv-inv-Groupᵉ = distributive-inv-mul-Groupᵉ Gᵉ

  iso-inv-Groupᵉ : iso-Groupᵉ Gᵉ (op-Groupᵉ Gᵉ)
  iso-inv-Groupᵉ = iso-equiv-Groupᵉ Gᵉ (op-Groupᵉ Gᵉ) equiv-inv-Groupᵉ
```