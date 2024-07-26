# Trivial groups

```agda
module group-theory.trivial-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.full-subgroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.trivial-subgroupsᵉ
```

</details>

## Idea

Aᵉ [group](group-theory.groups.mdᵉ) isᵉ saidᵉ to beᵉ **trivial**ᵉ ifᵉ itsᵉ underlyingᵉ
typeᵉ isᵉ [contractible](foundation-core.contractible-types.md).ᵉ Inᵉ otherᵉ words,ᵉ aᵉ
groupᵉ isᵉ trivialᵉ ifᵉ itᵉ consistsᵉ onlyᵉ ofᵉ theᵉ unitᵉ element.ᵉ

## Definitions

### The predicate of being a trivial group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-trivial-prop-Groupᵉ : Propᵉ l1ᵉ
  is-trivial-prop-Groupᵉ = is-contr-Propᵉ (type-Groupᵉ Gᵉ)

  is-trivial-Groupᵉ : UUᵉ l1ᵉ
  is-trivial-Groupᵉ = type-Propᵉ is-trivial-prop-Groupᵉ
```

### The type of trivial groups

```agda
Trivial-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Trivial-Groupᵉ lᵉ = Σᵉ (Groupᵉ lᵉ) is-trivial-Groupᵉ
```

### The trivial group

```agda
trivial-Groupᵉ : Groupᵉ lzero
pr1ᵉ (pr1ᵉ trivial-Groupᵉ) = unit-Setᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ trivial-Groupᵉ)) xᵉ yᵉ = starᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ trivial-Groupᵉ)) xᵉ yᵉ zᵉ = reflᵉ
pr1ᵉ (pr2ᵉ trivial-Groupᵉ) = (starᵉ ,ᵉ (refl-htpyᵉ ,ᵉ refl-htpyᵉ))
pr2ᵉ (pr2ᵉ trivial-Groupᵉ) = ((λ xᵉ → starᵉ) ,ᵉ refl-htpyᵉ ,ᵉ refl-htpyᵉ)
```

## Properties

### The type of subgroups of a trivial group is contractible

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  abstract
    is-contr-subgroup-is-trivial-Groupᵉ :
      is-trivial-Groupᵉ Gᵉ → is-contrᵉ (Subgroupᵉ l1ᵉ Gᵉ)
    pr1ᵉ (is-contr-subgroup-is-trivial-Groupᵉ Hᵉ) =
      trivial-Subgroupᵉ Gᵉ
    pr2ᵉ (is-contr-subgroup-is-trivial-Groupᵉ Hᵉ) Kᵉ =
      eq-has-same-elements-Subgroupᵉ Gᵉ
        ( trivial-Subgroupᵉ Gᵉ)
        ( Kᵉ)
        ( λ xᵉ →
          ( λ where reflᵉ → contains-unit-Subgroupᵉ Gᵉ Kᵉ) ,ᵉ
          ( λ _ →
            is-closed-under-eq-Subgroupᵉ Gᵉ
              ( trivial-Subgroupᵉ Gᵉ)
              ( contains-unit-Subgroupᵉ Gᵉ (trivial-Subgroupᵉ Gᵉ))
              ( eq-is-contrᵉ Hᵉ)))
```

### The trivial group is abelian

```agda
is-abelian-trivial-Groupᵉ : is-abelian-Groupᵉ trivial-Groupᵉ
is-abelian-trivial-Groupᵉ xᵉ yᵉ = reflᵉ

trivial-Abᵉ : Abᵉ lzero
trivial-Abᵉ = (trivial-Groupᵉ ,ᵉ is-abelian-trivial-Groupᵉ)
```