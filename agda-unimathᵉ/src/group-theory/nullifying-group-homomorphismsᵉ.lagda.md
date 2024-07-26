# Nullifying group homomorphisms

```agda
module group-theory.nullifying-group-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-groups-equipped-with-normal-subgroupsᵉ
open import group-theory.kernels-homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → H`ᵉ andᵉ aᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) `N`ᵉ ofᵉ theᵉ
[group](group-theory.groups.mdᵉ) `G`.ᵉ Weᵉ sayᵉ thatᵉ `f`ᵉ **nullifies**ᵉ `N`ᵉ ifᵉ itᵉ
satisfiesᵉ theᵉ conditionᵉ

```text
  Nᵉ ⊆ᵉ kerᵉ f,ᵉ
```

i.e.,ᵉ ifᵉ `fᵉ xᵉ ＝ᵉ 1`ᵉ forᵉ allᵉ `xᵉ ∈ᵉ N`.ᵉ Nullifyingᵉ groupᵉ homomorphismsᵉ areᵉ usedᵉ to
defineᵉ [quotientᵉ groups](group-theory.quotient-groups.md).ᵉ

## Definitions

### The predicate of nullifying a normal subgroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Kᵉ : Groupᵉ l2ᵉ)
  where

  nullifies-normal-subgroup-prop-hom-Groupᵉ :
    hom-Groupᵉ Gᵉ Kᵉ → Normal-Subgroupᵉ l3ᵉ Gᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifies-normal-subgroup-prop-hom-Groupᵉ fᵉ Hᵉ =
    leq-prop-Normal-Subgroupᵉ Gᵉ Hᵉ (kernel-hom-Groupᵉ Gᵉ Kᵉ fᵉ)

  nullifies-normal-subgroup-hom-Groupᵉ :
    hom-Groupᵉ Gᵉ Kᵉ → Normal-Subgroupᵉ l3ᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifies-normal-subgroup-hom-Groupᵉ fᵉ Hᵉ =
    type-Propᵉ (nullifies-normal-subgroup-prop-hom-Groupᵉ fᵉ Hᵉ)
```

### Group homomorphisms that nullify a normal subgroup, i.e., that contain a normal subgroup in their kernel

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Kᵉ : Groupᵉ l2ᵉ) (Hᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ)
  where

  nullifying-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  nullifying-hom-Groupᵉ =
    type-subtypeᵉ (λ fᵉ → nullifies-normal-subgroup-prop-hom-Groupᵉ Gᵉ Kᵉ fᵉ Hᵉ)

  hom-nullifying-hom-Groupᵉ :
    nullifying-hom-Groupᵉ → hom-Groupᵉ Gᵉ Kᵉ
  hom-nullifying-hom-Groupᵉ = pr1ᵉ

  nullifies-normal-subgroup-nullifying-hom-Groupᵉ :
    (fᵉ : nullifying-hom-Groupᵉ) →
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ
      ( hom-nullifying-hom-Groupᵉ fᵉ) Hᵉ
  nullifies-normal-subgroup-nullifying-hom-Groupᵉ = pr2ᵉ
```

## Properties

### A group homomorphism nullifies a normal subgroup if and only if it reflects the equivalence relation induced by the normal subgroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Kᵉ : Groupᵉ l2ᵉ)
  (Hᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ)
  where

  reflects-equivalence-relation-nullifies-normal-subgroup-hom-Groupᵉ :
    (fᵉ : hom-Groupᵉ Gᵉ Kᵉ) →
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ fᵉ Hᵉ →
    reflects-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Hᵉ)
      ( map-hom-Groupᵉ Gᵉ Kᵉ fᵉ)
  reflects-equivalence-relation-nullifies-normal-subgroup-hom-Groupᵉ fᵉ pᵉ αᵉ =
    ( invᵉ (right-unit-law-mul-Groupᵉ Kᵉ _)) ∙ᵉ
    ( inv-transpose-eq-mul-Group'ᵉ Kᵉ
      ( ( pᵉ (left-div-Groupᵉ Gᵉ _ _) αᵉ) ∙ᵉ
        ( preserves-left-div-hom-Groupᵉ Gᵉ Kᵉ fᵉ)))

  nullifies-normal-subgroup-reflects-equivalence-relation-hom-Groupᵉ :
    (fᵉ : hom-Groupᵉ Gᵉ Kᵉ) →
    reflects-equivalence-relationᵉ
      ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Hᵉ)
      ( map-hom-Groupᵉ Gᵉ Kᵉ fᵉ) →
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ fᵉ Hᵉ
  nullifies-normal-subgroup-reflects-equivalence-relation-hom-Groupᵉ fᵉ pᵉ xᵉ qᵉ =
    ( invᵉ (preserves-unit-hom-Groupᵉ Gᵉ Kᵉ fᵉ)) ∙ᵉ
    ( pᵉ ( is-closed-under-multiplication-Normal-Subgroupᵉ Gᵉ Hᵉ
          ( is-closed-under-inverses-Normal-Subgroupᵉ Gᵉ Hᵉ
            ( contains-unit-Normal-Subgroupᵉ Gᵉ Hᵉ))
          ( qᵉ)))

  compute-nullifying-hom-Groupᵉ :
    Σᵉ ( reflecting-map-equivalence-relationᵉ
        ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Hᵉ)
        ( type-Groupᵉ Kᵉ))
      ( λ fᵉ → preserves-mul-Groupᵉ Gᵉ Kᵉ (pr1ᵉ fᵉ)) ≃ᵉ
    nullifying-hom-Groupᵉ Gᵉ Kᵉ Hᵉ
  compute-nullifying-hom-Groupᵉ =
    ( equiv-type-subtypeᵉ
      ( λ fᵉ →
        is-prop-reflects-equivalence-relationᵉ
          ( equivalence-relation-congruence-Normal-Subgroupᵉ Gᵉ Hᵉ)
          ( set-Groupᵉ Kᵉ)
          ( pr1ᵉ fᵉ))
      ( λ fᵉ → is-prop-leq-Normal-Subgroupᵉ Gᵉ Hᵉ (kernel-hom-Groupᵉ Gᵉ Kᵉ fᵉ))
      ( nullifies-normal-subgroup-reflects-equivalence-relation-hom-Groupᵉ)
      ( reflects-equivalence-relation-nullifies-normal-subgroup-hom-Groupᵉ)) ∘eᵉ
    ( equiv-right-swap-Σᵉ)
```

### Composition of nullifying homomorphisms and reflecting homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l4ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l5ᵉ Hᵉ)
  where

  hom-comp-nullifying-hom-reflecting-hom-Groupᵉ :
    nullifying-hom-Groupᵉ Hᵉ Kᵉ Mᵉ →
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ →
    hom-Groupᵉ Gᵉ Kᵉ
  hom-comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ =
    comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ
      ( hom-nullifying-hom-Groupᵉ Hᵉ Kᵉ Mᵉ gᵉ)
      ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ)

  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Groupᵉ :
    ( gᵉ : nullifying-hom-Groupᵉ Hᵉ Kᵉ Mᵉ)
    ( fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ) →
    nullifies-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ
      ( hom-comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ)
      ( Nᵉ)
  nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ xᵉ nᵉ =
    nullifies-normal-subgroup-nullifying-hom-Groupᵉ Hᵉ Kᵉ Mᵉ gᵉ
      ( map-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ xᵉ)
      ( reflects-normal-subgroup-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ xᵉ nᵉ)

  comp-nullifying-hom-reflecting-hom-Groupᵉ :
    nullifying-hom-Groupᵉ Hᵉ Kᵉ Mᵉ →
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ →
    nullifying-hom-Groupᵉ Gᵉ Kᵉ Nᵉ
  pr1ᵉ (comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ) =
    hom-comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ
  pr2ᵉ (comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ) =
    nullifies-normal-subgroup-comp-nullifying-hom-reflecting-hom-Groupᵉ gᵉ fᵉ
```

## See also

-ᵉ [Homomorphismsᵉ ofᵉ groupsᵉ equippedᵉ with normalᵉ subgroups](group-theory.homomorphisms-groups-equipped-with-normal-subgroups.mdᵉ)