# Torsion-free groups

```agda
module group-theory.torsion-free-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.singleton-subtypesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.integer-powers-of-elements-groupsᵉ
open import group-theory.orders-of-elements-groupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.torsion-elements-groupsᵉ
```

</details>

## Idea

Aᵉ **torsion-freeᵉ group**ᵉ isᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ in whichᵉ anyᵉ
elementᵉ ofᵉ finiteᵉ [order](group-theory.orders-of-elements-groups.mdᵉ) isᵉ theᵉ
identityᵉ element.ᵉ Inᵉ otherᵉ words,ᵉ torsion-freeᵉ groupsᵉ areᵉ groupsᵉ in whichᵉ theᵉ
conditionᵉ

```text
  ∀ᵉ (kᵉ : nonzero-ℤ),ᵉ xᵏᵉ ＝ᵉ 1 → xᵉ ＝ᵉ 1
```

holdsᵉ forᵉ allᵉ elementsᵉ `xᵉ : G`.ᵉ Thisᵉ conditionᵉ canᵉ beᵉ formulatedᵉ in severalᵉ
[equivalent](foundation.logical-equivalences.mdᵉ) waysᵉ:

1.ᵉ `∀ᵉ (kᵉ : nonzero-ℤ),ᵉ xᵏᵉ ＝ᵉ 1 → xᵉ ＝ᵉ 1`.ᵉ
2.ᵉ Theᵉ [subset](group-theory.subsets-groups.mdᵉ) ofᵉ `G`ᵉ ofᵉ
   [torsionᵉ elements](group-theory.torsion-elements-groups.mdᵉ) isᵉ aᵉ
   [singletonᵉ subtype](foundation.singleton-subtypes.md).ᵉ
3.ᵉ Theᵉ mapᵉ `p`ᵉ in theᵉ [pullbackᵉ square](foundation-core.pullbacks.mdᵉ)
   ```text
             qᵉ
       ·ᵉ --------->ᵉ Propᵉ
       | ⌟ᵉ            |
      p|ᵉ              | Pᵉ ↦ᵉ {kᵉ : ℤᵉ ∣ᵉ (kᵉ ＝ᵉ 0ᵉ) ∨ᵉ Pᵉ}
       ∨ᵉ              ∨ᵉ
       Gᵉ ------->ᵉ Subgroupᵉ ℤᵉ
          orderᵉ
   ```
   isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

## Definitions

### The predicate of being a torsion-free group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-torsion-free-prop-Groupᵉ : Propᵉ l1ᵉ
  is-torsion-free-prop-Groupᵉ =
    Π-Propᵉ
      ( type-Groupᵉ Gᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( nonzero-ℤᵉ)
          ( λ kᵉ →
            function-Propᵉ
              ( integer-power-Groupᵉ Gᵉ (int-nonzero-ℤᵉ kᵉ) xᵉ ＝ᵉ unit-Groupᵉ Gᵉ)
              ( Id-Propᵉ (set-Groupᵉ Gᵉ) xᵉ (unit-Groupᵉ Gᵉ))))

  is-torsion-free-Groupᵉ : UUᵉ l1ᵉ
  is-torsion-free-Groupᵉ = type-Propᵉ is-torsion-free-prop-Groupᵉ

  is-prop-is-torsion-free-Groupᵉ : is-propᵉ is-torsion-free-Groupᵉ
  is-prop-is-torsion-free-Groupᵉ = is-prop-type-Propᵉ is-torsion-free-prop-Groupᵉ
```

### The predicate that a group has a unique torsion element

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  has-unique-torsion-element-prop-Groupᵉ : Propᵉ l1ᵉ
  has-unique-torsion-element-prop-Groupᵉ =
    is-singleton-subtype-Propᵉ (is-torsion-element-prop-Groupᵉ Gᵉ)

  has-unique-torsion-element-Groupᵉ : UUᵉ l1ᵉ
  has-unique-torsion-element-Groupᵉ =
    is-singleton-subtypeᵉ (is-torsion-element-prop-Groupᵉ Gᵉ)

  is-prop-has-unique-torsion-element-Groupᵉ :
    is-propᵉ has-unique-torsion-element-Groupᵉ
  is-prop-has-unique-torsion-element-Groupᵉ =
    is-prop-is-singleton-subtypeᵉ (is-torsion-element-prop-Groupᵉ Gᵉ)
```

### The predicate that the first projection of the pullback of `Prop lzero → Subgroup ℤ` along `order : G → Subgroup ℤ` is an equivalence

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Groupᵉ :
    Propᵉ (lsuc l1ᵉ)
  is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Groupᵉ =
    is-equiv-Propᵉ
      ( vertical-map-standard-pullbackᵉ
        { fᵉ = subgroup-order-element-Groupᵉ Gᵉ}
        { gᵉ = subgroup-Propᵉ ℤ-Groupᵉ})

  is-equiv-first-projection-pullback-subgroup-prop-Groupᵉ : UUᵉ (lsuc l1ᵉ)
  is-equiv-first-projection-pullback-subgroup-prop-Groupᵉ =
    type-Propᵉ is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Groupᵉ

  is-prop-is-equiv-first-projection-pullback-subgroup-prop-Groupᵉ :
    is-propᵉ is-equiv-first-projection-pullback-subgroup-prop-Groupᵉ
  is-prop-is-equiv-first-projection-pullback-subgroup-prop-Groupᵉ =
    is-prop-type-Propᵉ
      ( is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Groupᵉ)
```

## Properties

### The two definitions of torsion-free groups are equivalent

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-torsion-free-has-unique-torsion-element-Groupᵉ :
    has-unique-torsion-element-Groupᵉ Gᵉ → is-torsion-free-Groupᵉ Gᵉ
  is-torsion-free-has-unique-torsion-element-Groupᵉ Hᵉ xᵉ kᵉ pᵉ =
    apᵉ pr1ᵉ (eq-is-contrᵉ Hᵉ {xᵉ ,ᵉ intro-existsᵉ kᵉ pᵉ} {unit-torsion-element-Groupᵉ Gᵉ})

  abstract
    has-unique-torsion-element-is-torsion-free-Groupᵉ :
      is-torsion-free-Groupᵉ Gᵉ → has-unique-torsion-element-Groupᵉ Gᵉ
    has-unique-torsion-element-is-torsion-free-Groupᵉ Hᵉ =
      fundamental-theorem-id'ᵉ
        ( λ where xᵉ reflᵉ → is-torsion-element-unit-Groupᵉ Gᵉ)
        ( λ xᵉ →
          is-equiv-has-converse-is-propᵉ
            ( is-set-type-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ) xᵉ)
            ( is-prop-is-torsion-element-Groupᵉ Gᵉ xᵉ)
            ( elim-existsᵉ
              ( Id-Propᵉ (set-Groupᵉ Gᵉ) (unit-Groupᵉ Gᵉ) xᵉ)
              ( λ kᵉ pᵉ → invᵉ (Hᵉ xᵉ kᵉ pᵉ))))
```