# Characteristic subgroups

```agda
module group-theory.characteristic-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.images-of-group-homomorphismsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Aᵉ **characteristicᵉ subgroup**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ aᵉ
[subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ `G`ᵉ suchᵉ thatᵉ `fᵉ Hᵉ ⊆ᵉ H`ᵉ forᵉ everyᵉ
[isomorphism](group-theory.isomorphisms-groups.mdᵉ) `fᵉ : Gᵉ ≅ᵉ G`.ᵉ Theᵉ seeminglyᵉ
strongerᵉ condition,ᵉ whichᵉ assertsᵉ thatᵉ `fᵉ Hᵉ ＝ᵉ H`ᵉ forᵉ everyᵉ isomorphismᵉ
`fᵉ : Gᵉ ≅ᵉ G`ᵉ isᵉ equivalent.ᵉ

Noteᵉ thatᵉ anyᵉ characteristicᵉ subgroupᵉ isᵉ
[normal](group-theory.normal-subgroups.md),ᵉ sinceᵉ theᵉ conditionᵉ ofᵉ beingᵉ
characteristicᵉ impliesᵉ thatᵉ `conjugationᵉ xᵉ Hᵉ ＝ᵉ H`.ᵉ

Weᵉ alsoᵉ noteᵉ thatᵉ everyᵉ subgroupᵉ whichᵉ isᵉ definedᵉ forᵉ allᵉ groups,ᵉ suchᵉ asᵉ theᵉ
commutatorᵉ subgroup,ᵉ isᵉ automaticallyᵉ characteristicᵉ asᵉ aᵉ consequenceᵉ ofᵉ theᵉ
[univalenceᵉ axiom](foundation.univalence.md),ᵉ andᵉ thereforeᵉ alsoᵉ normal.ᵉ

## Definition

### The predicate of being a characteristic subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-characteristic-prop-Subgroupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-characteristic-prop-Subgroupᵉ =
    Π-Propᵉ
      ( iso-Groupᵉ Gᵉ Gᵉ)
      ( λ fᵉ →
        leq-prop-Subgroupᵉ Gᵉ
          ( im-hom-Subgroupᵉ Gᵉ Gᵉ (hom-iso-Groupᵉ Gᵉ Gᵉ fᵉ) Hᵉ)
          ( Hᵉ))
```

### The stronger predicate of being a characteristic subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-characteristic-prop-Subgroup'ᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-characteristic-prop-Subgroup'ᵉ =
    Π-Propᵉ
      ( iso-Groupᵉ Gᵉ Gᵉ)
      ( λ fᵉ →
        has-same-elements-prop-Subgroupᵉ Gᵉ
          ( im-hom-Subgroupᵉ Gᵉ Gᵉ (hom-iso-Groupᵉ Gᵉ Gᵉ fᵉ) Hᵉ)
          ( Hᵉ))
```

## See also

-ᵉ [Characteristicᵉ subgroup](https://groupprops.subwiki.org/wiki/Characteristic_subgroupᵉ)
  atᵉ Grouppropsᵉ
-ᵉ [Characteristicᵉ subgroup](https://www.wikidata.org/entity/Q747027ᵉ) atᵉ Wikidataᵉ
-ᵉ [Characteristicᵉ subgroup](https://en.wikipedia.org/wiki/Characteristic_subgroupᵉ)
  atᵉ Wikipediaᵉ