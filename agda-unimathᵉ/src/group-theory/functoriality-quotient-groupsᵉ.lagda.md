# Functoriality of quotient groups

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module group-theory.functoriality-quotient-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-squares-of-group-homomorphismsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.homomorphisms-groups-equipped-with-normal-subgroupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.nullifying-group-homomorphismsᵉ
open import group-theory.quotient-groupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) `N`ᵉ ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`ᵉ andᵉ aᵉ normalᵉ subgroupᵉ `M`ᵉ ofᵉ aᵉ groupᵉ `H`.ᵉ
Thenᵉ anyᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ
satisfyingᵉ theᵉ propertyᵉ thatᵉ `xᵉ ∈ᵉ Nᵉ ⇒ᵉ fᵉ xᵉ ∈ᵉ M`ᵉ inducesᵉ aᵉ groupᵉ homomorphismᵉ
`gᵉ : G/Nᵉ → H/M`,ᵉ whichᵉ isᵉ theᵉ uniqueᵉ groupᵉ homomorphismᵉ suchᵉ thatᵉ theᵉ squareᵉ

```text
         fᵉ
    Gᵉ ------->ᵉ Hᵉ
    |          |
  qᵉ |          | qᵉ
    ∨ᵉ          ∨ᵉ
   G/Nᵉ ----->ᵉ H/Mᵉ
         gᵉ
```

[commutes](group-theory.commuting-squares-of-group-homomorphisms.md).ᵉ

## Definitions

### The quotient functor on groups

#### The functorial action of the quotient group construction

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ)
  where

  abstract
    unique-hom-quotient-Groupᵉ :
      is-contrᵉ
        ( Σᵉ ( hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) (quotient-Groupᵉ Hᵉ Mᵉ))
            ( coherence-square-hom-Groupᵉ Gᵉ Hᵉ
              ( quotient-Groupᵉ Gᵉ Nᵉ)
              ( quotient-Groupᵉ Hᵉ Mᵉ)
              ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ)
              ( quotient-hom-Groupᵉ Gᵉ Nᵉ)
              ( quotient-hom-Groupᵉ Hᵉ Mᵉ)))
    unique-hom-quotient-Groupᵉ =
      unique-mapping-property-quotient-Groupᵉ Gᵉ Nᵉ
        ( quotient-Groupᵉ Hᵉ Mᵉ)
        ( comp-nullifying-hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ
          ( quotient-Groupᵉ Hᵉ Mᵉ)
          ( Nᵉ)
          ( Mᵉ)
          ( nullifying-quotient-hom-Groupᵉ Hᵉ Mᵉ)
          ( fᵉ))

  abstract
    hom-quotient-Groupᵉ : hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) (quotient-Groupᵉ Hᵉ Mᵉ)
    hom-quotient-Groupᵉ = pr1ᵉ (centerᵉ unique-hom-quotient-Groupᵉ)

    naturality-hom-quotient-Groupᵉ :
      coherence-square-hom-Groupᵉ Gᵉ Hᵉ
        ( quotient-Groupᵉ Gᵉ Nᵉ)
        ( quotient-Groupᵉ Hᵉ Mᵉ)
        ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ)
        ( quotient-hom-Groupᵉ Gᵉ Nᵉ)
        ( quotient-hom-Groupᵉ Hᵉ Mᵉ)
        ( hom-quotient-Groupᵉ)
    naturality-hom-quotient-Groupᵉ =
      pr2ᵉ (centerᵉ unique-hom-quotient-Groupᵉ)

  map-hom-quotient-Groupᵉ : type-quotient-Groupᵉ Gᵉ Nᵉ → type-quotient-Groupᵉ Hᵉ Mᵉ
  map-hom-quotient-Groupᵉ =
    map-hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) (quotient-Groupᵉ Hᵉ Mᵉ) hom-quotient-Groupᵉ
```

#### The functorial action preserves the identity homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  abstract
    preserves-id-hom-quotient-Group'ᵉ :
      (pᵉ : reflects-normal-subgroup-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-hom-Groupᵉ Gᵉ)) →
      hom-quotient-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-reflecting-hom-Group'ᵉ Gᵉ Nᵉ pᵉ) ＝ᵉ
      id-hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ)
    preserves-id-hom-quotient-Group'ᵉ pᵉ =
      apᵉ
        ( pr1ᵉ)
        ( eq-is-contr'ᵉ
          ( unique-mapping-property-quotient-Groupᵉ Gᵉ Nᵉ
            ( quotient-Groupᵉ Gᵉ Nᵉ)
            ( nullifying-quotient-hom-Groupᵉ Gᵉ Nᵉ))
          ( hom-quotient-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-reflecting-hom-Group'ᵉ Gᵉ Nᵉ pᵉ) ,ᵉ
            naturality-hom-quotient-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ
              ( id-reflecting-hom-Group'ᵉ Gᵉ Nᵉ pᵉ))
          ( id-hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ) ,ᵉ
            refl-htpyᵉ))

  abstract
    preserves-id-hom-quotient-Groupᵉ :
      hom-quotient-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-reflecting-hom-Groupᵉ Gᵉ Nᵉ) ＝ᵉ
      id-hom-Groupᵉ (quotient-Groupᵉ Gᵉ Nᵉ)
    preserves-id-hom-quotient-Groupᵉ =
      preserves-id-hom-quotient-Group'ᵉ
        ( reflects-normal-subgroup-id-hom-Groupᵉ Gᵉ Nᵉ)
```

#### The functorial action preserves composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  (Lᵉ : Normal-Subgroupᵉ l4ᵉ Gᵉ)
  (Mᵉ : Normal-Subgroupᵉ l5ᵉ Hᵉ)
  (Nᵉ : Normal-Subgroupᵉ l6ᵉ Kᵉ)
  where

  abstract
    preserves-comp-hom-quotient-Group'ᵉ :
      (gᵉ : reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ)
      (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ)
      (pᵉ :
        reflects-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
          ( hom-comp-reflecting-hom-Groupᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ)) →
      hom-quotient-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
        ( comp-reflecting-hom-Group'ᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ pᵉ) ＝ᵉ
      comp-hom-Groupᵉ
        ( quotient-Groupᵉ Gᵉ Lᵉ)
        ( quotient-Groupᵉ Hᵉ Mᵉ)
        ( quotient-Groupᵉ Kᵉ Nᵉ)
        ( hom-quotient-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
        ( hom-quotient-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
    preserves-comp-hom-quotient-Group'ᵉ gᵉ fᵉ pᵉ =
      apᵉ
        ( pr1ᵉ)
        ( eq-is-contr'ᵉ
          ( unique-mapping-property-quotient-Groupᵉ Gᵉ Lᵉ
            ( quotient-Groupᵉ Kᵉ Nᵉ)
            ( comp-nullifying-hom-reflecting-hom-Groupᵉ Gᵉ Kᵉ
              ( quotient-Groupᵉ Kᵉ Nᵉ)
              ( Lᵉ)
              ( Nᵉ)
              ( nullifying-quotient-hom-Groupᵉ Kᵉ Nᵉ)
              ( comp-reflecting-hom-Group'ᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ pᵉ)))
          ( ( hom-quotient-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
              ( comp-reflecting-hom-Group'ᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ pᵉ)) ,ᵉ
            ( naturality-hom-quotient-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
              ( comp-reflecting-hom-Group'ᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ pᵉ)))
          ( comp-hom-Groupᵉ
            ( quotient-Groupᵉ Gᵉ Lᵉ)
            ( quotient-Groupᵉ Hᵉ Mᵉ)
            ( quotient-Groupᵉ Kᵉ Nᵉ)
            ( hom-quotient-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
            ( hom-quotient-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ) ,ᵉ
            ( pasting-horizontal-coherence-square-mapsᵉ
              ( map-reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
              ( map-reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
              ( map-quotient-hom-Groupᵉ Gᵉ Lᵉ)
              ( map-quotient-hom-Groupᵉ Hᵉ Mᵉ)
              ( map-quotient-hom-Groupᵉ Kᵉ Nᵉ)
              ( map-hom-quotient-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
              ( map-hom-quotient-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
              ( naturality-hom-quotient-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
              ( naturality-hom-quotient-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ))))

  abstract
    preserves-comp-hom-quotient-Groupᵉ :
      (gᵉ : reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ)
      (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ) →
      hom-quotient-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ (comp-reflecting-hom-Groupᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ) ＝ᵉ
      comp-hom-Groupᵉ
        ( quotient-Groupᵉ Gᵉ Lᵉ)
        ( quotient-Groupᵉ Hᵉ Mᵉ)
        ( quotient-Groupᵉ Kᵉ Nᵉ)
        ( hom-quotient-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
        ( hom-quotient-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
    preserves-comp-hom-quotient-Groupᵉ gᵉ fᵉ =
      preserves-comp-hom-quotient-Group'ᵉ gᵉ fᵉ
        ( reflects-normal-subgroup-comp-reflecting-hom-Groupᵉ Gᵉ Hᵉ Kᵉ Lᵉ Mᵉ Nᵉ gᵉ fᵉ)
```

#### The quotient group functor

Thisᵉ functorᵉ remainsᵉ to beᵉ formalized.ᵉ