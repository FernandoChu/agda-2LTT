# Homomorphisms of groups equipped with normal subgroups

```agda
module group-theory.homomorphisms-groups-equipped-with-normal-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.normal-subgroupsᵉ
open import group-theory.pullbacks-subgroupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ equippedᵉ with aᵉ
[normalᵉ subgroup](group-theory.normal-subgroups.mdᵉ) andᵉ aᵉ groupᵉ `H`ᵉ equippedᵉ
with aᵉ normalᵉ subgroupᵉ `M`.ᵉ Aᵉ **homomorphismᵉ ofᵉ groupsᵉ equippedᵉ with normalᵉ
subgroups**ᵉ fromᵉ `(G,N)`ᵉ to `(H,M)`ᵉ consistsᵉ ofᵉ aᵉ
[groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ whichᵉ
**reflects**ᵉ theᵉ normalᵉ subgroupᵉ `N`ᵉ intoᵉ `M`,ᵉ i.e.,ᵉ suchᵉ thatᵉ theᵉ conditionᵉ
`xᵉ ∈ᵉ Nᵉ ⇒ᵉ fᵉ xᵉ ∈ᵉ M`ᵉ holds.ᵉ

## Definitions

### The property of group homomorphisms of reflecting a normal subgroup

Weᵉ sayᵉ thatᵉ aᵉ groupᵉ homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ **reflects**ᵉ aᵉ normalᵉ subgroupᵉ `N`ᵉ
ofᵉ `G`ᵉ intoᵉ aᵉ normalᵉ subgroupᵉ `M`ᵉ ofᵉ `H`ᵉ ifᵉ theᵉ propertyᵉ

```text
  xᵉ ∈ᵉ Nᵉ ⇒ᵉ fᵉ xᵉ ∈ᵉ Mᵉ
```

holdsᵉ forᵉ everyᵉ `xᵉ : G`,ᵉ i.e.,ᵉ ifᵉ `f`ᵉ mapsᵉ elementsᵉ in `N`ᵉ to elementsᵉ in `M`.ᵉ

## Definitions

### The predicate of reflecting a normal subgroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  where

  reflects-normal-subgroup-hom-Groupᵉ : hom-Groupᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  reflects-normal-subgroup-hom-Groupᵉ fᵉ =
    leq-Normal-Subgroupᵉ Gᵉ Nᵉ (pullback-Normal-Subgroupᵉ Gᵉ Hᵉ fᵉ Mᵉ)

  reflecting-hom-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  reflecting-hom-Groupᵉ = Σᵉ (hom-Groupᵉ Gᵉ Hᵉ) reflects-normal-subgroup-hom-Groupᵉ
```

### Reflecting group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ)
  where

  hom-reflecting-hom-Groupᵉ : hom-Groupᵉ Gᵉ Hᵉ
  hom-reflecting-hom-Groupᵉ = pr1ᵉ fᵉ

  reflects-normal-subgroup-reflecting-hom-Groupᵉ :
    reflects-normal-subgroup-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ hom-reflecting-hom-Groupᵉ
  reflects-normal-subgroup-reflecting-hom-Groupᵉ = pr2ᵉ fᵉ

  map-reflecting-hom-Groupᵉ : type-Groupᵉ Gᵉ → type-Groupᵉ Hᵉ
  map-reflecting-hom-Groupᵉ = map-hom-Groupᵉ Gᵉ Hᵉ hom-reflecting-hom-Groupᵉ
```

### The identity reflecting group homomorphism

Weᵉ defineᵉ twoᵉ variationsᵉ ofᵉ theᵉ identityᵉ reflectingᵉ groupᵉ homomorphism.ᵉ Weᵉ willᵉ
defineᵉ theᵉ standardᵉ identityᵉ reflectingᵉ groupᵉ homomorphism,ᵉ butᵉ weᵉ willᵉ alsoᵉ weᵉ
defineᵉ aᵉ generalizedᵉ versionᵉ whichᵉ takesᵉ asᵉ anᵉ argumentᵉ anᵉ arbitraryᵉ elementᵉ ofᵉ

```text
  reflects-normal-subgroup-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-hom-Groupᵉ G).ᵉ
```

Theᵉ purposeᵉ isᵉ thatᵉ in functorialityᵉ proofs,ᵉ theᵉ proofᵉ thatᵉ theᵉ identityᵉ
homomorphismᵉ isᵉ reflectingᵉ isᵉ notᵉ alwaysᵉ theᵉ standardᵉ one.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Nᵉ : Normal-Subgroupᵉ l2ᵉ Gᵉ)
  where

  reflects-normal-subgroup-id-hom-Groupᵉ :
    reflects-normal-subgroup-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-hom-Groupᵉ Gᵉ)
  reflects-normal-subgroup-id-hom-Groupᵉ =
    refl-leq-subtypeᵉ (subset-Normal-Subgroupᵉ Gᵉ Nᵉ)

  id-reflecting-hom-Group'ᵉ :
    (pᵉ : reflects-normal-subgroup-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ (id-hom-Groupᵉ Gᵉ)) →
    reflecting-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ
  pr1ᵉ (id-reflecting-hom-Group'ᵉ pᵉ) = id-hom-Groupᵉ Gᵉ
  pr2ᵉ (id-reflecting-hom-Group'ᵉ pᵉ) = pᵉ

  id-reflecting-hom-Groupᵉ : reflecting-hom-Groupᵉ Gᵉ Gᵉ Nᵉ Nᵉ
  id-reflecting-hom-Groupᵉ =
    id-reflecting-hom-Group'ᵉ reflects-normal-subgroup-id-hom-Groupᵉ
```

### Composition of reflecting group homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (Kᵉ : Groupᵉ l3ᵉ)
  (Lᵉ : Normal-Subgroupᵉ l4ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l5ᵉ Hᵉ)
  (Nᵉ : Normal-Subgroupᵉ l6ᵉ Kᵉ)
  where

  hom-comp-reflecting-hom-Groupᵉ :
    reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ →
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ →
    hom-Groupᵉ Gᵉ Kᵉ
  hom-comp-reflecting-hom-Groupᵉ gᵉ fᵉ =
    comp-hom-Groupᵉ Gᵉ Hᵉ Kᵉ
      ( hom-reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ)
      ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)

  map-comp-reflecting-hom-Groupᵉ :
    reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ →
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ →
    type-Groupᵉ Gᵉ → type-Groupᵉ Kᵉ
  map-comp-reflecting-hom-Groupᵉ gᵉ fᵉ =
    map-hom-Groupᵉ Gᵉ Kᵉ (hom-comp-reflecting-hom-Groupᵉ gᵉ fᵉ)

  reflects-normal-subgroup-comp-reflecting-hom-Groupᵉ :
    (gᵉ : reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ) →
    (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ) →
    reflects-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
      ( hom-comp-reflecting-hom-Groupᵉ gᵉ fᵉ)
  reflects-normal-subgroup-comp-reflecting-hom-Groupᵉ gᵉ fᵉ =
    transitive-leq-subtypeᵉ
      ( subset-Normal-Subgroupᵉ Gᵉ Lᵉ)
      ( subset-Normal-Subgroupᵉ Hᵉ Mᵉ ∘ᵉ map-reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)
      ( subset-Normal-Subgroupᵉ Kᵉ Nᵉ ∘ᵉ map-comp-reflecting-hom-Groupᵉ gᵉ fᵉ)
      ( ( reflects-normal-subgroup-reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ gᵉ) ∘ᵉ
        ( map-reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ))
      ( reflects-normal-subgroup-reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ fᵉ)

  comp-reflecting-hom-Group'ᵉ :
    (gᵉ : reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ) (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ) →
    (pᵉ :
      reflects-normal-subgroup-hom-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
        ( hom-comp-reflecting-hom-Groupᵉ gᵉ fᵉ)) →
    reflecting-hom-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
  pr1ᵉ (comp-reflecting-hom-Group'ᵉ gᵉ fᵉ pᵉ) = hom-comp-reflecting-hom-Groupᵉ gᵉ fᵉ
  pr2ᵉ (comp-reflecting-hom-Group'ᵉ gᵉ fᵉ pᵉ) = pᵉ

  comp-reflecting-hom-Groupᵉ :
    reflecting-hom-Groupᵉ Hᵉ Kᵉ Mᵉ Nᵉ →
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Lᵉ Mᵉ →
    reflecting-hom-Groupᵉ Gᵉ Kᵉ Lᵉ Nᵉ
  comp-reflecting-hom-Groupᵉ gᵉ fᵉ =
    comp-reflecting-hom-Group'ᵉ gᵉ fᵉ
      ( reflects-normal-subgroup-comp-reflecting-hom-Groupᵉ gᵉ fᵉ)
```

### Homotopies of reflecting homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  where

  htpy-reflecting-hom-Groupᵉ :
    reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ → reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-reflecting-hom-Groupᵉ fᵉ gᵉ =
    htpy-hom-Groupᵉ Gᵉ Hᵉ
      ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ)
      ( hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ gᵉ)

  refl-htpy-reflecting-hom-Groupᵉ :
    (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ) → htpy-reflecting-hom-Groupᵉ fᵉ fᵉ
  refl-htpy-reflecting-hom-Groupᵉ fᵉ =
    refl-htpy-hom-Groupᵉ Gᵉ Hᵉ (hom-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ)
```

## Properties

### Characterization of equality of reflecting homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  (Nᵉ : Normal-Subgroupᵉ l3ᵉ Gᵉ) (Mᵉ : Normal-Subgroupᵉ l4ᵉ Hᵉ)
  (fᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ)
  where

  htpy-eq-reflecting-hom-Groupᵉ :
    (gᵉ : reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ gᵉ
  htpy-eq-reflecting-hom-Groupᵉ gᵉ reflᵉ =
    refl-htpy-reflecting-hom-Groupᵉ Gᵉ Hᵉ Nᵉ Mᵉ fᵉ
```