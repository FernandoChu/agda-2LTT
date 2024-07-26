# Images of group homomorphisms

```agda
module group-theory.images-of-group-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.images-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.subtypesᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.pullbacks-subgroupsᵉ
open import group-theory.subgroupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Theᵉ **image**ᵉ ofᵉ aᵉ [groupᵉ homomorphism](group-theory.homomorphisms-groups.mdᵉ)
`fᵉ : Gᵉ → H`ᵉ consistsᵉ ofᵉ theᵉ [image](foundation.images.mdᵉ) ofᵉ theᵉ underlyingᵉ mapᵉ
ofᵉ `f`.ᵉ Thisᵉ [subset](group-theory.subsets-groups.mdᵉ) containsᵉ theᵉ unitᵉ elementᵉ
andᵉ isᵉ closedᵉ underᵉ multiplicationᵉ andᵉ inverses.ᵉ Itᵉ isᵉ thereforeᵉ aᵉ
[subgroup](group-theory.subgroups.mdᵉ) ofᵉ theᵉ [group](group-theory.groups.mdᵉ)
`H`.ᵉ Alternatively,ᵉ itᵉ canᵉ beᵉ describedᵉ asᵉ theᵉ leastᵉ subgroupᵉ ofᵉ `H`ᵉ thatᵉ
containsᵉ allᵉ theᵉ valuesᵉ ofᵉ `f`.ᵉ

Moreᵉ generally,ᵉ theᵉ **imageᵉ ofᵉ aᵉ subgroup**ᵉ `S`ᵉ underᵉ aᵉ groupᵉ homomorphismᵉ
`fᵉ : Gᵉ → H`ᵉ isᵉ theᵉ subgroupᵉ consistingᵉ ofᵉ allᵉ theᵉ elementsᵉ in theᵉ imageᵉ ofᵉ theᵉ
underlyingᵉ [subset](foundation-core.subtypes.mdᵉ) ofᵉ `S`ᵉ underᵉ theᵉ underlyingᵉ mapᵉ
ofᵉ `f`.ᵉ Sinceᵉ theᵉ imageᵉ ofᵉ aᵉ subgroupᵉ satisfiesᵉ theᵉ followingᵉ adjointᵉ relationᵉ

```text
  (imᵉ fᵉ Sᵉ ⊆ᵉ Tᵉ) ↔ᵉ (Sᵉ ⊆ᵉ Tᵉ ∘ᵉ fᵉ)
```

itᵉ followsᵉ thatᵉ weᵉ obtainᵉ aᵉ
[Galoisᵉ connection](order-theory.galois-connections.md).ᵉ

## Definitions

### The universal property of the image of a group homomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Kᵉ : Subgroupᵉ l3ᵉ Hᵉ)
  where

  is-image-hom-Groupᵉ : UUωᵉ
  is-image-hom-Groupᵉ =
    {lᵉ : Level} (Lᵉ : Subgroupᵉ lᵉ Hᵉ) →
    leq-Subgroupᵉ Hᵉ Kᵉ Lᵉ ↔ᵉ
    ((gᵉ : type-Groupᵉ Gᵉ) → is-in-Subgroupᵉ Hᵉ Lᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ))
```

### The universal property of the image subgroup of a subgroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Sᵉ : Subgroupᵉ l3ᵉ Gᵉ) (Tᵉ : Subgroupᵉ l4ᵉ Hᵉ)
  where

  is-image-subgroup-hom-Groupᵉ : UUωᵉ
  is-image-subgroup-hom-Groupᵉ =
    {lᵉ : Level} (Uᵉ : Subgroupᵉ lᵉ Hᵉ) →
    leq-Subgroupᵉ Hᵉ Tᵉ Uᵉ ↔ᵉ leq-Subgroupᵉ Gᵉ Sᵉ (pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ Uᵉ)
```

### The image subgroup under a group homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  subset-image-hom-Groupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ) Hᵉ
  subset-image-hom-Groupᵉ = subtype-imᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  is-image-subtype-subset-image-hom-Groupᵉ :
    is-image-subtypeᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ) subset-image-hom-Groupᵉ
  is-image-subtype-subset-image-hom-Groupᵉ =
    is-image-subtype-subtype-imᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  abstract
    contains-unit-image-hom-Groupᵉ :
      contains-unit-subset-Groupᵉ Hᵉ subset-image-hom-Groupᵉ
    contains-unit-image-hom-Groupᵉ =
      unit-trunc-Propᵉ (unit-Groupᵉ Gᵉ ,ᵉ preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  abstract
    is-closed-under-multiplication-image-hom-Groupᵉ :
      is-closed-under-multiplication-subset-Groupᵉ Hᵉ subset-image-hom-Groupᵉ
    is-closed-under-multiplication-image-hom-Groupᵉ {xᵉ} {yᵉ} Kᵉ Lᵉ =
      apply-twice-universal-property-trunc-Propᵉ Kᵉ Lᵉ
        ( subset-image-hom-Groupᵉ (mul-Groupᵉ Hᵉ xᵉ yᵉ))
        ( λ where
          ( gᵉ ,ᵉ reflᵉ) (hᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( mul-Groupᵉ Gᵉ gᵉ hᵉ ,ᵉ preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  abstract
    is-closed-under-inverses-image-hom-Groupᵉ :
      is-closed-under-inverses-subset-Groupᵉ Hᵉ subset-image-hom-Groupᵉ
    is-closed-under-inverses-image-hom-Groupᵉ {xᵉ} Kᵉ =
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( subset-image-hom-Groupᵉ (inv-Groupᵉ Hᵉ xᵉ))
        ( λ where
          ( gᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( inv-Groupᵉ Gᵉ gᵉ ,ᵉ preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ))

  is-subgroup-image-hom-Groupᵉ :
    is-subgroup-subset-Groupᵉ Hᵉ subset-image-hom-Groupᵉ
  pr1ᵉ is-subgroup-image-hom-Groupᵉ =
    contains-unit-image-hom-Groupᵉ
  pr1ᵉ (pr2ᵉ is-subgroup-image-hom-Groupᵉ) =
    is-closed-under-multiplication-image-hom-Groupᵉ
  pr2ᵉ (pr2ᵉ is-subgroup-image-hom-Groupᵉ) =
    is-closed-under-inverses-image-hom-Groupᵉ

  image-hom-Groupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ) Hᵉ
  pr1ᵉ image-hom-Groupᵉ = subset-image-hom-Groupᵉ
  pr2ᵉ image-hom-Groupᵉ = is-subgroup-image-hom-Groupᵉ

  is-image-image-hom-Groupᵉ :
    is-image-hom-Groupᵉ Gᵉ Hᵉ fᵉ image-hom-Groupᵉ
  is-image-image-hom-Groupᵉ Kᵉ =
    is-image-subtype-subset-image-hom-Groupᵉ (subset-Subgroupᵉ Hᵉ Kᵉ)

  contains-values-image-hom-Groupᵉ :
    (gᵉ : type-Groupᵉ Gᵉ) →
    is-in-Subgroupᵉ Hᵉ image-hom-Groupᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ)
  contains-values-image-hom-Groupᵉ =
    forward-implicationᵉ
      ( is-image-image-hom-Groupᵉ image-hom-Groupᵉ)
      ( refl-leq-Subgroupᵉ Hᵉ image-hom-Groupᵉ)

  leq-image-hom-Groupᵉ :
    {lᵉ : Level} (Kᵉ : Subgroupᵉ lᵉ Hᵉ) →
    ((gᵉ : type-Groupᵉ Gᵉ) → is-in-Subgroupᵉ Hᵉ Kᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ)) →
    leq-Subgroupᵉ Hᵉ image-hom-Groupᵉ Kᵉ
  leq-image-hom-Groupᵉ Kᵉ =
    backward-implicationᵉ (is-image-image-hom-Groupᵉ Kᵉ)
```

### The image of a subgroup under a group homomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ)
  where

  subset-im-hom-Subgroupᵉ : subset-Groupᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Hᵉ
  subset-im-hom-Subgroupᵉ =
    im-subtypeᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ) (subset-Subgroupᵉ Gᵉ Kᵉ)

  is-in-im-hom-Subgroupᵉ : type-Groupᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-im-hom-Subgroupᵉ = is-in-subtypeᵉ subset-im-hom-Subgroupᵉ

  contains-unit-im-hom-Subgroupᵉ :
    contains-unit-subset-Groupᵉ Hᵉ subset-im-hom-Subgroupᵉ
  contains-unit-im-hom-Subgroupᵉ =
    unit-trunc-Propᵉ (unit-Subgroupᵉ Gᵉ Kᵉ ,ᵉ preserves-unit-hom-Groupᵉ Gᵉ Hᵉ fᵉ)

  abstract
    is-closed-under-multiplication-im-hom-Subgroupᵉ :
      is-closed-under-multiplication-subset-Groupᵉ Hᵉ subset-im-hom-Subgroupᵉ
    is-closed-under-multiplication-im-hom-Subgroupᵉ {xᵉ} {yᵉ} uᵉ vᵉ =
      apply-twice-universal-property-trunc-Propᵉ uᵉ vᵉ
        ( subset-im-hom-Subgroupᵉ (mul-Groupᵉ Hᵉ xᵉ yᵉ))
        ( λ where
          ((x'ᵉ ,ᵉ kᵉ) ,ᵉ reflᵉ) ((y'ᵉ ,ᵉ lᵉ) ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( ( mul-Subgroupᵉ Gᵉ Kᵉ (x'ᵉ ,ᵉ kᵉ) (y'ᵉ ,ᵉ lᵉ)) ,ᵉ
                ( preserves-mul-hom-Groupᵉ Gᵉ Hᵉ fᵉ)))

  abstract
    is-closed-under-inverses-im-hom-Subgroupᵉ :
      is-closed-under-inverses-subset-Groupᵉ Hᵉ subset-im-hom-Subgroupᵉ
    is-closed-under-inverses-im-hom-Subgroupᵉ {xᵉ} uᵉ =
      apply-universal-property-trunc-Propᵉ uᵉ
        ( subset-im-hom-Subgroupᵉ (inv-Groupᵉ Hᵉ xᵉ))
        ( λ where
          ((x'ᵉ ,ᵉ kᵉ) ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( ( inv-Subgroupᵉ Gᵉ Kᵉ (x'ᵉ ,ᵉ kᵉ)) ,ᵉ
                ( preserves-inv-hom-Groupᵉ Gᵉ Hᵉ fᵉ)))

  im-hom-Subgroupᵉ : Subgroupᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Hᵉ
  pr1ᵉ im-hom-Subgroupᵉ =
    subset-im-hom-Subgroupᵉ
  pr1ᵉ (pr2ᵉ im-hom-Subgroupᵉ) =
    contains-unit-im-hom-Subgroupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ im-hom-Subgroupᵉ)) =
    is-closed-under-multiplication-im-hom-Subgroupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ im-hom-Subgroupᵉ)) =
    is-closed-under-inverses-im-hom-Subgroupᵉ

  forward-implication-is-image-subgroup-im-hom-Subgroupᵉ :
    {lᵉ : Level} (Uᵉ : Subgroupᵉ lᵉ Hᵉ) →
    leq-Subgroupᵉ Hᵉ im-hom-Subgroupᵉ Uᵉ →
    leq-Subgroupᵉ Gᵉ Kᵉ (pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ Uᵉ)
  forward-implication-is-image-subgroup-im-hom-Subgroupᵉ Uᵉ =
    forward-implication-adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)
      ( subset-Subgroupᵉ Hᵉ Uᵉ)

  backward-implication-is-image-subgroup-im-hom-Subgroupᵉ :
    {lᵉ : Level} (Uᵉ : Subgroupᵉ lᵉ Hᵉ) →
    leq-Subgroupᵉ Gᵉ Kᵉ (pullback-Subgroupᵉ Gᵉ Hᵉ fᵉ Uᵉ) →
    leq-Subgroupᵉ Hᵉ im-hom-Subgroupᵉ Uᵉ
  backward-implication-is-image-subgroup-im-hom-Subgroupᵉ Uᵉ =
    backward-implication-adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)
      ( subset-Subgroupᵉ Hᵉ Uᵉ)

  is-image-subgroup-im-hom-Subgroupᵉ :
    is-image-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ Kᵉ im-hom-Subgroupᵉ
  is-image-subgroup-im-hom-Subgroupᵉ Uᵉ =
    adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)
      ( subset-Subgroupᵉ Hᵉ Uᵉ)
```

### The image-pullback Galois connection on subgroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-order-im-hom-Subgroupᵉ :
    {l3ᵉ l4ᵉ : Level} (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) (Lᵉ : Subgroupᵉ l4ᵉ Gᵉ) →
    leq-Subgroupᵉ Gᵉ Kᵉ Lᵉ →
    leq-Subgroupᵉ Hᵉ (im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ) (im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Lᵉ)
  preserves-order-im-hom-Subgroupᵉ Kᵉ Lᵉ =
    preserves-order-im-subtypeᵉ
      ( map-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subgroupᵉ Gᵉ Kᵉ)
      ( subset-Subgroupᵉ Gᵉ Lᵉ)

  im-subgroup-hom-large-poset-hom-Groupᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Subgroup-Large-Posetᵉ Hᵉ)
  map-hom-Large-Preorderᵉ im-subgroup-hom-large-poset-hom-Groupᵉ =
    im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ im-subgroup-hom-large-poset-hom-Groupᵉ =
    preserves-order-im-hom-Subgroupᵉ

  image-pullback-galois-connection-Subgroupᵉ :
    galois-connection-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( λ lᵉ → lᵉ)
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Subgroup-Large-Posetᵉ Hᵉ)
  lower-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subgroupᵉ =
    im-subgroup-hom-large-poset-hom-Groupᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subgroupᵉ =
    pullback-subgroup-hom-large-poset-hom-Groupᵉ Gᵉ Hᵉ fᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subgroupᵉ Kᵉ =
    is-image-subgroup-im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ
```

## Properties

### Any subgroup `U` of `H` has the same elements as `im f K` if and only if `U` satisfies the universal property of the image of `K` under `f`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  (Kᵉ : Subgroupᵉ l3ᵉ Gᵉ) (Uᵉ : Subgroupᵉ l4ᵉ Hᵉ)
  where

  is-image-subgroup-has-same-elements-Subgroupᵉ :
    has-same-elements-Subgroupᵉ Hᵉ (im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ) Uᵉ →
    is-image-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ Kᵉ Uᵉ
  is-image-subgroup-has-same-elements-Subgroupᵉ sᵉ =
    is-lower-element-sim-galois-connection-Large-Posetᵉ
      ( Subgroup-Large-Posetᵉ Gᵉ)
      ( Subgroup-Large-Posetᵉ Hᵉ)
      ( image-pullback-galois-connection-Subgroupᵉ Gᵉ Hᵉ fᵉ)
      ( Kᵉ)
      ( Uᵉ)
      ( similar-has-same-elements-Subgroupᵉ Hᵉ (im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ) Uᵉ sᵉ)

  has-same-elements-is-image-Subgroupᵉ :
    is-image-subgroup-hom-Groupᵉ Gᵉ Hᵉ fᵉ Kᵉ Uᵉ →
    has-same-elements-Subgroupᵉ Hᵉ (im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ) Uᵉ
  has-same-elements-is-image-Subgroupᵉ iᵉ =
    has-same-elements-similar-Subgroupᵉ Hᵉ
      ( im-hom-Subgroupᵉ Gᵉ Hᵉ fᵉ Kᵉ)
      ( Uᵉ)
      ( sim-is-lower-element-galois-connection-Large-Posetᵉ
        ( Subgroup-Large-Posetᵉ Gᵉ)
        ( Subgroup-Large-Posetᵉ Hᵉ)
        ( image-pullback-galois-connection-Subgroupᵉ Gᵉ Hᵉ fᵉ)
        ( Kᵉ)
        ( Uᵉ)
        ( iᵉ))
```