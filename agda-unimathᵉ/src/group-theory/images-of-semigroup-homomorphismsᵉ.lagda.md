# Images of semigroup homomorphisms

```agda
module group-theory.images-of-semigroup-homomorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.images-subtypesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.pullbacks-subsemigroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsemigroupsᵉ
open import group-theory.subsets-semigroupsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
```

</details>

## Idea

Theᵉ **image**ᵉ ofᵉ aᵉ
[semigroupᵉ homomorphism](group-theory.homomorphisms-semigroups.mdᵉ) `fᵉ : Gᵉ → H`ᵉ
consistsᵉ ofᵉ theᵉ [image](foundation.images.mdᵉ) ofᵉ theᵉ underlyingᵉ mapᵉ ofᵉ `f`.ᵉ Thisᵉ
[subset](group-theory.subsets-semigroups.mdᵉ) isᵉ closedᵉ underᵉ multiplication,ᵉ soᵉ
itᵉ isᵉ aᵉ [subsemigroup](group-theory.subsemigroups.mdᵉ) ofᵉ theᵉ
[semigroup](group-theory.semigroups.mdᵉ) `H`.ᵉ Alternatively,ᵉ itᵉ canᵉ beᵉ describedᵉ
asᵉ theᵉ leastᵉ subsemigroupᵉ ofᵉ `H`ᵉ thatᵉ containsᵉ allᵉ theᵉ valuesᵉ ofᵉ `f`.ᵉ

Moreᵉ generally,ᵉ theᵉ **imageᵉ ofᵉ aᵉ subsemigroup**ᵉ `S`ᵉ underᵉ aᵉ semigroupᵉ
homomorphismᵉ `fᵉ : Gᵉ → H`ᵉ isᵉ theᵉ subsemigroupᵉ consistingᵉ ofᵉ allᵉ theᵉ elementsᵉ in
theᵉ imageᵉ ofᵉ theᵉ underlyingᵉ [subset](foundation-core.subtypes.mdᵉ) ofᵉ `S`ᵉ underᵉ
theᵉ underlyingᵉ mapᵉ ofᵉ `f`.ᵉ Sinceᵉ theᵉ imageᵉ ofᵉ aᵉ subsemigroupᵉ satisfiesᵉ theᵉ
followingᵉ adjointᵉ relationᵉ

```text
  (imᵉ fᵉ Sᵉ ⊆ᵉ Tᵉ) ↔ᵉ (Sᵉ ⊆ᵉ Tᵉ ∘ᵉ fᵉ)
```

itᵉ followsᵉ thatᵉ weᵉ obtainᵉ aᵉ
[Galoisᵉ connection](order-theory.galois-connections.md).ᵉ

## Definitions

### The universal property of the image of a semigroup homomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) (Kᵉ : Subsemigroupᵉ l3ᵉ Hᵉ)
  where

  is-image-hom-Semigroupᵉ : UUωᵉ
  is-image-hom-Semigroupᵉ =
    {lᵉ : Level} (Lᵉ : Subsemigroupᵉ lᵉ Hᵉ) →
    leq-Subsemigroupᵉ Hᵉ Kᵉ Lᵉ ↔ᵉ
    ( (gᵉ : type-Semigroupᵉ Gᵉ) →
      is-in-Subsemigroupᵉ Hᵉ Lᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ gᵉ))
```

### The universal property of the image subsemigroup of a subsemigroup

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) (Sᵉ : Subsemigroupᵉ l3ᵉ Gᵉ) (Tᵉ : Subsemigroupᵉ l4ᵉ Hᵉ)
  where

  is-image-subsemigroup-hom-Semigroupᵉ : UUωᵉ
  is-image-subsemigroup-hom-Semigroupᵉ =
    {lᵉ : Level} (Uᵉ : Subsemigroupᵉ lᵉ Hᵉ) →
    leq-Subsemigroupᵉ Hᵉ Tᵉ Uᵉ ↔ᵉ
    leq-Subsemigroupᵉ Gᵉ Sᵉ (pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Uᵉ)
```

### The image subsemigroup under a semigroup homomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  subset-image-hom-Semigroupᵉ : subset-Semigroupᵉ (l1ᵉ ⊔ l2ᵉ) Hᵉ
  subset-image-hom-Semigroupᵉ = subtype-imᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)

  is-image-subtype-subset-image-hom-Semigroupᵉ :
    is-image-subtypeᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ) subset-image-hom-Semigroupᵉ
  is-image-subtype-subset-image-hom-Semigroupᵉ =
    is-image-subtype-subtype-imᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)

  abstract
    is-closed-under-multiplication-image-hom-Semigroupᵉ :
      is-closed-under-multiplication-subset-Semigroupᵉ Hᵉ
        subset-image-hom-Semigroupᵉ
    is-closed-under-multiplication-image-hom-Semigroupᵉ {xᵉ} {yᵉ} Kᵉ Lᵉ =
      apply-twice-universal-property-trunc-Propᵉ Kᵉ Lᵉ
        ( subset-image-hom-Semigroupᵉ (mul-Semigroupᵉ Hᵉ xᵉ yᵉ))
        ( λ where
          ( gᵉ ,ᵉ reflᵉ) (hᵉ ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( mul-Semigroupᵉ Gᵉ gᵉ hᵉ ,ᵉ preserves-mul-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ))

  image-hom-Semigroupᵉ : Subsemigroupᵉ (l1ᵉ ⊔ l2ᵉ) Hᵉ
  pr1ᵉ image-hom-Semigroupᵉ = subset-image-hom-Semigroupᵉ
  pr2ᵉ image-hom-Semigroupᵉ = is-closed-under-multiplication-image-hom-Semigroupᵉ

  is-image-image-hom-Semigroupᵉ :
    is-image-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ image-hom-Semigroupᵉ
  is-image-image-hom-Semigroupᵉ Kᵉ =
    is-image-subtype-subset-image-hom-Semigroupᵉ (subset-Subsemigroupᵉ Hᵉ Kᵉ)

  contains-values-image-hom-Semigroupᵉ :
    (gᵉ : type-Semigroupᵉ Gᵉ) →
    is-in-Subsemigroupᵉ Hᵉ image-hom-Semigroupᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ gᵉ)
  contains-values-image-hom-Semigroupᵉ =
    forward-implicationᵉ
      ( is-image-image-hom-Semigroupᵉ image-hom-Semigroupᵉ)
      ( refl-leq-Subsemigroupᵉ Hᵉ image-hom-Semigroupᵉ)

  leq-image-hom-Semigroupᵉ :
    {lᵉ : Level} (Kᵉ : Subsemigroupᵉ lᵉ Hᵉ) →
    ( ( gᵉ : type-Semigroupᵉ Gᵉ) →
      is-in-Subsemigroupᵉ Hᵉ Kᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ gᵉ)) →
    leq-Subsemigroupᵉ Hᵉ image-hom-Semigroupᵉ Kᵉ
  leq-image-hom-Semigroupᵉ Kᵉ =
    backward-implicationᵉ (is-image-image-hom-Semigroupᵉ Kᵉ)
```

### The image of a subsemigroup under a semigroup homomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) (Kᵉ : Subsemigroupᵉ l3ᵉ Gᵉ)
  where

  subset-im-hom-Subsemigroupᵉ : subset-Semigroupᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Hᵉ
  subset-im-hom-Subsemigroupᵉ =
    im-subtypeᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ) (subset-Subsemigroupᵉ Gᵉ Kᵉ)

  abstract
    is-closed-under-multiplication-im-hom-Subsemigroupᵉ :
      is-closed-under-multiplication-subset-Semigroupᵉ Hᵉ
        subset-im-hom-Subsemigroupᵉ
    is-closed-under-multiplication-im-hom-Subsemigroupᵉ {xᵉ} {yᵉ} uᵉ vᵉ =
      apply-twice-universal-property-trunc-Propᵉ uᵉ vᵉ
        ( subset-im-hom-Subsemigroupᵉ (mul-Semigroupᵉ Hᵉ xᵉ yᵉ))
        ( λ where
          ((x'ᵉ ,ᵉ kᵉ) ,ᵉ reflᵉ) ((y'ᵉ ,ᵉ lᵉ) ,ᵉ reflᵉ) →
            unit-trunc-Propᵉ
              ( ( mul-Subsemigroupᵉ Gᵉ Kᵉ (x'ᵉ ,ᵉ kᵉ) (y'ᵉ ,ᵉ lᵉ)) ,ᵉ
                ( preserves-mul-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)))

  im-hom-Subsemigroupᵉ : Subsemigroupᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Hᵉ
  pr1ᵉ im-hom-Subsemigroupᵉ =
    subset-im-hom-Subsemigroupᵉ
  pr2ᵉ im-hom-Subsemigroupᵉ =
    is-closed-under-multiplication-im-hom-Subsemigroupᵉ

  forward-implication-is-image-subsemigroup-im-hom-Subsemigroupᵉ :
    {lᵉ : Level} (Uᵉ : Subsemigroupᵉ lᵉ Hᵉ) →
    leq-Subsemigroupᵉ Hᵉ im-hom-Subsemigroupᵉ Uᵉ →
    leq-Subsemigroupᵉ Gᵉ Kᵉ (pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Uᵉ)
  forward-implication-is-image-subsemigroup-im-hom-Subsemigroupᵉ Uᵉ =
    forward-implication-adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)
      ( subset-Subsemigroupᵉ Hᵉ Uᵉ)

  backward-implication-is-image-subsemigroup-im-hom-Subsemigroupᵉ :
    {lᵉ : Level} (Uᵉ : Subsemigroupᵉ lᵉ Hᵉ) →
    leq-Subsemigroupᵉ Gᵉ Kᵉ (pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Uᵉ) →
    leq-Subsemigroupᵉ Hᵉ im-hom-Subsemigroupᵉ Uᵉ
  backward-implication-is-image-subsemigroup-im-hom-Subsemigroupᵉ Uᵉ =
    backward-implication-adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)
      ( subset-Subsemigroupᵉ Hᵉ Uᵉ)

  is-image-subsemigroup-im-hom-Subsemigroupᵉ :
    is-image-subsemigroup-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ Kᵉ im-hom-Subsemigroupᵉ
  is-image-subsemigroup-im-hom-Subsemigroupᵉ Uᵉ =
    adjoint-relation-image-pullback-subtypeᵉ
      ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)
      ( subset-Subsemigroupᵉ Hᵉ Uᵉ)
```

### The image-pullback Galois connection on subsemigroups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  preserves-order-im-hom-Subsemigroupᵉ :
    {l3ᵉ l4ᵉ : Level} (Kᵉ : Subsemigroupᵉ l3ᵉ Gᵉ) (Lᵉ : Subsemigroupᵉ l4ᵉ Gᵉ) →
    leq-Subsemigroupᵉ Gᵉ Kᵉ Lᵉ →
    leq-Subsemigroupᵉ Hᵉ
      ( im-hom-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Kᵉ)
      ( im-hom-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Lᵉ)
  preserves-order-im-hom-Subsemigroupᵉ Kᵉ Lᵉ =
    preserves-order-im-subtypeᵉ
      ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Kᵉ)
      ( subset-Subsemigroupᵉ Gᵉ Lᵉ)

  im-hom-subsemigroup-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( Subsemigroup-Large-Posetᵉ Gᵉ)
      ( Subsemigroup-Large-Posetᵉ Hᵉ)
  map-hom-Large-Preorderᵉ im-hom-subsemigroup-hom-Large-Posetᵉ =
    im-hom-Subsemigroupᵉ Gᵉ Hᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ im-hom-subsemigroup-hom-Large-Posetᵉ =
    preserves-order-im-hom-Subsemigroupᵉ

  image-pullback-galois-connection-Subsemigroupᵉ :
    galois-connection-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( λ lᵉ → lᵉ)
      ( Subsemigroup-Large-Posetᵉ Gᵉ)
      ( Subsemigroup-Large-Posetᵉ Hᵉ)
  lower-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subsemigroupᵉ =
    im-hom-subsemigroup-hom-Large-Posetᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subsemigroupᵉ =
    pullback-hom-large-poset-Subsemigroupᵉ Gᵉ Hᵉ fᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    image-pullback-galois-connection-Subsemigroupᵉ Kᵉ =
    is-image-subsemigroup-im-hom-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Kᵉ
```