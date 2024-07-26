# Images of subtypes

```agda
module foundation.images-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.full-subtypesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.imagesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.powersetsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.pullbacks-subtypesᵉ
open import foundation.subtypesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `Sᵉ ⊆ᵉ A`,ᵉ
thenᵉ theᵉ **image**ᵉ ofᵉ `S`ᵉ underᵉ `f`ᵉ isᵉ theᵉ subtypeᵉ ofᵉ `B`ᵉ consistingᵉ ofᵉ theᵉ
valuesᵉ ofᵉ theᵉ compositeᵉ `Sᵉ ⊆ᵉ Aᵉ → B`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ imageᵉ `imᵉ fᵉ S`ᵉ ofᵉ aᵉ
subtypeᵉ `S`ᵉ underᵉ `f`ᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ thatᵉ

```text
  (imᵉ fᵉ Sᵉ ⊆ᵉ Uᵉ) ↔ᵉ (Sᵉ ⊆ᵉ Uᵉ ∘ᵉ f).ᵉ
```

Theᵉ imageᵉ operationᵉ onᵉ subtypesᵉ isᵉ anᵉ
[orderᵉ preservingᵉ map](order-theory.order-preserving-maps-large-posets.mdᵉ) fromᵉ
theᵉ [powerset](foundation.powersets.mdᵉ) ofᵉ `A`ᵉ to theᵉ powersetᵉ ofᵉ `B`.ᵉ Thusᵉ weᵉ
obtainᵉ aᵉ [Galoisᵉ connection](order-theory.galois-connections-large-posets.mdᵉ)
betweenᵉ theᵉ powersetsᵉ ofᵉ `A`ᵉ andᵉ `B`ᵉ: theᵉ **image-pullbackᵉ Galoisᵉ connection**ᵉ

```text
  image-subtypeᵉ fᵉ ⊣ᵉ pullback-subtypeᵉ f.ᵉ
```

## Definitions

### The predicate of being the image of a subtype under a map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Sᵉ : subtypeᵉ l3ᵉ Aᵉ)
  where

  is-image-map-subtypeᵉ : {l4ᵉ : Level} (Tᵉ : subtypeᵉ l4ᵉ Bᵉ) → UUωᵉ
  is-image-map-subtypeᵉ Tᵉ =
    {lᵉ : Level} (Uᵉ : subtypeᵉ lᵉ Bᵉ) → (Tᵉ ⊆ᵉ Uᵉ) ↔ᵉ (Sᵉ ⊆ᵉ Uᵉ ∘ᵉ fᵉ)
```

### The image of a subtype under a map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Sᵉ : subtypeᵉ l3ᵉ Aᵉ)
  where

  im-subtypeᵉ : subtypeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Bᵉ
  im-subtypeᵉ yᵉ = subtype-imᵉ (fᵉ ∘ᵉ inclusion-subtypeᵉ Sᵉ) yᵉ

  is-in-im-subtypeᵉ : Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-in-im-subtypeᵉ = is-in-subtypeᵉ im-subtypeᵉ
```

### The order preserving operation taking the image of a subtype under a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  preserves-order-im-subtypeᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : subtypeᵉ l3ᵉ Aᵉ) (Tᵉ : subtypeᵉ l4ᵉ Aᵉ) →
    Sᵉ ⊆ᵉ Tᵉ → im-subtypeᵉ fᵉ Sᵉ ⊆ᵉ im-subtypeᵉ fᵉ Tᵉ
  preserves-order-im-subtypeᵉ Sᵉ Tᵉ Hᵉ yᵉ pᵉ =
    apply-universal-property-trunc-Propᵉ pᵉ
      ( im-subtypeᵉ fᵉ Tᵉ yᵉ)
      ( λ ((xᵉ ,ᵉ sᵉ) ,ᵉ qᵉ) → unit-trunc-Propᵉ ((xᵉ ,ᵉ Hᵉ xᵉ sᵉ) ,ᵉ qᵉ))

  im-subtype-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( powerset-Large-Posetᵉ Aᵉ)
      ( powerset-Large-Posetᵉ Bᵉ)
  map-hom-Large-Preorderᵉ im-subtype-hom-Large-Posetᵉ =
    im-subtypeᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ im-subtype-hom-Large-Posetᵉ =
    preserves-order-im-subtypeᵉ
```

### The image-pullback Galois connection on powersets

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  forward-implication-adjoint-relation-image-pullback-subtypeᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : subtypeᵉ l3ᵉ Aᵉ) (Tᵉ : subtypeᵉ l4ᵉ Bᵉ) →
    (im-subtypeᵉ fᵉ Sᵉ ⊆ᵉ Tᵉ) → (Sᵉ ⊆ᵉ pullback-subtypeᵉ fᵉ Tᵉ)
  forward-implication-adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ Hᵉ xᵉ pᵉ =
    Hᵉ (fᵉ xᵉ) (unit-trunc-Propᵉ ((xᵉ ,ᵉ pᵉ) ,ᵉ reflᵉ))

  backward-implication-adjoint-relation-image-pullback-subtypeᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : subtypeᵉ l3ᵉ Aᵉ) (Tᵉ : subtypeᵉ l4ᵉ Bᵉ) →
    (Sᵉ ⊆ᵉ pullback-subtypeᵉ fᵉ Tᵉ) → (im-subtypeᵉ fᵉ Sᵉ ⊆ᵉ Tᵉ)
  backward-implication-adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ Hᵉ yᵉ pᵉ =
    apply-universal-property-trunc-Propᵉ pᵉ
      ( Tᵉ yᵉ)
      ( λ where ((xᵉ ,ᵉ sᵉ) ,ᵉ reflᵉ) → Hᵉ xᵉ sᵉ)

  adjoint-relation-image-pullback-subtypeᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : subtypeᵉ l3ᵉ Aᵉ) (Tᵉ : subtypeᵉ l4ᵉ Bᵉ) →
    (im-subtypeᵉ fᵉ Sᵉ ⊆ᵉ Tᵉ) ↔ᵉ (Sᵉ ⊆ᵉ pullback-subtypeᵉ fᵉ Tᵉ)
  pr1ᵉ (adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ) =
    forward-implication-adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ
  pr2ᵉ (adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ) =
    backward-implication-adjoint-relation-image-pullback-subtypeᵉ Sᵉ Tᵉ

  image-pullback-subtype-galois-connection-Large-Posetᵉ :
    galois-connection-Large-Posetᵉ
      ( λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ lᵉ)
      ( λ lᵉ → lᵉ)
      ( powerset-Large-Posetᵉ Aᵉ)
      ( powerset-Large-Posetᵉ Bᵉ)
  lower-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-subtype-galois-connection-Large-Posetᵉ =
    im-subtype-hom-Large-Posetᵉ fᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    image-pullback-subtype-galois-connection-Large-Posetᵉ =
    pullback-subtype-hom-Large-Posetᵉ fᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    image-pullback-subtype-galois-connection-Large-Posetᵉ =
    adjoint-relation-image-pullback-subtypeᵉ
```

## Properties

### If `S` and `T` have the same elements, then `im-subtype f S` and `im-subtype f T` have the same elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Sᵉ : subtypeᵉ l3ᵉ Aᵉ) (Tᵉ : subtypeᵉ l4ᵉ Aᵉ)
  where

  has-same-elements-im-has-same-elements-subtypeᵉ :
    has-same-elements-subtypeᵉ Sᵉ Tᵉ →
    has-same-elements-subtypeᵉ (im-subtypeᵉ fᵉ Sᵉ) (im-subtypeᵉ fᵉ Tᵉ)
  has-same-elements-im-has-same-elements-subtypeᵉ sᵉ =
    has-same-elements-sim-subtypeᵉ
      ( im-subtypeᵉ fᵉ Sᵉ)
      ( im-subtypeᵉ fᵉ Tᵉ)
      ( preserves-sim-hom-Large-Posetᵉ
        ( powerset-Large-Posetᵉ Aᵉ)
        ( powerset-Large-Posetᵉ Bᵉ)
        ( im-subtype-hom-Large-Posetᵉ fᵉ)
        ( Sᵉ)
        ( Tᵉ)
        ( sim-has-same-elements-subtypeᵉ Sᵉ Tᵉ sᵉ))
```

### The image subtype `im f (full-subtype A)` has the same elements as the subtype `im f`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  compute-im-full-subtypeᵉ :
    has-same-elements-subtypeᵉ
      ( im-subtypeᵉ fᵉ (full-subtypeᵉ lzero Aᵉ))
      ( subtype-imᵉ fᵉ)
  compute-im-full-subtypeᵉ yᵉ =
    iff-equivᵉ
      ( equiv-trunc-Propᵉ
        ( ( right-unit-law-Σ-is-contrᵉ
            ( λ aᵉ →
              is-contr-map-is-equivᵉ is-equiv-inclusion-full-subtypeᵉ (pr1ᵉ aᵉ))) ∘eᵉ
          ( compute-fiber-compᵉ fᵉ inclusion-full-subtypeᵉ yᵉ)))
```

### The image subtype `im (g ∘ f) S` has the same elements as the image subtype `im g (im f S)`

**Proof:**ᵉ Theᵉ assertedᵉ similarityᵉ followsᵉ atᵉ onceᵉ fromᵉ theᵉ similarityᵉ

```text
  pullback-subtypeᵉ (gᵉ ∘ᵉ fᵉ) ≈ᵉ pullback-subtypeᵉ gᵉ ∘ᵉ pullback-subtypeᵉ fᵉ
```

viaᵉ theᵉ image-pullbackᵉ Galoisᵉ connection.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) (Sᵉ : subtypeᵉ l4ᵉ Aᵉ)
  where

  compute-im-subtype-compᵉ :
    has-same-elements-subtypeᵉ
      ( im-subtypeᵉ (gᵉ ∘ᵉ fᵉ) Sᵉ)
      ( im-subtypeᵉ gᵉ (im-subtypeᵉ fᵉ Sᵉ))
  compute-im-subtype-compᵉ =
    has-same-elements-sim-subtypeᵉ
      ( im-subtypeᵉ (gᵉ ∘ᵉ fᵉ) Sᵉ)
      ( im-subtypeᵉ gᵉ (im-subtypeᵉ fᵉ Sᵉ))
      ( lower-sim-upper-sim-galois-connection-Large-Posetᵉ
        ( powerset-Large-Posetᵉ Aᵉ)
        ( powerset-Large-Posetᵉ Cᵉ)
        ( image-pullback-subtype-galois-connection-Large-Posetᵉ (gᵉ ∘ᵉ fᵉ))
        ( comp-galois-connection-Large-Posetᵉ
          ( powerset-Large-Posetᵉ Aᵉ)
          ( powerset-Large-Posetᵉ Bᵉ)
          ( powerset-Large-Posetᵉ Cᵉ)
          ( image-pullback-subtype-galois-connection-Large-Posetᵉ gᵉ)
          ( image-pullback-subtype-galois-connection-Large-Posetᵉ fᵉ))
        ( refl-sim-hom-Large-Posetᵉ
          ( powerset-Large-Posetᵉ Cᵉ)
          ( powerset-Large-Posetᵉ Aᵉ)
          ( pullback-subtype-hom-Large-Posetᵉ (gᵉ ∘ᵉ fᵉ)))
        ( Sᵉ))
```

### The image `im (g ∘ f)` has the same elements as the image subtype `im g (im f)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ)
  where

  compute-subtype-im-compᵉ :
    has-same-elements-subtypeᵉ (subtype-imᵉ (gᵉ ∘ᵉ fᵉ)) (im-subtypeᵉ gᵉ (subtype-imᵉ fᵉ))
  compute-subtype-im-compᵉ xᵉ =
    logical-equivalence-reasoningᵉ
      is-in-subtype-imᵉ (gᵉ ∘ᵉ fᵉ) xᵉ
      ↔ᵉ is-in-im-subtypeᵉ (gᵉ ∘ᵉ fᵉ) (full-subtypeᵉ lzero Aᵉ) xᵉ
        byᵉ
        inv-iffᵉ (compute-im-full-subtypeᵉ (gᵉ ∘ᵉ fᵉ) xᵉ)
      ↔ᵉ is-in-im-subtypeᵉ gᵉ (im-subtypeᵉ fᵉ (full-subtypeᵉ lzero Aᵉ)) xᵉ
        byᵉ
        compute-im-subtype-compᵉ gᵉ fᵉ (full-subtypeᵉ lzero Aᵉ) xᵉ
      ↔ᵉ is-in-im-subtypeᵉ gᵉ (subtype-imᵉ fᵉ) xᵉ
        byᵉ
        has-same-elements-im-has-same-elements-subtypeᵉ gᵉ
          ( im-subtypeᵉ fᵉ (full-subtypeᵉ lzero Aᵉ))
          ( subtype-imᵉ fᵉ)
          ( compute-im-full-subtypeᵉ fᵉ)
          ( xᵉ)
```