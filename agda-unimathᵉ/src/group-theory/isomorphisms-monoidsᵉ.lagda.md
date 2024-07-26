# Isomorphisms of monoids

```agda
module group-theory.isomorphisms-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.invertible-elements-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.precategory-of-monoidsᵉ
```

</details>

## Idea

Anᵉ **isomorphism**ᵉ ofᵉ [monoids](group-theory.monoids.mdᵉ) isᵉ anᵉ invertibleᵉ
[homomorphismᵉ ofᵉ monoids](group-theory.homomorphisms-monoids.md).ᵉ

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  is-iso-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-Monoidᵉ =
    is-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ} fᵉ

  hom-inv-is-iso-Monoidᵉ :
    is-iso-Monoidᵉ → hom-Monoidᵉ Nᵉ Mᵉ
  hom-inv-is-iso-Monoidᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      ( fᵉ)

  is-section-hom-inv-is-iso-Monoidᵉ :
    (Hᵉ : is-iso-Monoidᵉ) →
    comp-hom-Monoidᵉ Nᵉ Mᵉ Nᵉ fᵉ (hom-inv-is-iso-Monoidᵉ Hᵉ) ＝ᵉ
    id-hom-Monoidᵉ Nᵉ
  is-section-hom-inv-is-iso-Monoidᵉ =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      ( fᵉ)

  is-retraction-hom-inv-is-iso-Monoidᵉ :
    (Hᵉ : is-iso-Monoidᵉ) →
    comp-hom-Monoidᵉ Mᵉ Nᵉ Mᵉ (hom-inv-is-iso-Monoidᵉ Hᵉ) fᵉ ＝ᵉ
    id-hom-Monoidᵉ Mᵉ
  is-retraction-hom-inv-is-iso-Monoidᵉ =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      ( fᵉ)
```

### Isomorphisms of monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  iso-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-Monoidᵉ =
    iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ Mᵉ Nᵉ

  hom-iso-Monoidᵉ :
    iso-Monoidᵉ → hom-Monoidᵉ Mᵉ Nᵉ
  hom-iso-Monoidᵉ =
    hom-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}

  map-iso-Monoidᵉ :
    iso-Monoidᵉ → type-Monoidᵉ Mᵉ → type-Monoidᵉ Nᵉ
  map-iso-Monoidᵉ fᵉ = map-hom-Monoidᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ fᵉ)

  preserves-mul-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    map-iso-Monoidᵉ fᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Nᵉ (map-iso-Monoidᵉ fᵉ xᵉ) (map-iso-Monoidᵉ fᵉ yᵉ)
  preserves-mul-iso-Monoidᵉ fᵉ =
    preserves-mul-hom-Monoidᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ fᵉ)

  is-iso-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) →
    is-iso-Monoidᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ fᵉ)
  is-iso-iso-Monoidᵉ =
    is-iso-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}

  hom-inv-iso-Monoidᵉ :
    iso-Monoidᵉ → hom-Monoidᵉ Nᵉ Mᵉ
  hom-inv-iso-Monoidᵉ =
    hom-inv-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}

  map-inv-iso-Monoidᵉ :
    iso-Monoidᵉ → type-Monoidᵉ Nᵉ → type-Monoidᵉ Mᵉ
  map-inv-iso-Monoidᵉ fᵉ =
    map-hom-Monoidᵉ Nᵉ Mᵉ (hom-inv-iso-Monoidᵉ fᵉ)

  preserves-mul-inv-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) {xᵉ yᵉ : type-Monoidᵉ Nᵉ} →
    map-inv-iso-Monoidᵉ fᵉ (mul-Monoidᵉ Nᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Mᵉ (map-inv-iso-Monoidᵉ fᵉ xᵉ) (map-inv-iso-Monoidᵉ fᵉ yᵉ)
  preserves-mul-inv-iso-Monoidᵉ fᵉ =
    preserves-mul-hom-Monoidᵉ Nᵉ Mᵉ (hom-inv-iso-Monoidᵉ fᵉ)

  is-section-hom-inv-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) →
    comp-hom-Monoidᵉ Nᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ fᵉ) (hom-inv-iso-Monoidᵉ fᵉ) ＝ᵉ
    id-hom-Monoidᵉ Nᵉ
  is-section-hom-inv-iso-Monoidᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}

  is-section-map-inv-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) →
    map-iso-Monoidᵉ fᵉ ∘ᵉ map-inv-iso-Monoidᵉ fᵉ ~ᵉ idᵉ
  is-section-map-inv-iso-Monoidᵉ fᵉ =
    htpy-eq-hom-Monoidᵉ Nᵉ Nᵉ
      ( comp-hom-Monoidᵉ Nᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ fᵉ) (hom-inv-iso-Monoidᵉ fᵉ))
      ( id-hom-Monoidᵉ Nᵉ)
      ( is-section-hom-inv-iso-Monoidᵉ fᵉ)

  is-retraction-hom-inv-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) →
    comp-hom-Monoidᵉ Mᵉ Nᵉ Mᵉ (hom-inv-iso-Monoidᵉ fᵉ) (hom-iso-Monoidᵉ fᵉ) ＝ᵉ
    id-hom-Monoidᵉ Mᵉ
  is-retraction-hom-inv-iso-Monoidᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}

  is-retraction-map-inv-iso-Monoidᵉ :
    (fᵉ : iso-Monoidᵉ) →
    map-inv-iso-Monoidᵉ fᵉ ∘ᵉ map-iso-Monoidᵉ fᵉ ~ᵉ idᵉ
  is-retraction-map-inv-iso-Monoidᵉ fᵉ =
    htpy-eq-hom-Monoidᵉ Mᵉ Mᵉ
      ( comp-hom-Monoidᵉ Mᵉ Nᵉ Mᵉ (hom-inv-iso-Monoidᵉ fᵉ) (hom-iso-Monoidᵉ fᵉ))
      ( id-hom-Monoidᵉ Mᵉ)
      ( is-retraction-hom-inv-iso-Monoidᵉ fᵉ)
```

## Examples

### Identity homomorphisms are isomorphisms

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-iso-id-hom-Monoidᵉ :
    is-iso-Monoidᵉ Mᵉ Mᵉ (id-hom-Monoidᵉ Mᵉ)
  is-iso-id-hom-Monoidᵉ =
    is-iso-id-hom-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}

  id-iso-Monoidᵉ : iso-Monoidᵉ Mᵉ Mᵉ
  id-iso-Monoidᵉ =
    id-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
```

### Equalities induce isomorphisms

Anᵉ equalityᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ givesᵉ riseᵉ to anᵉ isomorphismᵉ betweenᵉ them.ᵉ
Thisᵉ isᵉ becauseᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ anᵉ isomorphismᵉ givenᵉ
`reflᵉ : Idᵉ xᵉ x`,ᵉ fromᵉ `x`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ morphismᵉ asᵉ suchᵉ anᵉ
isomorphism.ᵉ

```agda
iso-eq-Monoidᵉ :
  {l1ᵉ : Level} (Mᵉ Nᵉ : Monoidᵉ l1ᵉ) → Mᵉ ＝ᵉ Nᵉ → iso-Monoidᵉ Mᵉ Nᵉ
iso-eq-Monoidᵉ = iso-eq-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ
```

## Properties

### Being an isomorphism is a proposition

Letᵉ `fᵉ : homᵉ xᵉ y`ᵉ andᵉ supposeᵉ `gᵉ g'ᵉ : homᵉ yᵉ x`ᵉ areᵉ bothᵉ two-sidedᵉ inversesᵉ to
`f`.ᵉ Itᵉ isᵉ enoughᵉ to showᵉ thatᵉ `gᵉ = g'`ᵉ sinceᵉ theᵉ equalitiesᵉ areᵉ propositionsᵉ
(sinceᵉ theᵉ hom-typesᵉ areᵉ sets).ᵉ Butᵉ weᵉ haveᵉ theᵉ followingᵉ chainᵉ ofᵉ equalitiesᵉ:
`gᵉ = gᵉ ∘ᵉ id_yᵉ = gᵉ ∘ᵉ (fᵉ ∘ᵉ g'ᵉ) = (gᵉ ∘ᵉ fᵉ) ∘ᵉ g'ᵉ = id_xᵉ ∘ᵉ g'ᵉ = g'`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  is-prop-is-iso-Monoidᵉ :
    (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) →
    is-propᵉ (is-iso-Monoidᵉ Mᵉ Nᵉ fᵉ)
  is-prop-is-iso-Monoidᵉ =
    is-prop-is-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
  is-iso-prop-Monoidᵉ :
    (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-iso-prop-Monoidᵉ =
    is-iso-prop-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}
```

### The type of isomorphisms form a set

Theᵉ typeᵉ ofᵉ isomorphismsᵉ betweenᵉ objectsᵉ `xᵉ yᵉ : A`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ theᵉ setᵉ
`homᵉ xᵉ y`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  is-set-iso-Monoidᵉ : is-setᵉ (iso-Monoidᵉ Mᵉ Nᵉ)
  is-set-iso-Monoidᵉ =
    is-set-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}

  iso-set-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  iso-set-Monoidᵉ =
    iso-set-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ}
```

### Isomorphisms are stable by composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (Kᵉ : Monoidᵉ l3ᵉ)
  (gᵉ : iso-Monoidᵉ Nᵉ Kᵉ) (fᵉ : iso-Monoidᵉ Mᵉ Nᵉ)
  where

  hom-comp-iso-Monoidᵉ : hom-Monoidᵉ Mᵉ Kᵉ
  hom-comp-iso-Monoidᵉ =
    hom-comp-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      { Zᵉ = Kᵉ}
      ( gᵉ)
      ( fᵉ)

  is-iso-comp-iso-Monoidᵉ :
    is-iso-Monoidᵉ Mᵉ Kᵉ hom-comp-iso-Monoidᵉ
  is-iso-comp-iso-Monoidᵉ =
    is-iso-comp-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      { Zᵉ = Kᵉ}
      ( gᵉ)
      ( fᵉ)

  comp-iso-Monoidᵉ : iso-Monoidᵉ Mᵉ Kᵉ
  comp-iso-Monoidᵉ =
    comp-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      { Zᵉ = Kᵉ}
      ( gᵉ)
      ( fᵉ)
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : iso-Monoidᵉ Mᵉ Nᵉ)
  where

  is-iso-inv-iso-Monoidᵉ :
    is-iso-Monoidᵉ Nᵉ Mᵉ (hom-inv-iso-Monoidᵉ Mᵉ Nᵉ fᵉ)
  is-iso-inv-iso-Monoidᵉ =
    is-iso-inv-is-iso-Large-Precategoryᵉ
      ( Monoid-Large-Precategoryᵉ)
      { Xᵉ = Mᵉ}
      { Yᵉ = Nᵉ}
      ( is-iso-iso-Monoidᵉ Mᵉ Nᵉ fᵉ)

  inv-iso-Monoidᵉ : iso-Monoidᵉ Nᵉ Mᵉ
  inv-iso-Monoidᵉ =
    inv-iso-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ {Xᵉ = Mᵉ} {Yᵉ = Nᵉ} fᵉ
```

### Any isomorphism of monoids preserves and reflects invertible elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  (fᵉ : iso-Monoidᵉ Mᵉ Nᵉ)
  where

  preserves-invertible-elements-iso-Monoidᵉ :
    {xᵉ : type-Monoidᵉ Mᵉ} →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ →
    is-invertible-element-Monoidᵉ Nᵉ (map-iso-Monoidᵉ Mᵉ Nᵉ fᵉ xᵉ)
  preserves-invertible-elements-iso-Monoidᵉ =
    preserves-invertible-elements-hom-Monoidᵉ Mᵉ Nᵉ (hom-iso-Monoidᵉ Mᵉ Nᵉ fᵉ)

  reflects-invertible-elements-iso-Monoidᵉ :
    {xᵉ : type-Monoidᵉ Mᵉ} →
    is-invertible-element-Monoidᵉ Nᵉ (map-iso-Monoidᵉ Mᵉ Nᵉ fᵉ xᵉ) →
    is-invertible-element-Monoidᵉ Mᵉ xᵉ
  reflects-invertible-elements-iso-Monoidᵉ Hᵉ =
    trᵉ
      ( is-invertible-element-Monoidᵉ Mᵉ)
      ( is-retraction-map-inv-iso-Monoidᵉ Mᵉ Nᵉ fᵉ _)
      ( preserves-invertible-elements-hom-Monoidᵉ Nᵉ Mᵉ
        ( hom-inv-iso-Monoidᵉ Mᵉ Nᵉ fᵉ)
        ( Hᵉ))
```