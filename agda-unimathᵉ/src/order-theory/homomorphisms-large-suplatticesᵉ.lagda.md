# Homomorphisms of large suplattices

```agda
module order-theory.homomorphisms-large-suplatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-suplatticesᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ largeᵉ suplattices**ᵉ isᵉ anᵉ
[orderᵉ preservingᵉ map](order-theory.order-preserving-maps-large-posets.mdᵉ) thatᵉ
preservesᵉ leastᵉ upperᵉ bounds.ᵉ

## Definitions

### The predicate of being a homomorphism of large suplattices

```agda
module _
  {αKᵉ αLᵉ : Level → Level} {βKᵉ βLᵉ : Level → Level → Level}
  {γᵉ : Level}
  (Kᵉ : Large-Suplatticeᵉ αKᵉ βKᵉ γᵉ) (Lᵉ : Large-Suplatticeᵉ αLᵉ βLᵉ γᵉ)
  where

  preserves-sup-hom-Large-Posetᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( large-poset-Large-Suplatticeᵉ Kᵉ)
      ( large-poset-Large-Suplatticeᵉ Lᵉ) →
    UUωᵉ
  preserves-sup-hom-Large-Posetᵉ fᵉ =
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ Kᵉ l2ᵉ) →
    ( map-hom-Large-Posetᵉ
      ( large-poset-Large-Suplatticeᵉ Kᵉ)
      ( large-poset-Large-Suplatticeᵉ Lᵉ)
      ( fᵉ)
      ( sup-Large-Suplatticeᵉ Kᵉ xᵉ)) ＝ᵉ
    sup-Large-Suplatticeᵉ Lᵉ
      ( λ iᵉ →
        map-hom-Large-Posetᵉ
          ( large-poset-Large-Suplatticeᵉ Kᵉ)
          ( large-poset-Large-Suplatticeᵉ Lᵉ)
          ( fᵉ)
          ( xᵉ iᵉ))

  record
    hom-Large-Suplatticeᵉ : UUωᵉ
    where
    field
      hom-large-poset-hom-Large-Suplatticeᵉ :
        hom-Large-Posetᵉ
          ( λ lᵉ → lᵉ)
          ( large-poset-Large-Suplatticeᵉ Kᵉ)
          ( large-poset-Large-Suplatticeᵉ Lᵉ)
      preserves-sup-hom-Large-Suplatticeᵉ :
        preserves-sup-hom-Large-Posetᵉ hom-large-poset-hom-Large-Suplatticeᵉ

  open hom-Large-Suplatticeᵉ public

  module _
    (fᵉ : hom-Large-Suplatticeᵉ)
    where

    map-hom-Large-Suplatticeᵉ :
      {l1ᵉ : Level} →
      type-Large-Suplatticeᵉ Kᵉ l1ᵉ → type-Large-Suplatticeᵉ Lᵉ l1ᵉ
    map-hom-Large-Suplatticeᵉ =
      map-hom-Large-Posetᵉ
        ( large-poset-Large-Suplatticeᵉ Kᵉ)
        ( large-poset-Large-Suplatticeᵉ Lᵉ)
        ( hom-large-poset-hom-Large-Suplatticeᵉ fᵉ)

    preserves-order-map-hom-Large-Suplatticeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Suplatticeᵉ Kᵉ l1ᵉ) (yᵉ : type-Large-Suplatticeᵉ Kᵉ l2ᵉ) →
      leq-Large-Suplatticeᵉ Kᵉ xᵉ yᵉ →
      leq-Large-Suplatticeᵉ Lᵉ
        ( map-hom-Large-Suplatticeᵉ xᵉ)
        ( map-hom-Large-Suplatticeᵉ yᵉ)
    preserves-order-map-hom-Large-Suplatticeᵉ =
      preserves-order-hom-Large-Posetᵉ
        ( large-poset-Large-Suplatticeᵉ Kᵉ)
        ( large-poset-Large-Suplatticeᵉ Lᵉ)
        ( hom-large-poset-hom-Large-Suplatticeᵉ fᵉ)
```