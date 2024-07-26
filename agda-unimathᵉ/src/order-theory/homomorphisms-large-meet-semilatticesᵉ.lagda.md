# Homomorphisms of large meet-semilattices

```agda
module order-theory.homomorphisms-large-meet-semilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-meet-semilatticesᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Anᵉ homomorphismᵉ ofᵉ
[largeᵉ meet-semilattices](order-theory.large-meet-semilattices.mdᵉ) fromᵉ `K`ᵉ to
`L`ᵉ isᵉ anᵉ
[orderᵉ preservingᵉ map](order-theory.order-preserving-maps-large-posets.mdᵉ) fromᵉ
`K`ᵉ to `L`ᵉ whichᵉ preservesᵉ meetsᵉ andᵉ theᵉ topᵉ element.ᵉ

## Definition

```agda
module _
  {αKᵉ αLᵉ : Level → Level} {βKᵉ βLᵉ : Level → Level → Level}
  (Kᵉ : Large-Meet-Semilatticeᵉ αKᵉ βKᵉ)
  (Lᵉ : Large-Meet-Semilatticeᵉ αLᵉ βLᵉ)
  where

  record
    hom-Large-Meet-Semilatticeᵉ : UUωᵉ
    where
    field
      hom-large-poset-hom-Large-Meet-Semilatticeᵉ :
        hom-Large-Posetᵉ
          ( λ lᵉ → lᵉ)
          ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
          ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      preserves-meets-hom-Large-Meet-Semilatticeᵉ :
        {l1ᵉ l2ᵉ : Level}
        (xᵉ : type-Large-Meet-Semilatticeᵉ Kᵉ l1ᵉ)
        (yᵉ : type-Large-Meet-Semilatticeᵉ Kᵉ l2ᵉ) →
        map-hom-Large-Posetᵉ
          ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
          ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
          ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ)
          ( meet-Large-Meet-Semilatticeᵉ Kᵉ xᵉ yᵉ) ＝ᵉ
        meet-Large-Meet-Semilatticeᵉ Lᵉ
          ( map-hom-Large-Posetᵉ
            ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
            ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
            ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ)
            ( xᵉ))
          ( map-hom-Large-Posetᵉ
            ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
            ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
            ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ)
            ( yᵉ))
      preserves-top-hom-Large-Meet-Semilatticeᵉ :
        map-hom-Large-Posetᵉ
          ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
          ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
          ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ)
          ( top-Large-Meet-Semilatticeᵉ Kᵉ) ＝ᵉ
        top-Large-Meet-Semilatticeᵉ Lᵉ

  open hom-Large-Meet-Semilatticeᵉ public

  module _
    (fᵉ : hom-Large-Meet-Semilatticeᵉ)
    where

    map-hom-Large-Meet-Semilatticeᵉ :
      {l1ᵉ : Level} →
      type-Large-Meet-Semilatticeᵉ Kᵉ l1ᵉ →
      type-Large-Meet-Semilatticeᵉ Lᵉ l1ᵉ
    map-hom-Large-Meet-Semilatticeᵉ =
      map-hom-Large-Posetᵉ
        ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
        ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
        ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ fᵉ)

    preserves-order-hom-Large-Meet-Semilatticeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Meet-Semilatticeᵉ Kᵉ l1ᵉ)
      (yᵉ : type-Large-Meet-Semilatticeᵉ Kᵉ l2ᵉ) →
      leq-Large-Meet-Semilatticeᵉ Kᵉ xᵉ yᵉ →
      leq-Large-Meet-Semilatticeᵉ Lᵉ
        ( map-hom-Large-Meet-Semilatticeᵉ xᵉ)
        ( map-hom-Large-Meet-Semilatticeᵉ yᵉ)
    preserves-order-hom-Large-Meet-Semilatticeᵉ =
      preserves-order-hom-Large-Posetᵉ
        ( large-poset-Large-Meet-Semilatticeᵉ Kᵉ)
        ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
        ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ fᵉ)
```