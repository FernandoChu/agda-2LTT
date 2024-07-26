# Homomorphisms of large frames

```agda
module order-theory.homomorphisms-large-framesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.homomorphisms-large-meet-semilatticesᵉ
open import order-theory.homomorphisms-large-suplatticesᵉ
open import order-theory.large-framesᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ largeᵉ frames**ᵉ fromᵉ `K`ᵉ to `L`ᵉ isᵉ anᵉ orderᵉ preservingᵉ mapᵉ
fromᵉ `K`ᵉ to `L`ᵉ whichᵉ preservesᵉ meets,ᵉ theᵉ topᵉ element,ᵉ andᵉ suprema.ᵉ

## Definitions

### Homomorphisms of frames

```agda
module _
  {αKᵉ αLᵉ : Level → Level} {βKᵉ βLᵉ : Level → Level → Level} {γᵉ : Level}
  (Kᵉ : Large-Frameᵉ αKᵉ βKᵉ γᵉ) (Lᵉ : Large-Frameᵉ αLᵉ βLᵉ γᵉ)
  where

  record
    hom-Large-Frameᵉ : UUωᵉ
    where
    field
      hom-large-meet-semilattice-hom-Large-Frameᵉ :
        hom-Large-Meet-Semilatticeᵉ
          ( large-meet-semilattice-Large-Frameᵉ Kᵉ)
          ( large-meet-semilattice-Large-Frameᵉ Lᵉ)
      preserves-sup-hom-Large-Frameᵉ :
        preserves-sup-hom-Large-Posetᵉ
          ( large-suplattice-Large-Frameᵉ Kᵉ)
          ( large-suplattice-Large-Frameᵉ Lᵉ)
          ( hom-large-poset-hom-Large-Meet-Semilatticeᵉ
            ( hom-large-meet-semilattice-hom-Large-Frameᵉ))

  open hom-Large-Frameᵉ public

  module _
    (fᵉ : hom-Large-Frameᵉ)
    where

    map-hom-Large-Frameᵉ :
      {l1ᵉ : Level} → type-Large-Frameᵉ Kᵉ l1ᵉ → type-Large-Frameᵉ Lᵉ l1ᵉ
    map-hom-Large-Frameᵉ =
      map-hom-Large-Meet-Semilatticeᵉ
        ( large-meet-semilattice-Large-Frameᵉ Kᵉ)
        ( large-meet-semilattice-Large-Frameᵉ Lᵉ)
        ( hom-large-meet-semilattice-hom-Large-Frameᵉ fᵉ)

    preserves-order-hom-Large-Frameᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Frameᵉ Kᵉ l1ᵉ) (yᵉ : type-Large-Frameᵉ Kᵉ l2ᵉ) →
      leq-Large-Frameᵉ Kᵉ xᵉ yᵉ →
      leq-Large-Frameᵉ Lᵉ (map-hom-Large-Frameᵉ xᵉ) (map-hom-Large-Frameᵉ yᵉ)
    preserves-order-hom-Large-Frameᵉ =
      preserves-order-hom-Large-Meet-Semilatticeᵉ
        ( large-meet-semilattice-Large-Frameᵉ Kᵉ)
        ( large-meet-semilattice-Large-Frameᵉ Lᵉ)
        ( hom-large-meet-semilattice-hom-Large-Frameᵉ fᵉ)

    preserves-meets-hom-Large-Frameᵉ :
      {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Frameᵉ Kᵉ l1ᵉ) (yᵉ : type-Large-Frameᵉ Kᵉ l2ᵉ) →
      map-hom-Large-Frameᵉ (meet-Large-Frameᵉ Kᵉ xᵉ yᵉ) ＝ᵉ
      meet-Large-Frameᵉ Lᵉ (map-hom-Large-Frameᵉ xᵉ) (map-hom-Large-Frameᵉ yᵉ)
    preserves-meets-hom-Large-Frameᵉ =
      preserves-meets-hom-Large-Meet-Semilatticeᵉ
        ( hom-large-meet-semilattice-hom-Large-Frameᵉ fᵉ)

    preserves-top-hom-Large-Frameᵉ :
      map-hom-Large-Frameᵉ (top-Large-Frameᵉ Kᵉ) ＝ᵉ top-Large-Frameᵉ Lᵉ
    preserves-top-hom-Large-Frameᵉ =
      preserves-top-hom-Large-Meet-Semilatticeᵉ
        ( hom-large-meet-semilattice-hom-Large-Frameᵉ fᵉ)
```