# Homomorphisms of meet sup lattices

```agda
module order-theory.homomorphisms-meet-sup-latticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.homomorphisms-meet-semilatticesᵉ
open import order-theory.homomorphisms-sup-latticesᵉ
open import order-theory.meet-suplatticesᵉ
open import order-theory.order-preserving-maps-posetsᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ meet-suplattices**ᵉ isᵉ aᵉ homomorphismᵉ ofᵉ meet-semilatticesᵉ
thatᵉ in additionᵉ preservesᵉ leastᵉ upperᵉ bounds.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Meet-Suplatticeᵉ l3ᵉ l4ᵉ)
  where

  preserves-meets-supsᵉ :
    (type-Meet-Suplatticeᵉ Aᵉ → type-Meet-Suplatticeᵉ Bᵉ) →
    UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  preserves-meets-supsᵉ fᵉ =
    preserves-meetᵉ
      ( meet-semilattice-Meet-Suplatticeᵉ Aᵉ)
      ( meet-semilattice-Meet-Suplatticeᵉ Bᵉ)
      ( fᵉ) ×ᵉ
    preserves-supsᵉ
      ( suplattice-Meet-Suplatticeᵉ Aᵉ)
      ( suplattice-Meet-Suplatticeᵉ Bᵉ)
      ( fᵉ)

  hom-Meet-Suplatticeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  hom-Meet-Suplatticeᵉ =
    Σᵉ ( type-Meet-Suplatticeᵉ Aᵉ → type-Meet-Suplatticeᵉ Bᵉ)
      ( λ fᵉ →
        preserves-order-Posetᵉ
          ( poset-Meet-Suplatticeᵉ Aᵉ)
          ( poset-Meet-Suplatticeᵉ Bᵉ)
          ( fᵉ) ×ᵉ
        ( preserves-meets-supsᵉ fᵉ))

  map-hom-Meet-Suplatticeᵉ :
    hom-Meet-Suplatticeᵉ →
    type-Meet-Suplatticeᵉ Aᵉ → type-Meet-Suplatticeᵉ Bᵉ
  map-hom-Meet-Suplatticeᵉ = pr1ᵉ

  preserves-order-Meet-Suplatticeᵉ :
    (Hᵉ : hom-Meet-Suplatticeᵉ) →
    preserves-order-Posetᵉ
      ( poset-Meet-Suplatticeᵉ Aᵉ)
      ( poset-Meet-Suplatticeᵉ Bᵉ)
      ( map-hom-Meet-Suplatticeᵉ Hᵉ)
  preserves-order-Meet-Suplatticeᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  preserves-meets-sups-Meet-Suplatticeᵉ :
    (Hᵉ : hom-Meet-Suplatticeᵉ) →
    preserves-meets-supsᵉ (map-hom-Meet-Suplatticeᵉ Hᵉ)
  preserves-meets-sups-Meet-Suplatticeᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  preserves-meets-Meet-Suplatticeᵉ :
    (Hᵉ : hom-Meet-Suplatticeᵉ) →
    preserves-meetᵉ
      ( meet-semilattice-Meet-Suplatticeᵉ Aᵉ)
      ( meet-semilattice-Meet-Suplatticeᵉ Bᵉ)
      ( map-hom-Meet-Suplatticeᵉ Hᵉ)
  preserves-meets-Meet-Suplatticeᵉ = pr1ᵉ ∘ᵉ preserves-meets-sups-Meet-Suplatticeᵉ

  preserves-sups-Meet-Suplatticeᵉ :
    (Hᵉ : hom-Meet-Suplatticeᵉ) →
    preserves-supsᵉ
      ( suplattice-Meet-Suplatticeᵉ Aᵉ)
      ( suplattice-Meet-Suplatticeᵉ Bᵉ)
      ( map-hom-Meet-Suplatticeᵉ Hᵉ)
  preserves-sups-Meet-Suplatticeᵉ = pr2ᵉ ∘ᵉ preserves-meets-sups-Meet-Suplatticeᵉ
```