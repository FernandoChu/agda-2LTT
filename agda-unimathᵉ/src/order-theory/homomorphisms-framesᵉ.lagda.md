# Homomorphisms of frames

```agda
module order-theory.homomorphisms-framesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.framesᵉ
open import order-theory.homomorphisms-meet-semilatticesᵉ
open import order-theory.homomorphisms-meet-sup-latticesᵉ
open import order-theory.homomorphisms-sup-latticesᵉ
open import order-theory.order-preserving-maps-posetsᵉ
```

</details>

## Idea

Aᵉ **frameᵉ homomorphism**ᵉ isᵉ anᵉ orderᵉ preservingᵉ mapᵉ betweenᵉ posetsᵉ thatᵉ
additionallyᵉ preservesᵉ binaryᵉ meetsᵉ andᵉ arbitraryᵉ joins.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Frameᵉ l1ᵉ l2ᵉ) (Bᵉ : Frameᵉ l3ᵉ l4ᵉ)
  where

  hom-Frameᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ l3ᵉ)
  hom-Frameᵉ = Σᵉ (type-Frameᵉ Aᵉ → type-Frameᵉ Bᵉ)
    (λ fᵉ → preserves-order-Posetᵉ (poset-Frameᵉ Aᵉ) (poset-Frameᵉ Bᵉ) fᵉ ×ᵉ
      preserves-meets-supsᵉ
        ( meet-suplattice-Frameᵉ Aᵉ)
        ( meet-suplattice-Frameᵉ Bᵉ)
        ( fᵉ))

  map-hom-Frameᵉ : hom-Frameᵉ → type-Frameᵉ Aᵉ → type-Frameᵉ Bᵉ
  map-hom-Frameᵉ = pr1ᵉ

  preserves-order-hom-Frameᵉ :
    (Hᵉ : hom-Frameᵉ) →
    preserves-order-Posetᵉ (poset-Frameᵉ Aᵉ) (poset-Frameᵉ Bᵉ) (map-hom-Frameᵉ Hᵉ)
  preserves-order-hom-Frameᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  preserves-meets-sups-hom-Frameᵉ :
    (Hᵉ : hom-Frameᵉ) →
    preserves-meets-supsᵉ
      ( meet-suplattice-Frameᵉ Aᵉ)
      ( meet-suplattice-Frameᵉ Bᵉ)
      ( map-hom-Frameᵉ Hᵉ)
  preserves-meets-sups-hom-Frameᵉ = pr2ᵉ ∘ᵉ pr2ᵉ

  preserves-meets-hom-Frameᵉ :
    (Hᵉ : hom-Frameᵉ) →
    preserves-meetᵉ
      ( meet-semilattice-Frameᵉ Aᵉ)
      ( meet-semilattice-Frameᵉ Bᵉ)
      ( map-hom-Frameᵉ Hᵉ)
  preserves-meets-hom-Frameᵉ = pr1ᵉ ∘ᵉ preserves-meets-sups-hom-Frameᵉ

  preserves-sups-hom-Frameᵉ :
    (Hᵉ : hom-Frameᵉ) →
    preserves-supsᵉ
      ( suplattice-Frameᵉ Aᵉ)
      ( suplattice-Frameᵉ Bᵉ)
      ( map-hom-Frameᵉ Hᵉ)
  preserves-sups-hom-Frameᵉ = pr2ᵉ ∘ᵉ preserves-meets-sups-hom-Frameᵉ
```