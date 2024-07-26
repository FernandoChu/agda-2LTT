# Homomorphisms of suplattices

```agda
module order-theory.homomorphisms-sup-latticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.order-preserving-maps-posetsᵉ
open import order-theory.suplatticesᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ suplattices**ᵉ isᵉ aᵉ orderᵉ preservingᵉ mapᵉ betweenᵉ theᵉ
underlyingᵉ posetsᵉ thatᵉ preservesᵉ leastᵉ upperᵉ bounds.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Aᵉ : Suplatticeᵉ l1ᵉ l2ᵉ l3ᵉ) (Bᵉ : Suplatticeᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  preserves-supsᵉ :
    (type-Suplatticeᵉ Aᵉ → type-Suplatticeᵉ Bᵉ) →
    UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  preserves-supsᵉ fᵉ =
    {Iᵉ : UUᵉ l3ᵉ} → (bᵉ : Iᵉ → type-Suplatticeᵉ Aᵉ) →
    is-least-upper-bound-family-of-elements-Posetᵉ
      ( poset-Suplatticeᵉ Bᵉ)
      ( fᵉ ∘ᵉ bᵉ)
      ( fᵉ (sup-Suplatticeᵉ Aᵉ bᵉ))

  hom-Suplatticeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  hom-Suplatticeᵉ =
    Σᵉ ( type-Suplatticeᵉ Aᵉ → type-Suplatticeᵉ Bᵉ)
      ( λ fᵉ →
        preserves-order-Posetᵉ (poset-Suplatticeᵉ Aᵉ) (poset-Suplatticeᵉ Bᵉ) fᵉ ×ᵉ
        preserves-supsᵉ fᵉ)

  map-hom-Suplatticeᵉ :
    hom-Suplatticeᵉ → type-Suplatticeᵉ Aᵉ → type-Suplatticeᵉ Bᵉ
  map-hom-Suplatticeᵉ = pr1ᵉ

  preserves-order-hom-Suplatticeᵉ :
    (Hᵉ : hom-Suplatticeᵉ) →
    preserves-order-Posetᵉ
      ( poset-Suplatticeᵉ Aᵉ)
      ( poset-Suplatticeᵉ Bᵉ)
      ( map-hom-Suplatticeᵉ Hᵉ)
  preserves-order-hom-Suplatticeᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  preserves-sup-hom-Suplatticeᵉ :
    (Hᵉ : hom-Suplatticeᵉ) → preserves-supsᵉ (map-hom-Suplatticeᵉ Hᵉ)
  preserves-sup-hom-Suplatticeᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```