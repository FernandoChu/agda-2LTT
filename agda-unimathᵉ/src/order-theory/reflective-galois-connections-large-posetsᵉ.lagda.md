# Reflective Galois connections between large posets

```agda
module order-theory.reflective-galois-connections-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.galois-connections-large-posetsᵉ
open import order-theory.large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ **reflectiveᵉ galoisᵉ connection**ᵉ betweenᵉ
[largeᵉ posets](order-theory.large-posets.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ aᵉ
[Galoisᵉ connection](order-theory.galois-connections-large-posets.mdᵉ)
`fᵉ : Pᵉ ⇆ᵉ Qᵉ : g`ᵉ suchᵉ thatᵉ `fᵉ ∘ᵉ gᵉ : Qᵉ → P`ᵉ isᵉ theᵉ identityᵉ map.ᵉ

## Definitions

### The predicate of being a reflective Galois connection

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  where

  private
    fᵉ = map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ
    gᵉ = map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ

  is-reflective-galois-connection-Large-Posetᵉ : UUωᵉ
  is-reflective-galois-connection-Large-Posetᵉ =
    {lᵉ : Level} (xᵉ : type-Large-Posetᵉ Qᵉ lᵉ) →
    leq-Large-Posetᵉ Qᵉ (fᵉ (gᵉ xᵉ)) xᵉ ×ᵉ
    leq-Large-Posetᵉ Qᵉ xᵉ (fᵉ (gᵉ xᵉ))
```

### The type of reflective Galois connections

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  where

  record reflective-galois-connection-Large-Posetᵉ : UUωᵉ
    where
    field
      galois-connection-reflective-galois-connection-Large-Posetᵉ :
        galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ
      is-reflective-reflective-galois-connection-Large-Posetᵉ :
        is-reflective-galois-connection-Large-Posetᵉ Pᵉ Qᵉ
          galois-connection-reflective-galois-connection-Large-Posetᵉ

  open reflective-galois-connection-Large-Posetᵉ public

  module _
    (Gᵉ : reflective-galois-connection-Large-Posetᵉ)
    where

    lower-adjoint-reflective-galois-connection-Large-Posetᵉ :
      hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ
    lower-adjoint-reflective-galois-connection-Large-Posetᵉ =
      lower-adjoint-galois-connection-Large-Posetᵉ
        ( galois-connection-reflective-galois-connection-Large-Posetᵉ Gᵉ)
```