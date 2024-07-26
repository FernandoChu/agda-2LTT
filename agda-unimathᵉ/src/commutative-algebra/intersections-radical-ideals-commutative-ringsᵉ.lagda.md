# Intersections of radical ideals of commutative rings

```agda
module commutative-algebra.intersections-radical-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.full-ideals-commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.intersections-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.products-ideals-commutative-ringsᵉ
open import commutative-algebra.products-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radicals-of-ideals-commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-meet-semilatticesᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ
[radicalᵉ ideals](commutative-algebra.radical-ideals-commutative-rings.mdᵉ)
consistsᵉ ofᵉ theᵉ elementsᵉ containedᵉ in bothᵉ ofᵉ them.ᵉ Givenᵉ twoᵉ radicalᵉ idealsᵉ `I`ᵉ
andᵉ `J`,ᵉ theirᵉ intersectionᵉ canᵉ beᵉ computedᵉ asᵉ

```text
  Iᵉ ∩ᵉ Jᵉ ＝ᵉ √ᵉ IJ,ᵉ
```

where `IJ`ᵉ isᵉ theᵉ
[product](commutative-algebra.products-ideals-commutative-rings.mdᵉ) ofᵉ `I`ᵉ andᵉ
`J`.ᵉ

## Definition

### The universal property of intersections of radical ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  is-intersection-radical-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) → UUωᵉ
  is-intersection-radical-ideal-Commutative-Ringᵉ Kᵉ =
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( Iᵉ)
      ( Jᵉ)
      ( Kᵉ)
```

### The intersection of radical ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  is-radical-intersection-radical-ideal-Commutative-Ringᵉ :
    is-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
  pr1ᵉ (is-radical-intersection-radical-ideal-Commutative-Ringᵉ xᵉ nᵉ (Hᵉ ,ᵉ Kᵉ)) =
    is-radical-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ xᵉ nᵉ Hᵉ
  pr2ᵉ (is-radical-intersection-radical-ideal-Commutative-Ringᵉ xᵉ nᵉ (Hᵉ ,ᵉ Kᵉ)) =
    is-radical-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ xᵉ nᵉ Kᵉ

  intersection-radical-ideal-Commutative-Ringᵉ :
    radical-ideal-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Aᵉ
  pr1ᵉ intersection-radical-ideal-Commutative-Ringᵉ =
    intersection-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
  pr2ᵉ intersection-radical-ideal-Commutative-Ringᵉ =
    is-radical-intersection-radical-ideal-Commutative-Ringᵉ

  ideal-intersection-radical-ideal-Commutative-Ringᵉ :
    ideal-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Aᵉ
  ideal-intersection-radical-ideal-Commutative-Ringᵉ =
    ideal-radical-ideal-Commutative-Ringᵉ Aᵉ
      intersection-radical-ideal-Commutative-Ringᵉ

  is-intersection-intersection-radical-ideal-Commutative-Ringᵉ :
    is-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      intersection-radical-ideal-Commutative-Ringᵉ
  is-intersection-intersection-radical-ideal-Commutative-Ringᵉ Kᵉ =
    is-intersection-intersection-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)
```

### The large meet-semilattice of radical ideals in a commutative ring

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  has-meets-radical-ideal-Commutative-Ringᵉ :
    has-meets-Large-Posetᵉ (radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  meet-has-meets-Large-Posetᵉ
    has-meets-radical-ideal-Commutative-Ringᵉ =
    intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
  is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
    has-meets-radical-ideal-Commutative-Ringᵉ =
    is-intersection-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ

  is-large-meet-semilattice-radical-ideal-Commutative-Ringᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  has-meets-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-radical-ideal-Commutative-Ringᵉ =
    has-meets-radical-ideal-Commutative-Ringᵉ
  has-top-element-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-radical-ideal-Commutative-Ringᵉ =
    has-top-element-radical-ideal-Commutative-Ringᵉ Aᵉ

  radical-ideal-Commutative-Ring-Large-Meet-Semilatticeᵉ :
    Large-Meet-Semilatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-poset-Large-Meet-Semilatticeᵉ
    radical-ideal-Commutative-Ring-Large-Meet-Semilatticeᵉ =
    radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ
  is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
    radical-ideal-Commutative-Ring-Large-Meet-Semilatticeᵉ =
    is-large-meet-semilattice-radical-ideal-Commutative-Ringᵉ
```

## Properties

### The radical ideal of an intersection is the intersection of the radicals of the ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  forward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ))
  forward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ xᵉ (Hᵉ ,ᵉ Kᵉ) =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
        ( xᵉ))
      ( λ (nᵉ ,ᵉ H'ᵉ) →
        apply-universal-property-trunc-Propᵉ Kᵉ
          ( subset-radical-of-ideal-Commutative-Ringᵉ Aᵉ
            ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
            ( xᵉ))
          ( λ (mᵉ ,ᵉ K'ᵉ) →
            intro-existsᵉ
              ( add-ℕᵉ nᵉ mᵉ)
              ( ( is-closed-under-eq-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
                  ( is-closed-under-right-multiplication-ideal-Commutative-Ringᵉ
                    ( Aᵉ)
                    ( Iᵉ)
                    ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
                    ( power-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
                    ( H'ᵉ))
                  ( invᵉ ( distributive-power-add-Commutative-Ringᵉ Aᵉ nᵉ mᵉ))) ,ᵉ
                ( is-closed-under-eq-ideal-Commutative-Ringᵉ Aᵉ Jᵉ
                  ( is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ
                    ( Aᵉ)
                    ( Jᵉ)
                    ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
                    ( power-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
                    ( K'ᵉ))
                  ( invᵉ ( distributive-power-add-Commutative-Ringᵉ Aᵉ nᵉ mᵉ))))))

  backward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ))
      ( intersection-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
  backward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ xᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( subset-intersection-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( xᵉ))
      ( λ (nᵉ ,ᵉ H'ᵉ ,ᵉ K'ᵉ) →
        ( intro-existsᵉ nᵉ H'ᵉ ,ᵉ intro-existsᵉ nᵉ K'ᵉ))

  preserves-intersection-radical-of-ideal-Commutative-Ringᵉ :
    ( intersection-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)) ＝ᵉ
    ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ))
  preserves-intersection-radical-of-ideal-Commutative-Ringᵉ =
    eq-has-same-elements-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( intersection-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ))
      ( λ xᵉ →
        forward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ xᵉ ,ᵉ
        backward-inclusion-intersection-radical-of-ideal-Commutative-Ringᵉ xᵉ)
```

### The intersection of radical ideals is the radical of the ideal generated by their product

Givenᵉ twoᵉ radicalᵉ idealsᵉ `I`ᵉ andᵉ `J`,ᵉ weᵉ claimᵉ thatᵉ

```text
  Iᵉ ∩ᵉ Jᵉ ＝ᵉ √ᵉ IJ,ᵉ
```

where `IJ`ᵉ isᵉ theᵉ
[product](commutative-algebra.products-ideals-commutative-rings.mdᵉ) ofᵉ theᵉ
idealsᵉ `I`ᵉ andᵉ `J`.ᵉ Toᵉ proveᵉ this,ᵉ itᵉ sufficesᵉ to proveᵉ theᵉ inclusionsᵉ

```text
  IJᵉ ⊆ᵉ Iᵉ ∩ᵉ Jᵉ ⊆ᵉ √ᵉ IJ.ᵉ
```

Noteᵉ thatᵉ anyᵉ productᵉ ofᵉ elementsᵉ in `I`ᵉ andᵉ `J`ᵉ isᵉ in theᵉ intersectionᵉ `Iᵉ ∩ᵉ J`.ᵉ
Thisᵉ settlesᵉ theᵉ firstᵉ inclusion.ᵉ Forᵉ theᵉ secondᵉ inclusion,ᵉ noteᵉ thatᵉ ifᵉ
`xᵉ ∈ᵉ Iᵉ ∩ᵉ J`,ᵉ thenᵉ `x²ᵉ ∈ᵉ IJ`ᵉ soᵉ itᵉ followsᵉ thatᵉ `xᵉ ∈ᵉ √ᵉ IJ`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  contains-product-intersection-radical-ideal-Commutative-Ringᵉ :
    contains-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
  pr1ᵉ (contains-product-intersection-radical-ideal-Commutative-Ringᵉ xᵉ yᵉ pᵉ qᵉ) =
    is-closed-under-right-multiplication-radical-ideal-Commutative-Ringᵉ
      Aᵉ Iᵉ xᵉ yᵉ pᵉ
  pr2ᵉ (contains-product-intersection-radical-ideal-Commutative-Ringᵉ xᵉ yᵉ pᵉ qᵉ) =
    is-closed-under-left-multiplication-radical-ideal-Commutative-Ringᵉ
      Aᵉ Jᵉ xᵉ yᵉ qᵉ

  forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
  forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ (Hᵉ ,ᵉ Kᵉ) =
    is-radical-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( xᵉ)
      ( 2ᵉ)
      ( contains-product-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ xᵉ xᵉ Hᵉ Kᵉ)

  backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
  backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( is-product-product-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( ideal-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
        ( contains-product-intersection-radical-ideal-Commutative-Ringᵉ))

  has-same-elements-intersection-radical-ideal-Commutative-Ringᵉ :
    has-same-elements-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
  pr1ᵉ (has-same-elements-intersection-radical-ideal-Commutative-Ringᵉ xᵉ) =
    forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ
  pr2ᵉ (has-same-elements-intersection-radical-ideal-Commutative-Ringᵉ xᵉ) =
    backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ

  is-product-intersection-radical-ideal-Commutative-Ringᵉ :
    is-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
      ( contains-product-intersection-radical-ideal-Commutative-Ringᵉ)
  is-product-intersection-radical-ideal-Commutative-Ringᵉ Kᵉ Hᵉ xᵉ pᵉ =
    is-product-product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ Kᵉ Hᵉ xᵉ
      ( forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ pᵉ)

  is-intersection-product-radical-ideal-Commutative-Ringᵉ :
    is-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ)
  pr1ᵉ (is-intersection-product-radical-ideal-Commutative-Ringᵉ Kᵉ) (Lᵉ ,ᵉ Mᵉ) xᵉ pᵉ =
    forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ
      ( Lᵉ xᵉ pᵉ ,ᵉ Mᵉ xᵉ pᵉ)
  pr1ᵉ (pr2ᵉ (is-intersection-product-radical-ideal-Commutative-Ringᵉ Kᵉ) Hᵉ) xᵉ pᵉ =
    pr1ᵉ
      ( backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ
        ( Hᵉ xᵉ pᵉ))
  pr2ᵉ (pr2ᵉ (is-intersection-product-radical-ideal-Commutative-Ringᵉ Kᵉ) Hᵉ) xᵉ pᵉ =
    pr2ᵉ
      ( backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ xᵉ
        ( Hᵉ xᵉ pᵉ))
```