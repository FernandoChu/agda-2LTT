# Pullbacks of subsemigroups

```agda
module group-theory.pullbacks-subsemigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.powersetsᵉ
open import foundation.pullbacks-subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.subsemigroupsᵉ
open import group-theory.subsets-semigroupsᵉ

open import order-theory.commuting-squares-of-order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [semigroupᵉ homomorphism](group-theory.homomorphisms-semigroups.mdᵉ)
`fᵉ : Gᵉ → H`ᵉ intoᵉ aᵉ [semigroup](group-theory.semigroups.mdᵉ) `H`ᵉ equippedᵉ with aᵉ
[subsemigroup](group-theory.subsemigroups.mdᵉ) `Kᵉ ≤ᵉ H`,ᵉ theᵉ **pullback**ᵉ
`pullbackᵉ fᵉ K`ᵉ ofᵉ `K`ᵉ alongᵉ `f`ᵉ isᵉ definedᵉ byᵉ substitutingᵉ `f`ᵉ in `K`.ᵉ Inᵉ otherᵉ
words,ᵉ itᵉ isᵉ theᵉ subsemigroupᵉ `pullbackᵉ fᵉ K`ᵉ ofᵉ `G`ᵉ consistingᵉ ofᵉ theᵉ elementsᵉ
`xᵉ : G`ᵉ suchᵉ thatᵉ `fᵉ xᵉ ∈ᵉ K`.ᵉ

## Definitions

### The pullback of a subsemigroup along a semigroup homomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ)
  (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ) (Kᵉ : Subsemigroupᵉ l3ᵉ Hᵉ)
  where

  subset-pullback-Subsemigroupᵉ : subset-Semigroupᵉ l3ᵉ Gᵉ
  subset-pullback-Subsemigroupᵉ =
    subset-Subsemigroupᵉ Hᵉ Kᵉ ∘ᵉ map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ

  is-closed-under-multiplication-pullback-Subsemigroupᵉ :
    is-closed-under-multiplication-subset-Semigroupᵉ Gᵉ
      subset-pullback-Subsemigroupᵉ
  is-closed-under-multiplication-pullback-Subsemigroupᵉ pᵉ qᵉ =
    is-closed-under-eq-Subsemigroup'ᵉ Hᵉ Kᵉ
      ( is-closed-under-multiplication-Subsemigroupᵉ Hᵉ Kᵉ pᵉ qᵉ)
      ( preserves-mul-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)

  pullback-Subsemigroupᵉ : Subsemigroupᵉ l3ᵉ Gᵉ
  pr1ᵉ pullback-Subsemigroupᵉ =
    subset-pullback-Subsemigroupᵉ
  pr2ᵉ pullback-Subsemigroupᵉ =
    is-closed-under-multiplication-pullback-Subsemigroupᵉ

  is-in-pullback-Subsemigroupᵉ : type-Semigroupᵉ Gᵉ → UUᵉ l3ᵉ
  is-in-pullback-Subsemigroupᵉ =
    is-in-Subsemigroupᵉ Gᵉ pullback-Subsemigroupᵉ

  is-closed-under-eq-pullback-Subsemigroupᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-pullback-Subsemigroupᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-pullback-Subsemigroupᵉ yᵉ
  is-closed-under-eq-pullback-Subsemigroupᵉ =
    is-closed-under-eq-Subsemigroupᵉ Gᵉ pullback-Subsemigroupᵉ

  is-closed-under-eq-pullback-Subsemigroup'ᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-pullback-Subsemigroupᵉ yᵉ → xᵉ ＝ᵉ yᵉ → is-in-pullback-Subsemigroupᵉ xᵉ
  is-closed-under-eq-pullback-Subsemigroup'ᵉ =
    is-closed-under-eq-Subsemigroup'ᵉ Gᵉ pullback-Subsemigroupᵉ
```

### The order preserving operation `pullback-Subsemigroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  preserves-order-pullback-Subsemigroupᵉ :
    {l3ᵉ l4ᵉ : Level} (Sᵉ : Subsemigroupᵉ l3ᵉ Hᵉ) (Tᵉ : Subsemigroupᵉ l4ᵉ Hᵉ) →
    leq-Subsemigroupᵉ Hᵉ Sᵉ Tᵉ →
    leq-Subsemigroupᵉ Gᵉ
      ( pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Sᵉ)
      ( pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ Tᵉ)
  preserves-order-pullback-Subsemigroupᵉ Sᵉ Tᵉ =
    preserves-order-pullback-subtypeᵉ
      ( map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-Subsemigroupᵉ Hᵉ Sᵉ)
      ( subset-Subsemigroupᵉ Hᵉ Tᵉ)

  pullback-hom-large-poset-Subsemigroupᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( Subsemigroup-Large-Posetᵉ Hᵉ)
      ( Subsemigroup-Large-Posetᵉ Gᵉ)
  map-hom-Large-Preorderᵉ pullback-hom-large-poset-Subsemigroupᵉ =
    pullback-Subsemigroupᵉ Gᵉ Hᵉ fᵉ
  preserves-order-hom-Large-Preorderᵉ pullback-hom-large-poset-Subsemigroupᵉ =
    preserves-order-pullback-Subsemigroupᵉ
```

## Properties

### The pullback operation commutes with the underlying subtype operation

Theᵉ squareᵉ

```text
                       pullbackᵉ fᵉ
    Subsemigroupᵉ Hᵉ ---------------->ᵉ Subsemigroupᵉ Gᵉ
          |                                |
   Kᵉ ↦ᵉ UKᵉ |                                | Kᵉ ↦ᵉ UKᵉ
          |                                |
          ∨ᵉ                                ∨ᵉ
  subset-Semigroupᵉ Hᵉ ------------>ᵉ subset-Semigroupᵉ Gᵉ
                      pullbackᵉ fᵉ
```

ofᵉ [orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
[commutes](order-theory.commuting-squares-of-order-preserving-maps-large-posets.mdᵉ)
byᵉ reflexivity.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Hᵉ : Semigroupᵉ l2ᵉ) (fᵉ : hom-Semigroupᵉ Gᵉ Hᵉ)
  where

  coherence-square-pullback-subset-Subsemigroupᵉ :
    coherence-square-hom-Large-Posetᵉ
      ( Subsemigroup-Large-Posetᵉ Hᵉ)
      ( powerset-Large-Posetᵉ (type-Semigroupᵉ Hᵉ))
      ( Subsemigroup-Large-Posetᵉ Gᵉ)
      ( powerset-Large-Posetᵉ (type-Semigroupᵉ Gᵉ))
      ( pullback-hom-large-poset-Subsemigroupᵉ Gᵉ Hᵉ fᵉ)
      ( subset-subsemigroup-hom-large-poset-Semigroupᵉ Hᵉ)
      ( subset-subsemigroup-hom-large-poset-Semigroupᵉ Gᵉ)
      ( pullback-subtype-hom-Large-Posetᵉ (map-hom-Semigroupᵉ Gᵉ Hᵉ fᵉ))
  coherence-square-pullback-subset-Subsemigroupᵉ =
    refl-sim-hom-Large-Posetᵉ
      ( Subsemigroup-Large-Posetᵉ Hᵉ)
      ( powerset-Large-Posetᵉ (type-Semigroupᵉ Gᵉ))
      ( comp-hom-Large-Posetᵉ
        ( Subsemigroup-Large-Posetᵉ Hᵉ)
        ( Subsemigroup-Large-Posetᵉ Gᵉ)
        ( powerset-Large-Posetᵉ (type-Semigroupᵉ Gᵉ))
        ( subset-subsemigroup-hom-large-poset-Semigroupᵉ Gᵉ)
        ( pullback-hom-large-poset-Subsemigroupᵉ Gᵉ Hᵉ fᵉ))
```