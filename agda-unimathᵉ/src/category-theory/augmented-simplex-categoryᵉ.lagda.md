# The augmented simplex category

```agda
module category-theory.augmented-simplex-categoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.precategoriesᵉ

open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.order-preserving-maps-posetsᵉ
```

</details>

## Idea

**Theᵉ augmentedᵉ simplexᵉ category**ᵉ isᵉ theᵉ categoryᵉ consistingᵉ ofᵉ
[finiteᵉ totalᵉ orders](order-theory.finite-total-orders.mdᵉ) andᵉ
[order-preservingᵉ maps](order-theory.order-preserving-maps-posets.md).ᵉ However,ᵉ
weᵉ defineᵉ itᵉ asᵉ theᵉ categoryᵉ whoseᵉ objectsᵉ areᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.mdᵉ) andᵉ whoseᵉ
hom-[sets](foundation-core.sets.mdᵉ) `homᵉ nᵉ m`ᵉ areᵉ order-preservingᵉ mapsᵉ betweenᵉ
theᵉ [standardᵉ finiteᵉ types](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ n`ᵉ to `Finᵉ m`ᵉ [equipped](foundation.structure.mdᵉ) with theᵉ
[standardᵉ ordering](elementary-number-theory.inequality-standard-finite-types.md),ᵉ
andᵉ thenᵉ showᵉ thatᵉ itᵉ isᵉ
[equivalent](category-theory.equivalences-of-precategories.mdᵉ) to theᵉ former.ᵉ

## Definition

### The augmented simplex precategory

```agda
obj-augmented-simplex-Categoryᵉ : UUᵉ lzero
obj-augmented-simplex-Categoryᵉ = ℕᵉ

hom-set-augmented-simplex-Categoryᵉ :
  obj-augmented-simplex-Categoryᵉ → obj-augmented-simplex-Categoryᵉ → Setᵉ lzero
hom-set-augmented-simplex-Categoryᵉ nᵉ mᵉ =
  hom-set-Posetᵉ (Fin-Posetᵉ nᵉ) (Fin-Posetᵉ mᵉ)

hom-augmented-simplex-Categoryᵉ :
  obj-augmented-simplex-Categoryᵉ → obj-augmented-simplex-Categoryᵉ → UUᵉ lzero
hom-augmented-simplex-Categoryᵉ nᵉ mᵉ =
  type-Setᵉ (hom-set-augmented-simplex-Categoryᵉ nᵉ mᵉ)

comp-hom-augmented-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ : obj-augmented-simplex-Categoryᵉ} →
  hom-augmented-simplex-Categoryᵉ mᵉ rᵉ →
  hom-augmented-simplex-Categoryᵉ nᵉ mᵉ →
  hom-augmented-simplex-Categoryᵉ nᵉ rᵉ
comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} =
  comp-hom-Posetᵉ (Fin-Posetᵉ nᵉ) (Fin-Posetᵉ mᵉ) (Fin-Posetᵉ rᵉ)

associative-comp-hom-augmented-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ sᵉ : obj-augmented-simplex-Categoryᵉ}
  (hᵉ : hom-augmented-simplex-Categoryᵉ rᵉ sᵉ)
  (gᵉ : hom-augmented-simplex-Categoryᵉ mᵉ rᵉ)
  (fᵉ : hom-augmented-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {sᵉ}
    ( comp-hom-augmented-simplex-Categoryᵉ {mᵉ} {rᵉ} {sᵉ} hᵉ gᵉ)
    ( fᵉ) ＝ᵉ
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {rᵉ} {sᵉ}
    ( hᵉ)
    ( comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} gᵉ fᵉ)
associative-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  associative-comp-hom-Posetᵉ
    ( Fin-Posetᵉ nᵉ)
    ( Fin-Posetᵉ mᵉ)
    ( Fin-Posetᵉ rᵉ)
    ( Fin-Posetᵉ sᵉ)

involutive-eq-associative-comp-hom-augmented-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ sᵉ : obj-augmented-simplex-Categoryᵉ}
  (hᵉ : hom-augmented-simplex-Categoryᵉ rᵉ sᵉ)
  (gᵉ : hom-augmented-simplex-Categoryᵉ mᵉ rᵉ)
  (fᵉ : hom-augmented-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {sᵉ}
    ( comp-hom-augmented-simplex-Categoryᵉ {mᵉ} {rᵉ} {sᵉ} hᵉ gᵉ)
    ( fᵉ) ＝ⁱᵉ
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {rᵉ} {sᵉ}
    ( hᵉ)
    ( comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} gᵉ fᵉ)
involutive-eq-associative-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  involutive-eq-associative-comp-hom-Posetᵉ
    ( Fin-Posetᵉ nᵉ)
    ( Fin-Posetᵉ mᵉ)
    ( Fin-Posetᵉ rᵉ)
    ( Fin-Posetᵉ sᵉ)

associative-composition-operation-augmented-simplex-Categoryᵉ :
  associative-composition-operation-binary-family-Setᵉ
    hom-set-augmented-simplex-Categoryᵉ
pr1ᵉ associative-composition-operation-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} =
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ}
pr2ᵉ associative-composition-operation-augmented-simplex-Categoryᵉ
  { nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  involutive-eq-associative-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ}

id-hom-augmented-simplex-Categoryᵉ :
  (nᵉ : obj-augmented-simplex-Categoryᵉ) → hom-augmented-simplex-Categoryᵉ nᵉ nᵉ
id-hom-augmented-simplex-Categoryᵉ nᵉ = id-hom-Posetᵉ (Fin-Posetᵉ nᵉ)

left-unit-law-comp-hom-augmented-simplex-Categoryᵉ :
  {nᵉ mᵉ : obj-augmented-simplex-Categoryᵉ}
  (fᵉ : hom-augmented-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {mᵉ}
    ( id-hom-augmented-simplex-Categoryᵉ mᵉ)
    ( fᵉ) ＝ᵉ
  fᵉ
left-unit-law-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} =
  left-unit-law-comp-hom-Posetᵉ (Fin-Posetᵉ nᵉ) (Fin-Posetᵉ mᵉ)

right-unit-law-comp-hom-augmented-simplex-Categoryᵉ :
  {nᵉ mᵉ : obj-augmented-simplex-Categoryᵉ}
  (fᵉ : hom-augmented-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {nᵉ} {mᵉ}
    ( fᵉ)
    ( id-hom-augmented-simplex-Categoryᵉ nᵉ) ＝ᵉ
  fᵉ
right-unit-law-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} =
  right-unit-law-comp-hom-Posetᵉ (Fin-Posetᵉ nᵉ) (Fin-Posetᵉ mᵉ)

is-unital-composition-operation-augmented-simplex-Categoryᵉ :
  is-unital-composition-operation-binary-family-Setᵉ
    ( hom-set-augmented-simplex-Categoryᵉ)
    ( λ {nᵉ} {mᵉ} {rᵉ} → comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ})
pr1ᵉ is-unital-composition-operation-augmented-simplex-Categoryᵉ =
  id-hom-augmented-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ is-unital-composition-operation-augmented-simplex-Categoryᵉ) {nᵉ} {mᵉ} =
  left-unit-law-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ}
pr2ᵉ (pr2ᵉ is-unital-composition-operation-augmented-simplex-Categoryᵉ) {nᵉ} {mᵉ} =
  right-unit-law-comp-hom-augmented-simplex-Categoryᵉ {nᵉ} {mᵉ}

augmented-simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
pr1ᵉ augmented-simplex-Precategoryᵉ = obj-augmented-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ augmented-simplex-Precategoryᵉ) = hom-set-augmented-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ augmented-simplex-Precategoryᵉ)) =
  associative-composition-operation-augmented-simplex-Categoryᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ augmented-simplex-Precategoryᵉ)) =
  is-unital-composition-operation-augmented-simplex-Categoryᵉ
```

### The augmented simplex category

Itᵉ remainsᵉ to beᵉ formalizedᵉ thatᵉ theᵉ augmentedᵉ simplexᵉ categoryᵉ isᵉ univalent.ᵉ

## Properties

### The augmented simplex category is equivalent to the category of finite total orders

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ