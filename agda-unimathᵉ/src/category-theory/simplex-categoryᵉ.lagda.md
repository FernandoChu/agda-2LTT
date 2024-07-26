# The simplex category

```agda
module category-theory.simplex-categoryᵉ where
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

**Theᵉ simplexᵉ category**ᵉ isᵉ theᵉ categoryᵉ consistingᵉ ofᵉ inhabitedᵉ finiteᵉ totalᵉ
ordersᵉ andᵉ
[order-preservingᵉ maps](order-theory.order-preserving-maps-posets.md).ᵉ However,ᵉ
weᵉ defineᵉ itᵉ asᵉ theᵉ categoryᵉ whoseᵉ objectsᵉ areᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.mdᵉ) andᵉ whoseᵉ
hom-[sets](foundation-core.sets.mdᵉ) `homᵉ nᵉ m`ᵉ areᵉ order-preservingᵉ mapsᵉ betweenᵉ
theᵉ [standardᵉ finiteᵉ types](univalent-combinatorics.standard-finite-types.mdᵉ)
`Finᵉ (succ-ℕᵉ n)`ᵉ to `Finᵉ (succ-ℕᵉ m)`ᵉ [equipped](foundation.structure.mdᵉ) with
theᵉ
[standardᵉ ordering](elementary-number-theory.inequality-standard-finite-types.md),ᵉ
andᵉ thenᵉ showᵉ thatᵉ itᵉ isᵉ
[equivalent](category-theory.equivalences-of-precategories.mdᵉ) to theᵉ former.ᵉ

## Definition

### The simplex precategory

```agda
obj-simplex-Categoryᵉ : UUᵉ lzero
obj-simplex-Categoryᵉ = ℕᵉ

hom-set-simplex-Categoryᵉ :
  obj-simplex-Categoryᵉ → obj-simplex-Categoryᵉ → Setᵉ lzero
hom-set-simplex-Categoryᵉ nᵉ mᵉ =
  hom-set-Posetᵉ (Fin-Posetᵉ (succ-ℕᵉ nᵉ)) (Fin-Posetᵉ (succ-ℕᵉ mᵉ))

hom-simplex-Categoryᵉ :
  obj-simplex-Categoryᵉ → obj-simplex-Categoryᵉ → UUᵉ lzero
hom-simplex-Categoryᵉ nᵉ mᵉ = type-Setᵉ (hom-set-simplex-Categoryᵉ nᵉ mᵉ)

comp-hom-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ : obj-simplex-Categoryᵉ} →
  hom-simplex-Categoryᵉ mᵉ rᵉ → hom-simplex-Categoryᵉ nᵉ mᵉ → hom-simplex-Categoryᵉ nᵉ rᵉ
comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} =
  comp-hom-Posetᵉ
    ( Fin-Posetᵉ (succ-ℕᵉ nᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ mᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ rᵉ))

associative-comp-hom-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ sᵉ : obj-simplex-Categoryᵉ}
  (hᵉ : hom-simplex-Categoryᵉ rᵉ sᵉ)
  (gᵉ : hom-simplex-Categoryᵉ mᵉ rᵉ)
  (fᵉ : hom-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {sᵉ}
    ( comp-hom-simplex-Categoryᵉ {mᵉ} {rᵉ} {sᵉ} hᵉ gᵉ)
    ( fᵉ) ＝ᵉ
  comp-hom-simplex-Categoryᵉ {nᵉ} {rᵉ} {sᵉ}
    ( hᵉ)
    ( comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} gᵉ fᵉ)
associative-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  associative-comp-hom-Posetᵉ
    ( Fin-Posetᵉ (succ-ℕᵉ nᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ mᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ rᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ sᵉ))

involutive-eq-associative-comp-hom-simplex-Categoryᵉ :
  {nᵉ mᵉ rᵉ sᵉ : obj-simplex-Categoryᵉ}
  (hᵉ : hom-simplex-Categoryᵉ rᵉ sᵉ)
  (gᵉ : hom-simplex-Categoryᵉ mᵉ rᵉ)
  (fᵉ : hom-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {sᵉ}
    ( comp-hom-simplex-Categoryᵉ {mᵉ} {rᵉ} {sᵉ} hᵉ gᵉ)
    ( fᵉ) ＝ⁱᵉ
  comp-hom-simplex-Categoryᵉ {nᵉ} {rᵉ} {sᵉ}
    ( hᵉ)
    ( comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} gᵉ fᵉ)
involutive-eq-associative-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  involutive-eq-associative-comp-hom-Posetᵉ
    ( Fin-Posetᵉ (succ-ℕᵉ nᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ mᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ rᵉ))
    ( Fin-Posetᵉ (succ-ℕᵉ sᵉ))

associative-composition-operation-simplex-Categoryᵉ :
  associative-composition-operation-binary-family-Setᵉ hom-set-simplex-Categoryᵉ
pr1ᵉ associative-composition-operation-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} =
  comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ}
pr2ᵉ associative-composition-operation-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ} =
  involutive-eq-associative-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {rᵉ} {sᵉ}

id-hom-simplex-Categoryᵉ : (nᵉ : obj-simplex-Categoryᵉ) → hom-simplex-Categoryᵉ nᵉ nᵉ
id-hom-simplex-Categoryᵉ nᵉ = id-hom-Posetᵉ (Fin-Posetᵉ (succ-ℕᵉ nᵉ))

left-unit-law-comp-hom-simplex-Categoryᵉ :
  {nᵉ mᵉ : obj-simplex-Categoryᵉ} (fᵉ : hom-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} {mᵉ} (id-hom-simplex-Categoryᵉ mᵉ) fᵉ ＝ᵉ fᵉ
left-unit-law-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} =
  left-unit-law-comp-hom-Posetᵉ (Fin-Posetᵉ (succ-ℕᵉ nᵉ)) (Fin-Posetᵉ (succ-ℕᵉ mᵉ))

right-unit-law-comp-hom-simplex-Categoryᵉ :
  {nᵉ mᵉ : obj-simplex-Categoryᵉ} (fᵉ : hom-simplex-Categoryᵉ nᵉ mᵉ) →
  comp-hom-simplex-Categoryᵉ {nᵉ} {nᵉ} {mᵉ} fᵉ (id-hom-simplex-Categoryᵉ nᵉ) ＝ᵉ fᵉ
right-unit-law-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ} =
  right-unit-law-comp-hom-Posetᵉ (Fin-Posetᵉ (succ-ℕᵉ nᵉ)) (Fin-Posetᵉ (succ-ℕᵉ mᵉ))

is-unital-composition-operation-simplex-Categoryᵉ :
  is-unital-composition-operation-binary-family-Setᵉ
    ( hom-set-simplex-Categoryᵉ)
    ( comp-hom-simplex-Categoryᵉ)
pr1ᵉ is-unital-composition-operation-simplex-Categoryᵉ = id-hom-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ is-unital-composition-operation-simplex-Categoryᵉ) {nᵉ} {mᵉ} =
  left-unit-law-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ}
pr2ᵉ (pr2ᵉ is-unital-composition-operation-simplex-Categoryᵉ) {nᵉ} {mᵉ} =
  right-unit-law-comp-hom-simplex-Categoryᵉ {nᵉ} {mᵉ}

simplex-Precategoryᵉ : Precategoryᵉ lzero lzero
pr1ᵉ simplex-Precategoryᵉ = obj-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ simplex-Precategoryᵉ) = hom-set-simplex-Categoryᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ simplex-Precategoryᵉ)) =
  associative-composition-operation-simplex-Categoryᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ simplex-Precategoryᵉ)) =
  is-unital-composition-operation-simplex-Categoryᵉ
```

### The simplex category

Itᵉ remainsᵉ to beᵉ formalizedᵉ thatᵉ theᵉ simplexᵉ categoryᵉ isᵉ univalent.ᵉ

## Properties

### The simplex category is equivalent to the category of inhabited finite total orders

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

### The simplex category has a face map and degeneracy unique factorization system

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

### The simplex category has a degeneracy and face map unique factorization system

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

### There is a unique nontrivial involution on the simplex category

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ