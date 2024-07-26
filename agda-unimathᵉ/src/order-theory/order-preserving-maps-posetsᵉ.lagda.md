# Order preserving maps on posets

```agda
module order-theory.order-preserving-maps-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.order-preserving-maps-preordersᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Pᵉ → Q`ᵉ betweenᵉ theᵉ underlyingᵉ typesᵉ ofᵉ twoᵉ posetsᵉ isᵉ siadᵉ to beᵉ
**orderᵉ preserving**ᵉ ifᵉ `xᵉ ≤ᵉ y`ᵉ in `P`ᵉ impliesᵉ `fᵉ xᵉ ≤ᵉ fᵉ y`ᵉ in `Q`.ᵉ

## Definition

### Order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  preserves-order-Poset-Propᵉ :
    (type-Posetᵉ Pᵉ → type-Posetᵉ Qᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-order-Poset-Propᵉ =
    preserves-order-Preorder-Propᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  preserves-order-Posetᵉ :
    (type-Posetᵉ Pᵉ → type-Posetᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-order-Posetᵉ =
    preserves-order-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  is-prop-preserves-order-Posetᵉ :
    (fᵉ : type-Posetᵉ Pᵉ → type-Posetᵉ Qᵉ) → is-propᵉ (preserves-order-Posetᵉ fᵉ)
  is-prop-preserves-order-Posetᵉ =
    is-prop-preserves-order-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  hom-set-Posetᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-set-Posetᵉ =
    set-subsetᵉ
      ( function-Setᵉ (type-Posetᵉ Pᵉ) (set-Posetᵉ Qᵉ))
      ( preserves-order-Poset-Propᵉ)

  hom-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-Posetᵉ = type-Setᵉ hom-set-Posetᵉ

  map-hom-Posetᵉ : hom-Posetᵉ → type-Posetᵉ Pᵉ → type-Posetᵉ Qᵉ
  map-hom-Posetᵉ = map-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  preserves-order-map-hom-Posetᵉ :
    (fᵉ : hom-Posetᵉ) → preserves-order-Posetᵉ (map-hom-Posetᵉ fᵉ)
  preserves-order-map-hom-Posetᵉ =
    preserves-order-map-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)
```

### Homotopies of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  htpy-hom-Posetᵉ : (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-hom-Posetᵉ = htpy-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  refl-htpy-hom-Posetᵉ : (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) → htpy-hom-Posetᵉ fᵉ fᵉ
  refl-htpy-hom-Posetᵉ =
    refl-htpy-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  htpy-eq-hom-Posetᵉ :
    (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Posetᵉ fᵉ gᵉ
  htpy-eq-hom-Posetᵉ = htpy-eq-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  is-torsorial-htpy-hom-Posetᵉ :
    (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) → is-torsorialᵉ (htpy-hom-Posetᵉ fᵉ)
  is-torsorial-htpy-hom-Posetᵉ =
    is-torsorial-htpy-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  is-equiv-htpy-eq-hom-Posetᵉ :
    (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → is-equivᵉ (htpy-eq-hom-Posetᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Posetᵉ =
    is-equiv-htpy-eq-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  extensionality-hom-Posetᵉ :
    (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-Posetᵉ fᵉ gᵉ
  extensionality-hom-Posetᵉ =
    extensionality-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  eq-htpy-hom-Posetᵉ :
    (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → htpy-hom-Posetᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Posetᵉ = eq-htpy-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  is-prop-htpy-hom-Posetᵉ :
    (fᵉ gᵉ : hom-Posetᵉ Pᵉ Qᵉ) → is-propᵉ (htpy-hom-Posetᵉ fᵉ gᵉ)
  is-prop-htpy-hom-Posetᵉ fᵉ gᵉ =
    is-prop-Πᵉ
      ( λ xᵉ →
        is-set-type-Posetᵉ Qᵉ
          ( map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ)
          ( map-hom-Posetᵉ Pᵉ Qᵉ gᵉ xᵉ))
```

### The identity order preserving map

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  preserves-order-id-Posetᵉ :
    preserves-order-Posetᵉ Pᵉ Pᵉ (idᵉ {Aᵉ = type-Posetᵉ Pᵉ})
  preserves-order-id-Posetᵉ = preserves-order-id-Preorderᵉ (preorder-Posetᵉ Pᵉ)

  id-hom-Posetᵉ : hom-Posetᵉ Pᵉ Pᵉ
  id-hom-Posetᵉ = id-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ)
```

### Composing order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ) (Rᵉ : Posetᵉ l5ᵉ l6ᵉ)
  where

  preserves-order-comp-Posetᵉ :
    (gᵉ : hom-Posetᵉ Qᵉ Rᵉ) (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) →
    preserves-order-Posetᵉ Pᵉ Rᵉ
      ( map-hom-Posetᵉ Qᵉ Rᵉ gᵉ ∘ᵉ map-hom-Posetᵉ Pᵉ Qᵉ fᵉ)
  preserves-order-comp-Posetᵉ =
    preserves-order-comp-Preorderᵉ
      ( preorder-Posetᵉ Pᵉ)
      ( preorder-Posetᵉ Qᵉ)
      ( preorder-Posetᵉ Rᵉ)

  comp-hom-Posetᵉ :
    (gᵉ : hom-Posetᵉ Qᵉ Rᵉ) (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) → hom-Posetᵉ Pᵉ Rᵉ
  comp-hom-Posetᵉ =
    comp-hom-Preorderᵉ
      ( preorder-Posetᵉ Pᵉ)
      ( preorder-Posetᵉ Qᵉ)
      ( preorder-Posetᵉ Rᵉ)
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  left-unit-law-comp-hom-Posetᵉ :
    (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) →
    Idᵉ ( comp-hom-Posetᵉ Pᵉ Qᵉ Qᵉ (id-hom-Posetᵉ Qᵉ) fᵉ) fᵉ
  left-unit-law-comp-hom-Posetᵉ =
    left-unit-law-comp-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)

  right-unit-law-comp-hom-Posetᵉ :
    (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) →
    Idᵉ (comp-hom-Posetᵉ Pᵉ Pᵉ Qᵉ fᵉ (id-hom-Posetᵉ Pᵉ)) fᵉ
  right-unit-law-comp-hom-Posetᵉ =
    right-unit-law-comp-hom-Preorderᵉ (preorder-Posetᵉ Pᵉ) (preorder-Posetᵉ Qᵉ)
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (Rᵉ : Posetᵉ l5ᵉ l6ᵉ) (Sᵉ : Posetᵉ l7ᵉ l8ᵉ)
  where

  associative-comp-hom-Posetᵉ :
    (hᵉ : hom-Posetᵉ Rᵉ Sᵉ) (gᵉ : hom-Posetᵉ Qᵉ Rᵉ) (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) →
    comp-hom-Posetᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Posetᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Posetᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Posetᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ)
  associative-comp-hom-Posetᵉ =
    associative-comp-hom-Preorderᵉ
      ( preorder-Posetᵉ Pᵉ)
      ( preorder-Posetᵉ Qᵉ)
      ( preorder-Posetᵉ Rᵉ)
      ( preorder-Posetᵉ Sᵉ)

  involutive-eq-associative-comp-hom-Posetᵉ :
    (hᵉ : hom-Posetᵉ Rᵉ Sᵉ) (gᵉ : hom-Posetᵉ Qᵉ Rᵉ) (fᵉ : hom-Posetᵉ Pᵉ Qᵉ) →
    comp-hom-Posetᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Posetᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Posetᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Posetᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Posetᵉ =
    involutive-eq-associative-comp-hom-Preorderᵉ
      ( preorder-Posetᵉ Pᵉ)
      ( preorder-Posetᵉ Qᵉ)
      ( preorder-Posetᵉ Rᵉ)
      ( preorder-Posetᵉ Sᵉ)
```