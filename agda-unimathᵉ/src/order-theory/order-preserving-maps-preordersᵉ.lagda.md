# Order preserving maps on preorders

```agda
module order-theory.order-preserving-maps-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ mapᵉ `fᵉ : Pᵉ → Q`ᵉ betweenᵉ theᵉ underlyingᵉ typesᵉ ofᵉ twoᵉ preordersᵉ isᵉ saidᵉ to beᵉ
**orderᵉ preserving**ᵉ ifᵉ `xᵉ ≤ᵉ y`ᵉ in `P`ᵉ impliesᵉ `fᵉ xᵉ ≤ᵉ fᵉ y`ᵉ in `Q`.ᵉ

## Definition

### Order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Qᵉ : Preorderᵉ l3ᵉ l4ᵉ)
  where

  preserves-order-Preorder-Propᵉ :
    (type-Preorderᵉ Pᵉ → type-Preorderᵉ Qᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-order-Preorder-Propᵉ fᵉ =
    Π-Propᵉ
      ( type-Preorderᵉ Pᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Preorderᵉ Pᵉ)
          ( λ yᵉ →
            hom-Propᵉ
              ( leq-Preorder-Propᵉ Pᵉ xᵉ yᵉ)
              ( leq-Preorder-Propᵉ Qᵉ (fᵉ xᵉ) (fᵉ yᵉ))))

  preserves-order-Preorderᵉ :
    (type-Preorderᵉ Pᵉ → type-Preorderᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-order-Preorderᵉ fᵉ =
    type-Propᵉ (preserves-order-Preorder-Propᵉ fᵉ)

  is-prop-preserves-order-Preorderᵉ :
    (fᵉ : type-Preorderᵉ Pᵉ → type-Preorderᵉ Qᵉ) →
    is-propᵉ (preserves-order-Preorderᵉ fᵉ)
  is-prop-preserves-order-Preorderᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-order-Preorder-Propᵉ fᵉ)

  hom-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-Preorderᵉ =
    Σᵉ (type-Preorderᵉ Pᵉ → type-Preorderᵉ Qᵉ) preserves-order-Preorderᵉ

  map-hom-Preorderᵉ : hom-Preorderᵉ → type-Preorderᵉ Pᵉ → type-Preorderᵉ Qᵉ
  map-hom-Preorderᵉ = pr1ᵉ

  preserves-order-map-hom-Preorderᵉ :
    (fᵉ : hom-Preorderᵉ) → preserves-order-Preorderᵉ (map-hom-Preorderᵉ fᵉ)
  preserves-order-map-hom-Preorderᵉ = pr2ᵉ
```

### Homotopies of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Qᵉ : Preorderᵉ l3ᵉ l4ᵉ)
  where

  htpy-hom-Preorderᵉ : (fᵉ gᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-hom-Preorderᵉ fᵉ gᵉ = map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ ~ᵉ map-hom-Preorderᵉ Pᵉ Qᵉ gᵉ

  refl-htpy-hom-Preorderᵉ : (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → htpy-hom-Preorderᵉ fᵉ fᵉ
  refl-htpy-hom-Preorderᵉ fᵉ = refl-htpyᵉ

  htpy-eq-hom-Preorderᵉ :
    (fᵉ gᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → Idᵉ fᵉ gᵉ → htpy-hom-Preorderᵉ fᵉ gᵉ
  htpy-eq-hom-Preorderᵉ fᵉ .fᵉ reflᵉ = refl-htpy-hom-Preorderᵉ fᵉ

  is-torsorial-htpy-hom-Preorderᵉ :
    (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → is-torsorialᵉ (htpy-hom-Preorderᵉ fᵉ)
  is-torsorial-htpy-hom-Preorderᵉ fᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ))
      ( is-prop-preserves-order-Preorderᵉ Pᵉ Qᵉ)
      ( map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ)
      ( refl-htpyᵉ)
      ( preserves-order-map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ)

  is-equiv-htpy-eq-hom-Preorderᵉ :
    (fᵉ gᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → is-equivᵉ (htpy-eq-hom-Preorderᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-Preorderᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-Preorderᵉ fᵉ)
      ( htpy-eq-hom-Preorderᵉ fᵉ)

  extensionality-hom-Preorderᵉ :
    (fᵉ gᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → Idᵉ fᵉ gᵉ ≃ᵉ htpy-hom-Preorderᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-Preorderᵉ fᵉ gᵉ) = htpy-eq-hom-Preorderᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-Preorderᵉ fᵉ gᵉ) = is-equiv-htpy-eq-hom-Preorderᵉ fᵉ gᵉ

  eq-htpy-hom-Preorderᵉ :
    (fᵉ gᵉ : hom-Preorderᵉ Pᵉ Qᵉ) → htpy-hom-Preorderᵉ fᵉ gᵉ → Idᵉ fᵉ gᵉ
  eq-htpy-hom-Preorderᵉ fᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-Preorderᵉ fᵉ gᵉ)
```

### The identity order preserving map

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  preserves-order-id-Preorderᵉ :
    preserves-order-Preorderᵉ Pᵉ Pᵉ (idᵉ {Aᵉ = type-Preorderᵉ Pᵉ})
  preserves-order-id-Preorderᵉ xᵉ yᵉ = idᵉ

  id-hom-Preorderᵉ : hom-Preorderᵉ Pᵉ Pᵉ
  pr1ᵉ id-hom-Preorderᵉ = idᵉ
  pr2ᵉ id-hom-Preorderᵉ = preserves-order-id-Preorderᵉ
```

### Composing order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Qᵉ : Preorderᵉ l3ᵉ l4ᵉ) (Rᵉ : Preorderᵉ l5ᵉ l6ᵉ)
  where

  preserves-order-comp-Preorderᵉ :
    (gᵉ : hom-Preorderᵉ Qᵉ Rᵉ) (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) →
    preserves-order-Preorderᵉ Pᵉ Rᵉ
      ( map-hom-Preorderᵉ Qᵉ Rᵉ gᵉ ∘ᵉ map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ)
  preserves-order-comp-Preorderᵉ gᵉ fᵉ xᵉ yᵉ Hᵉ =
    preserves-order-map-hom-Preorderᵉ Qᵉ Rᵉ gᵉ
      ( map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ xᵉ)
      ( map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ yᵉ)
      ( preserves-order-map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ xᵉ yᵉ Hᵉ)

  comp-hom-Preorderᵉ :
    (gᵉ : hom-Preorderᵉ Qᵉ Rᵉ) (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) →
    hom-Preorderᵉ Pᵉ Rᵉ
  pr1ᵉ (comp-hom-Preorderᵉ gᵉ fᵉ) =
    map-hom-Preorderᵉ Qᵉ Rᵉ gᵉ ∘ᵉ map-hom-Preorderᵉ Pᵉ Qᵉ fᵉ
  pr2ᵉ (comp-hom-Preorderᵉ gᵉ fᵉ) =
    preserves-order-comp-Preorderᵉ gᵉ fᵉ
```

### Unit laws for composition of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Qᵉ : Preorderᵉ l3ᵉ l4ᵉ)
  where

  left-unit-law-comp-hom-Preorderᵉ :
    (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) →
    Idᵉ ( comp-hom-Preorderᵉ Pᵉ Qᵉ Qᵉ (id-hom-Preorderᵉ Qᵉ) fᵉ) fᵉ
  left-unit-law-comp-hom-Preorderᵉ fᵉ =
    eq-htpy-hom-Preorderᵉ Pᵉ Qᵉ
      ( comp-hom-Preorderᵉ Pᵉ Qᵉ Qᵉ (id-hom-Preorderᵉ Qᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-hom-Preorderᵉ :
    (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ) →
    Idᵉ (comp-hom-Preorderᵉ Pᵉ Pᵉ Qᵉ fᵉ (id-hom-Preorderᵉ Pᵉ)) fᵉ
  right-unit-law-comp-hom-Preorderᵉ fᵉ =
    eq-htpy-hom-Preorderᵉ Pᵉ Qᵉ
      ( comp-hom-Preorderᵉ Pᵉ Pᵉ Qᵉ fᵉ (id-hom-Preorderᵉ Pᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)
```

### Associativity of composition of order preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Qᵉ : Preorderᵉ l3ᵉ l4ᵉ)
  (Rᵉ : Preorderᵉ l5ᵉ l6ᵉ) (Sᵉ : Preorderᵉ l7ᵉ l8ᵉ)
  (hᵉ : hom-Preorderᵉ Rᵉ Sᵉ)
  (gᵉ : hom-Preorderᵉ Qᵉ Rᵉ)
  (fᵉ : hom-Preorderᵉ Pᵉ Qᵉ)
  where

  associative-comp-hom-Preorderᵉ :
    comp-hom-Preorderᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Preorderᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Preorderᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Preorderᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ)
  associative-comp-hom-Preorderᵉ =
    eq-htpy-hom-Preorderᵉ Pᵉ Sᵉ
      ( comp-hom-Preorderᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Preorderᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Preorderᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Preorderᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)

  involutive-eq-associative-comp-hom-Preorderᵉ :
    comp-hom-Preorderᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Preorderᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Preorderᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Preorderᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Preorderᵉ =
    involutive-eq-eqᵉ associative-comp-hom-Preorderᵉ
```