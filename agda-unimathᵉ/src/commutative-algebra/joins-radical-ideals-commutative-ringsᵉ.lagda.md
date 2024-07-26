# Joins of radical ideals of commutative rings

```agda
module commutative-algebra.joins-radical-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.intersections-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.joins-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.products-ideals-commutative-ringsᵉ
open import commutative-algebra.products-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-generated-by-subsets-commutative-ringsᵉ
open import commutative-algebra.radicals-of-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
```

</details>

## Idea

Theᵉ **join**ᵉ ofᵉ aᵉ familyᵉ ofᵉ
[radicalᵉ ideals](commutative-algebra.radical-ideals-commutative-rings.mdᵉ)
`αᵉ ↦ᵉ Jᵉ α`ᵉ in aᵉ [commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) isᵉ
theᵉ leastᵉ radicalᵉ idealᵉ containingᵉ eachᵉ `Jᵉ α`.ᵉ

## Definitions

### The universal property of the join of a family of radical ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  is-join-family-of-radical-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) → UUωᵉ
  is-join-family-of-radical-ideals-Commutative-Ringᵉ =
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( Iᵉ)

  inclusion-is-join-family-of-radical-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    is-join-family-of-radical-ideals-Commutative-Ringᵉ Jᵉ →
    {l5ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l5ᵉ Aᵉ) →
    ((αᵉ : Uᵉ) → leq-radical-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ
  inclusion-is-join-family-of-radical-ideals-Commutative-Ringᵉ =
    leq-is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( Iᵉ)

  contains-ideal-is-join-family-of-radical-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    is-join-family-of-radical-ideals-Commutative-Ringᵉ Jᵉ →
    {αᵉ : Uᵉ} → leq-radical-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Jᵉ
  contains-ideal-is-join-family-of-radical-ideals-Commutative-Ringᵉ Jᵉ Hᵉ {αᵉ} =
    is-upper-bound-is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      { xᵉ = Iᵉ}
      { yᵉ = Jᵉ}
      ( Hᵉ)
      ( αᵉ)
```

### The join of a family of radical ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Iᵉ : UUᵉ l2ᵉ} (Jᵉ : Iᵉ → radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  generating-subset-join-family-of-radical-ideals-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Aᵉ
  generating-subset-join-family-of-radical-ideals-Commutative-Ringᵉ =
    generating-subset-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
      ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))

  join-family-of-radical-ideals-Commutative-Ringᵉ :
    radical-ideal-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  join-family-of-radical-ideals-Commutative-Ringᵉ =
    radical-ideal-subset-Commutative-Ringᵉ Aᵉ
      generating-subset-join-family-of-radical-ideals-Commutative-Ringᵉ

  forward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    ((iᵉ : Iᵉ) → leq-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ iᵉ) Kᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ)
      ( Kᵉ)
  forward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ
    Kᵉ Hᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))
      ( Kᵉ)
      ( forward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)
        ( Hᵉ))

  backward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ)
      ( Kᵉ) →
    (iᵉ : Iᵉ) → leq-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ iᵉ) Kᵉ
  backward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ
    Kᵉ Hᵉ iᵉ xᵉ pᵉ =
    Hᵉ ( xᵉ)
      ( contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))
        ( xᵉ)
        ( backward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))
          ( λ tᵉ → idᵉ)
          ( iᵉ)
          ( xᵉ)
          ( pᵉ)))

  is-join-join-family-of-radical-ideals-Commutative-Ringᵉ :
    is-join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ
      join-family-of-radical-ideals-Commutative-Ringᵉ
  pr1ᵉ (is-join-join-family-of-radical-ideals-Commutative-Ringᵉ Kᵉ) =
    forward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ Kᵉ
  pr2ᵉ (is-join-join-family-of-radical-ideals-Commutative-Ringᵉ Kᵉ) =
    backward-inclusion-is-join-join-family-of-radical-ideals-Commutative-Ringᵉ
      Kᵉ
```

### The large suplattice of radical ideals in a commutative ring

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-large-suplattice-radical-ideal-Commutative-Ringᵉ :
    is-large-suplattice-Large-Posetᵉ l1ᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-radical-ideal-Commutative-Ringᵉ Iᵉ) =
    join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Iᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-radical-ideal-Commutative-Ringᵉ Iᵉ) =
    is-join-join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Iᵉ

  radical-ideal-Commutative-Ring-Large-Suplatticeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  large-poset-Large-Suplatticeᵉ
    radical-ideal-Commutative-Ring-Large-Suplatticeᵉ =
    radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    radical-ideal-Commutative-Ring-Large-Suplatticeᵉ =
    is-large-suplattice-radical-ideal-Commutative-Ringᵉ
```

## Properties

### Join is an order preserving operation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ}
  (Iᵉ : Uᵉ → radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Jᵉ : Uᵉ → radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  (Hᵉ : (αᵉ : Uᵉ) → leq-radical-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) (Jᵉ αᵉ))
  where

  preserves-order-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ)
  preserves-order-join-family-of-radical-ideals-Commutative-Ringᵉ =
    preserves-order-sup-Large-Suplatticeᵉ
      ( radical-ideal-Commutative-Ring-Large-Suplatticeᵉ Aᵉ)
      { xᵉ = Iᵉ}
      { yᵉ = Jᵉ}
      ( Hᵉ)
```

### `√ (⋁_α √ I_α) ＝ √ (⋁_α I_α)` for any family `I` of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
  forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( forward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ))
        ( ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
        ( λ αᵉ →
          is-radical-of-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
            ( Iᵉ αᵉ)
            ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
              ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
            ( λ xᵉ pᵉ →
              contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ
                ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ)
                ( xᵉ)
                ( contains-ideal-join-family-of-ideals-Commutative-Ringᵉ
                  Aᵉ Iᵉ xᵉ pᵉ))))

  backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))
  backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ =
    preserves-order-radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))
      ( preserves-order-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( λ αᵉ → ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ))
        ( λ αᵉ → contains-ideal-radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))

  radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ :
    join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
      ( λ αᵉ → radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)) ＝ᵉ
    radical-of-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ)
  radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ =
    antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → radical-of-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ)))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ))
      ( forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ)
      ( backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ)
```

### Products of radical ideals distribute over joins

Considerᵉ aᵉ radicalᵉ idealᵉ `I`ᵉ andᵉ aᵉ familyᵉ ofᵉ radicalᵉ idealsᵉ `J_α`ᵉ indexedᵉ byᵉ
`αᵉ : U`.ᵉ Toᵉ proveᵉ distributivity,ᵉ weᵉ makeᵉ theᵉ followingᵉ calculationᵉ where weᵉ
willᵉ writeᵉ `·r`ᵉ forᵉ theᵉ productᵉ ofᵉ radicalᵉ idealsᵉ andᵉ `⋁r`ᵉ forᵉ theᵉ joinᵉ ofᵉ aᵉ
familyᵉ ofᵉ radicalᵉ ideals.ᵉ

```text
  Iᵉ ·rᵉ (⋁r_αᵉ J_αᵉ) ＝ᵉ √ᵉ (Iᵉ ·ᵉ √ᵉ (⋁_αᵉ J_αᵉ))
                  ＝ᵉ √ᵉ (Iᵉ ·ᵉ (⋁_αᵉ J_αᵉ))
                  ＝ᵉ √ᵉ (⋁_αᵉ (Iᵉ ·ᵉ J_αᵉ))
                  ＝ᵉ √ᵉ (⋁_αᵉ √ᵉ (Iᵉ ·ᵉ J_αᵉ))
                  ＝ᵉ ⋁r_αᵉ (Iᵉ ·rᵉ J_αᵉ)
```

Theᵉ proofᵉ belowᵉ proceedsᵉ byᵉ provingᵉ inclusionsᵉ in bothᵉ directionsᵉ alongᵉ theᵉ
computationᵉ stepsᵉ above.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  {Uᵉ : UUᵉ l3ᵉ} (Jᵉ : Uᵉ → radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
  forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ =
    transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( product-ideal-Commutative-Ringᵉ Aᵉ
          ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( product-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
              ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ →
              product-ideal-Commutative-Ringᵉ Aᵉ
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( backward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ
          ( Aᵉ)
          ( λ αᵉ →
            product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
        ( preserves-order-radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( product-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
              ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ →
              product-ideal-Commutative-Ringᵉ Aᵉ
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
          ( forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ
            ( Aᵉ)
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
      ( forward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ
        ( Aᵉ)
        ( Iᵉ)
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))

  backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
  backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ =
    transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ →
            product-ideal-Commutative-Ringᵉ Aᵉ
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
              ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ →
              product-ideal-Commutative-Ringᵉ Aᵉ
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
        ( radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( product-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
              ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
        ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
          ( Iᵉ)
          ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( backward-inclusion-right-radical-law-product-radical-ideal-Commutative-Ringᵉ
          ( Aᵉ)
          ( Iᵉ)
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
        ( preserves-order-radical-of-ideal-Commutative-Ringᵉ Aᵉ
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
            ( λ αᵉ →
              product-ideal-Commutative-Ringᵉ Aᵉ
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
                ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
          ( product-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
              ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
          ( backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ
            ( Aᵉ)
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( λ αᵉ → ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ)))))
      ( forward-inclusion-radical-law-join-family-of-radical-ideals-Commutative-Ringᵉ
        ( Aᵉ)
        ( λ αᵉ →
          product-ideal-Commutative-Ringᵉ Aᵉ
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
            ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))

  sim-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ :
    sim-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
  pr1ᵉ sim-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ =
    forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ
  pr2ᵉ sim-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ =
    backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ

  distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ :
    product-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( Iᵉ)
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ) ＝ᵉ
    join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
      ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
  distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ =
    antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ)
      ( backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ)
```

### Intersections of radical ideals distribute over joins

Sinceᵉ theᵉ
[intersection](commutative-algebra.intersections-radical-ideals-commutative-rings.mdᵉ)
`Iᵉ ∩ᵉ J`ᵉ ofᵉ twoᵉ radicalᵉ idealsᵉ isᵉ theᵉ
[product](commutative-algebra.products-radical-ideals-commutative-rings.mdᵉ) `IJ`ᵉ
ofᵉ radicalᵉ ideals,ᵉ itᵉ followsᵉ thatᵉ intersectionsᵉ distributeᵉ overᵉ joinsᵉ ofᵉ
radicalᵉ ideals.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  {Uᵉ : UUᵉ l3ᵉ} (Jᵉ : Uᵉ → radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
  forward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ =
    transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
          ( Iᵉ)
          ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( preserves-order-join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
          ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
          ( λ αᵉ →
            backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
              ( Jᵉ αᵉ)))
        ( forward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ
          ( Aᵉ)
          ( Iᵉ)
          ( Jᵉ)))
      ( forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))

  backward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ :
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
  backward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ =
    transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( product-radical-ideal-Commutative-Ringᵉ Aᵉ
          ( Iᵉ)
          ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
          ( Iᵉ)
          ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( backward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
          ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
        ( backward-inclusion-distributive-product-join-family-of-radical-ideals-Commutative-Ringᵉ
          ( Aᵉ)
          ( Iᵉ)
          ( Jᵉ)))
      ( preserves-order-join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
        ( λ αᵉ → product-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
        ( λ αᵉ →
          forward-inclusion-intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
            ( Jᵉ αᵉ)))

  distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ :
    intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( Iᵉ)
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ) ＝ᵉ
    join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
      ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
  distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ =
    antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
      ( intersection-radical-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → intersection-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( forward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ)
      ( backward-inclusion-distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ)
```