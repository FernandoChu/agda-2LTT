# Minimum on the standard finite types

```agda
module elementary-number-theory.minimum-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ

open import order-theory.greatest-lower-bounds-posetsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ operationᵉ ofᵉ minimumᵉ (greatestᵉ lowerᵉ boundᵉ) forᵉ theᵉ standardᵉ
finiteᵉ types.ᵉ

## Definition

```agda
min-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (min-Finᵉ kᵉ xᵉ yᵉ)
min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ _) = inlᵉ xᵉ
min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inlᵉ xᵉ) = inlᵉ xᵉ
min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inrᵉ _) = inrᵉ starᵉ

min-Fin-Finᵉ : (nᵉ kᵉ : ℕᵉ) → (Finᵉ (succ-ℕᵉ nᵉ) → Finᵉ kᵉ) → Finᵉ kᵉ
min-Fin-Finᵉ zero-ℕᵉ kᵉ fᵉ = fᵉ (inrᵉ starᵉ)
min-Fin-Finᵉ (succ-ℕᵉ nᵉ) kᵉ fᵉ =
  min-Finᵉ kᵉ (fᵉ (inrᵉ starᵉ)) (min-Fin-Finᵉ nᵉ kᵉ (λ kᵉ → fᵉ (inlᵉ kᵉ)))
```

## Properties

### Minimum is a greatest lower bound

Weᵉ proveᵉ thatᵉ `min-Fin`ᵉ isᵉ aᵉ greatestᵉ lowerᵉ boundᵉ ofᵉ itsᵉ twoᵉ argumentsᵉ byᵉ
showingᵉ thatᵉ `min(m,nᵉ) ≤ᵉ x`ᵉ isᵉ equivalentᵉ to `(mᵉ ≤ᵉ xᵉ) ∧ᵉ (nᵉ ≤ᵉ x)`,ᵉ in components.ᵉ
Byᵉ reflexivityᵉ ofᵉ `≤`,ᵉ weᵉ computeᵉ thatᵉ `min(m,nᵉ) ≤ᵉ m`ᵉ (andᵉ correspondinglyᵉ forᵉ
`n`).ᵉ

```agda
leq-min-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) →
  leq-Finᵉ kᵉ lᵉ mᵉ → leq-Finᵉ kᵉ lᵉ nᵉ → leq-Finᵉ kᵉ lᵉ (min-Finᵉ kᵉ mᵉ nᵉ)
leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ qᵉ = leq-min-Finᵉ kᵉ xᵉ yᵉ zᵉ pᵉ qᵉ
leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) pᵉ qᵉ = pᵉ
leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) pᵉ qᵉ = qᵉ
leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ qᵉ = starᵉ
leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ qᵉ = starᵉ

leq-left-leq-min-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ lᵉ (min-Finᵉ kᵉ mᵉ nᵉ) → leq-Finᵉ kᵉ lᵉ mᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ =
  leq-left-leq-min-Finᵉ kᵉ xᵉ yᵉ zᵉ pᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ _) pᵉ = pᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ _) (inlᵉ _) pᵉ = starᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ _) (inrᵉ _) pᵉ = starᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inlᵉ yᵉ) (inrᵉ _) pᵉ = pᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inrᵉ _) (inlᵉ _) pᵉ = starᵉ
leq-left-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inrᵉ _) (inrᵉ _) pᵉ = starᵉ

leq-right-leq-min-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ lᵉ (min-Finᵉ kᵉ mᵉ nᵉ) → leq-Finᵉ kᵉ lᵉ nᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ x₁ᵉ) (inlᵉ x₂ᵉ) pᵉ =
  leq-right-leq-min-Finᵉ kᵉ xᵉ x₁ᵉ x₂ᵉ pᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ x₁ᵉ) (inrᵉ x₂ᵉ) pᵉ = starᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ x₁ᵉ) (inlᵉ x₂ᵉ) pᵉ = pᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ x₁ᵉ) (inrᵉ x₂ᵉ) pᵉ = starᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ x₁ᵉ) (inrᵉ x₂ᵉ) pᵉ = starᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ x₁ᵉ) (inlᵉ x₂ᵉ) pᵉ = pᵉ
leq-right-leq-min-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ x₁ᵉ) (inlᵉ x₂ᵉ) pᵉ = pᵉ

is-greatest-lower-bound-min-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ : Finᵉ kᵉ) →
  is-greatest-binary-lower-bound-Posetᵉ (Fin-Posetᵉ kᵉ) lᵉ mᵉ (min-Finᵉ kᵉ lᵉ mᵉ)
is-greatest-lower-bound-min-Finᵉ kᵉ lᵉ mᵉ =
  prove-is-greatest-binary-lower-bound-Posetᵉ
    ( Fin-Posetᵉ kᵉ)
    ( ( leq-left-leq-min-Finᵉ kᵉ
        ( min-Finᵉ kᵉ lᵉ mᵉ)
        ( lᵉ)
        ( mᵉ)
        ( refl-leq-Finᵉ kᵉ (min-Finᵉ kᵉ lᵉ mᵉ))) ,ᵉ
      ( leq-right-leq-min-Finᵉ kᵉ
        ( min-Finᵉ kᵉ lᵉ mᵉ)
        ( lᵉ)
        ( mᵉ)
        ( refl-leq-Finᵉ kᵉ (min-Finᵉ kᵉ lᵉ mᵉ))))
    ( λ xᵉ (Hᵉ ,ᵉ Kᵉ) → leq-min-Finᵉ kᵉ xᵉ lᵉ mᵉ Hᵉ Kᵉ)
```