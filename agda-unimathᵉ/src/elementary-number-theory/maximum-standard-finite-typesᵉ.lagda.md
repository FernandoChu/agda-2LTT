# Maximum on the standard finite types

```agda
module elementary-number-theory.maximum-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.unit-typeᵉ

open import order-theory.least-upper-bounds-posetsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ theᵉ operationᵉ ofᵉ maximumᵉ (leastᵉ upperᵉ boundᵉ) forᵉ theᵉ standardᵉ finiteᵉ
types.ᵉ

## Definition

```agda
max-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (max-Finᵉ kᵉ xᵉ yᵉ)
max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ _) = inrᵉ starᵉ
max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inlᵉ xᵉ) = inrᵉ starᵉ
max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inrᵉ _) = inrᵉ starᵉ

max-Fin-Finᵉ : (nᵉ kᵉ : ℕᵉ) → (Finᵉ (succ-ℕᵉ nᵉ) → Finᵉ kᵉ) → Finᵉ kᵉ
max-Fin-Finᵉ zero-ℕᵉ kᵉ fᵉ =
  fᵉ (inrᵉ starᵉ)
max-Fin-Finᵉ (succ-ℕᵉ nᵉ) kᵉ fᵉ =
  max-Finᵉ kᵉ (fᵉ (inrᵉ starᵉ)) (max-Fin-Finᵉ nᵉ kᵉ (λ kᵉ → fᵉ (inlᵉ kᵉ)))
```

## Properties

### Maximum is greatest lower bound

```agda
leq-max-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) →
  leq-Finᵉ kᵉ mᵉ lᵉ → leq-Finᵉ kᵉ nᵉ lᵉ → leq-Finᵉ kᵉ (max-Finᵉ kᵉ mᵉ nᵉ) lᵉ
leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ qᵉ = leq-max-Finᵉ kᵉ xᵉ yᵉ zᵉ pᵉ qᵉ
leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ qᵉ = starᵉ
leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) pᵉ qᵉ = starᵉ
leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) pᵉ qᵉ = starᵉ
leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ qᵉ = starᵉ

leq-left-leq-max-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ (max-Finᵉ kᵉ mᵉ nᵉ) lᵉ → leq-Finᵉ kᵉ mᵉ lᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ =
  leq-left-leq-max-Finᵉ kᵉ xᵉ yᵉ zᵉ pᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ = starᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) pᵉ = starᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) pᵉ = starᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ = starᵉ
leq-left-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ = pᵉ

leq-right-leq-max-Finᵉ :
  (kᵉ : ℕᵉ) (lᵉ mᵉ nᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ (max-Finᵉ kᵉ mᵉ nᵉ) lᵉ → leq-Finᵉ kᵉ nᵉ lᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ =
  leq-right-leq-max-Finᵉ kᵉ xᵉ yᵉ zᵉ pᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) pᵉ = starᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) pᵉ = starᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inlᵉ zᵉ) pᵉ = starᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) (inrᵉ zᵉ) pᵉ = starᵉ
leq-right-leq-max-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ zᵉ) pᵉ = pᵉ

is-least-upper-bound-max-Finᵉ :
  (kᵉ : ℕᵉ) (mᵉ nᵉ : Finᵉ kᵉ) →
  is-least-binary-upper-bound-Posetᵉ (Fin-Posetᵉ kᵉ) mᵉ nᵉ (max-Finᵉ kᵉ mᵉ nᵉ)
is-least-upper-bound-max-Finᵉ kᵉ mᵉ nᵉ =
  prove-is-least-binary-upper-bound-Posetᵉ
    ( Fin-Posetᵉ kᵉ)
    ( ( leq-left-leq-max-Finᵉ kᵉ
        ( max-Finᵉ kᵉ mᵉ nᵉ)
        ( mᵉ)
        ( nᵉ)
        ( refl-leq-Finᵉ kᵉ (max-Finᵉ kᵉ mᵉ nᵉ))) ,ᵉ
      ( leq-right-leq-max-Finᵉ kᵉ
        ( max-Finᵉ kᵉ mᵉ nᵉ)
        ( mᵉ)
        ( nᵉ)
        ( refl-leq-Finᵉ kᵉ (max-Finᵉ kᵉ mᵉ nᵉ))))
    ( λ xᵉ (Hᵉ ,ᵉ Kᵉ) → leq-max-Finᵉ kᵉ xᵉ mᵉ nᵉ Hᵉ Kᵉ)
```