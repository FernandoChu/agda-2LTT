# Repeating an element in a standard finite type

```agda
module elementary-number-theory.repeating-element-standard-finite-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.unit-typeᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

```agda
repeat-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ kᵉ
repeat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (repeat-Finᵉ kᵉ xᵉ yᵉ)
repeat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ _) = inrᵉ starᵉ
repeat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inlᵉ yᵉ) = yᵉ
repeat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) (inrᵉ _) = inrᵉ starᵉ

abstract
  is-almost-injective-repeat-Finᵉ :
    (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) {yᵉ zᵉ : Finᵉ (succ-ℕᵉ kᵉ)} →
    inlᵉ xᵉ ≠ᵉ yᵉ → inlᵉ xᵉ ≠ᵉ zᵉ →
    repeat-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ repeat-Finᵉ kᵉ xᵉ zᵉ → yᵉ ＝ᵉ zᵉ
  is-almost-injective-repeat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inlᵉ yᵉ} {inlᵉ zᵉ} fᵉ gᵉ pᵉ =
    apᵉ
      ( inlᵉ)
      ( is-almost-injective-repeat-Finᵉ kᵉ xᵉ
        ( λ qᵉ → fᵉ (apᵉ inlᵉ qᵉ))
        ( λ qᵉ → gᵉ (apᵉ inlᵉ qᵉ))
        ( is-injective-inlᵉ pᵉ))
  is-almost-injective-repeat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inlᵉ yᵉ} {inrᵉ _} fᵉ gᵉ pᵉ =
    ex-falsoᵉ (Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ) pᵉ)
  is-almost-injective-repeat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inrᵉ _} {inlᵉ zᵉ} fᵉ gᵉ pᵉ =
    ex-falsoᵉ (Eq-Fin-eqᵉ (succ-ℕᵉ kᵉ) pᵉ)
  is-almost-injective-repeat-Finᵉ
    (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) {inrᵉ _} {inrᵉ _} fᵉ gᵉ pᵉ =
    reflᵉ
  is-almost-injective-repeat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) {inlᵉ yᵉ} {inlᵉ zᵉ} fᵉ gᵉ pᵉ =
    apᵉ inlᵉ pᵉ
  is-almost-injective-repeat-Finᵉ
    (succ-ℕᵉ kᵉ) (inrᵉ _) {inlᵉ yᵉ} {inrᵉ _} fᵉ gᵉ pᵉ =
    ex-falsoᵉ (fᵉ (apᵉ inlᵉ (invᵉ pᵉ)))
  is-almost-injective-repeat-Finᵉ
    (succ-ℕᵉ kᵉ) (inrᵉ _) {inrᵉ _} {inlᵉ zᵉ} fᵉ gᵉ pᵉ =
    ex-falsoᵉ (gᵉ (apᵉ inlᵉ pᵉ))
  is-almost-injective-repeat-Finᵉ
    (succ-ℕᵉ kᵉ) (inrᵉ _) {inrᵉ _} {inrᵉ _} fᵉ gᵉ pᵉ = reflᵉ
```