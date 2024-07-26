# Inequality on the standard finite types

```agda
module elementary-number-theory.inequality-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definitions

```agda
leq-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → UUᵉ lzero
leq-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (inrᵉ yᵉ) = unitᵉ
leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = leq-Finᵉ kᵉ xᵉ yᵉ
leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) = emptyᵉ

abstract
  is-prop-leq-Finᵉ :
    (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → is-propᵉ (leq-Finᵉ kᵉ xᵉ yᵉ)
  is-prop-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = is-prop-leq-Finᵉ kᵉ xᵉ yᵉ
  is-prop-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ starᵉ) = is-prop-unitᵉ
  is-prop-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) (inlᵉ yᵉ) = is-prop-emptyᵉ
  is-prop-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) = is-prop-unitᵉ

leq-Fin-Propᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Propᵉ lzero
pr1ᵉ (leq-Fin-Propᵉ kᵉ xᵉ yᵉ) = leq-Finᵉ kᵉ xᵉ yᵉ
pr2ᵉ (leq-Fin-Propᵉ kᵉ xᵉ yᵉ) = is-prop-leq-Finᵉ kᵉ xᵉ yᵉ

leq-neg-one-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → leq-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ)
leq-neg-one-Finᵉ kᵉ xᵉ = starᵉ

refl-leq-Finᵉ : (kᵉ : ℕᵉ) → is-reflexiveᵉ (leq-Finᵉ kᵉ)
refl-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = refl-leq-Finᵉ kᵉ xᵉ
refl-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = starᵉ

antisymmetric-leq-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ xᵉ yᵉ → leq-Finᵉ kᵉ yᵉ xᵉ → xᵉ ＝ᵉ yᵉ
antisymmetric-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) Hᵉ Kᵉ =
  apᵉ inlᵉ (antisymmetric-leq-Finᵉ kᵉ xᵉ yᵉ Hᵉ Kᵉ)
antisymmetric-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) Hᵉ Kᵉ = reflᵉ

transitive-leq-Finᵉ :
  (kᵉ : ℕᵉ) → is-transitiveᵉ (leq-Finᵉ kᵉ)
transitive-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inlᵉ zᵉ) Hᵉ Kᵉ =
  transitive-leq-Finᵉ kᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ
transitive-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) (inrᵉ starᵉ) Hᵉ Kᵉ = starᵉ
transitive-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) Hᵉ Kᵉ = starᵉ
transitive-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) (inrᵉ starᵉ) Hᵉ Kᵉ = starᵉ

concatenate-eq-leq-eq-Finᵉ :
  (kᵉ : ℕᵉ) {x1ᵉ x2ᵉ x3ᵉ x4ᵉ : Finᵉ kᵉ} →
  x1ᵉ ＝ᵉ x2ᵉ → leq-Finᵉ kᵉ x2ᵉ x3ᵉ → x3ᵉ ＝ᵉ x4ᵉ → leq-Finᵉ kᵉ x1ᵉ x4ᵉ
concatenate-eq-leq-eq-Finᵉ kᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

leq-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) →
  leq-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ xᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ xᵉ))
leq-succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = leq-succ-Finᵉ kᵉ xᵉ
leq-succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = starᵉ

preserves-leq-nat-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ : Finᵉ kᵉ} → leq-Finᵉ kᵉ xᵉ yᵉ → leq-ℕᵉ (nat-Finᵉ kᵉ xᵉ) (nat-Finᵉ kᵉ yᵉ)
preserves-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} Hᵉ =
  preserves-leq-nat-Finᵉ kᵉ Hᵉ
preserves-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inrᵉ starᵉ} Hᵉ =
  leq-le-ℕᵉ (nat-Finᵉ kᵉ xᵉ) kᵉ (strict-upper-bound-nat-Finᵉ kᵉ xᵉ)
preserves-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} Hᵉ =
  refl-leq-ℕᵉ kᵉ

reflects-leq-nat-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ : Finᵉ kᵉ} → leq-ℕᵉ (nat-Finᵉ kᵉ xᵉ) (nat-Finᵉ kᵉ yᵉ) → leq-Finᵉ kᵉ xᵉ yᵉ
reflects-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} Hᵉ =
  reflects-leq-nat-Finᵉ kᵉ Hᵉ
reflects-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inlᵉ yᵉ} Hᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ (nat-Finᵉ kᵉ yᵉ) kᵉ (strict-upper-bound-nat-Finᵉ kᵉ yᵉ) Hᵉ)
reflects-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inrᵉ starᵉ} Hᵉ = starᵉ
reflects-leq-nat-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} Hᵉ = starᵉ
```

### The partial order on the standard finite types

```agda
Fin-Preorderᵉ : ℕᵉ → Preorderᵉ lzero lzero
pr1ᵉ (Fin-Preorderᵉ kᵉ) = Finᵉ kᵉ
pr1ᵉ (pr2ᵉ (Fin-Preorderᵉ kᵉ)) = leq-Fin-Propᵉ kᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (Fin-Preorderᵉ kᵉ))) = refl-leq-Finᵉ kᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (Fin-Preorderᵉ kᵉ))) = transitive-leq-Finᵉ kᵉ

Fin-Posetᵉ : ℕᵉ → Posetᵉ lzero lzero
pr1ᵉ (Fin-Posetᵉ kᵉ) = Fin-Preorderᵉ kᵉ
pr2ᵉ (Fin-Posetᵉ kᵉ) = antisymmetric-leq-Finᵉ kᵉ
```

## Properties

### Ordering on the standard finite types is decidable

```agda
is-decidable-leq-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → is-decidableᵉ (leq-Finᵉ kᵉ xᵉ yᵉ)
is-decidable-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = is-decidable-leq-Finᵉ kᵉ xᵉ yᵉ
is-decidable-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = inlᵉ starᵉ
is-decidable-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) = inrᵉ (λ xᵉ → xᵉ)
is-decidable-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) = inlᵉ starᵉ

leq-Fin-Decidable-Propᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Decidable-Propᵉ lzero
pr1ᵉ (leq-Fin-Decidable-Propᵉ kᵉ xᵉ yᵉ) = leq-Finᵉ kᵉ xᵉ yᵉ
pr1ᵉ (pr2ᵉ (leq-Fin-Decidable-Propᵉ kᵉ xᵉ yᵉ)) = is-prop-leq-Finᵉ kᵉ xᵉ yᵉ
pr2ᵉ (pr2ᵉ (leq-Fin-Decidable-Propᵉ kᵉ xᵉ yᵉ)) = is-decidable-leq-Finᵉ kᵉ xᵉ yᵉ
```

### Ordering on the standard finite types is linear

```agda
linear-leq-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → leq-Finᵉ kᵉ xᵉ yᵉ +ᵉ leq-Finᵉ kᵉ yᵉ xᵉ
linear-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = linear-leq-Finᵉ kᵉ xᵉ yᵉ
linear-leq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = inlᵉ starᵉ
linear-leq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) yᵉ = inrᵉ starᵉ
```