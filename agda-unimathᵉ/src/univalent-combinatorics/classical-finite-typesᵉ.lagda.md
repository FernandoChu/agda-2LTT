# The classical definition of the standard finite types

```agda
module univalent-combinatorics.classical-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Classically,ᵉ theᵉ standardᵉ typeᵉ with nᵉ elementsᵉ isᵉ definedᵉ to beᵉ `{0,1,...,n-1}`,ᵉ
i.e.,ᵉ itᵉ isᵉ theᵉ typeᵉ ofᵉ naturalᵉ numbersᵉ strictlyᵉ lessᵉ thanᵉ n.ᵉ

## Definitions

### The classical definition of the finite types

```agda
classical-Finᵉ : ℕᵉ → UUᵉ lzero
classical-Finᵉ kᵉ = Σᵉ ℕᵉ (λ xᵉ → le-ℕᵉ xᵉ kᵉ)
```

### The inclusion from `classical-Fin` to ℕ

```agda
nat-classical-Finᵉ : (kᵉ : ℕᵉ) → classical-Finᵉ kᵉ → ℕᵉ
nat-classical-Finᵉ kᵉ = pr1ᵉ
```

## Properties

### Characterization of equality

```agda
Eq-classical-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : classical-Finᵉ kᵉ) → UUᵉ lzero
Eq-classical-Finᵉ kᵉ xᵉ yᵉ = Idᵉ (nat-classical-Finᵉ kᵉ xᵉ) (nat-classical-Finᵉ kᵉ yᵉ)

eq-succ-classical-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : classical-Finᵉ kᵉ) → Idᵉ {Aᵉ = classical-Finᵉ kᵉ} xᵉ yᵉ →
  Idᵉ
    { Aᵉ = classical-Finᵉ (succ-ℕᵉ kᵉ)}
    ( pairᵉ (succ-ℕᵉ (pr1ᵉ xᵉ)) (pr2ᵉ xᵉ))
    ( pairᵉ (succ-ℕᵉ (pr1ᵉ yᵉ)) (pr2ᵉ yᵉ))
eq-succ-classical-Finᵉ kᵉ xᵉ .xᵉ reflᵉ = reflᵉ

eq-Eq-classical-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : classical-Finᵉ kᵉ) → Eq-classical-Finᵉ kᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
eq-Eq-classical-Finᵉ (succ-ℕᵉ kᵉ) (pairᵉ zero-ℕᵉ _) (pairᵉ zero-ℕᵉ _) eᵉ = reflᵉ
eq-Eq-classical-Finᵉ (succ-ℕᵉ kᵉ) (pairᵉ (succ-ℕᵉ xᵉ) pᵉ) (pairᵉ (succ-ℕᵉ yᵉ) qᵉ) eᵉ =
  eq-succ-classical-Finᵉ kᵉ
    ( pairᵉ xᵉ pᵉ)
    ( pairᵉ yᵉ qᵉ)
    ( eq-Eq-classical-Finᵉ kᵉ (pairᵉ xᵉ pᵉ) (pairᵉ yᵉ qᵉ) (is-injective-succ-ℕᵉ eᵉ))
```

### The classical finite types are equivalent to the standard finite types

#### We define maps back and forth between the standard finite sets and the bounded natural numbers

```agda
standard-classical-Finᵉ : (kᵉ : ℕᵉ) → classical-Finᵉ kᵉ → Finᵉ kᵉ
standard-classical-Finᵉ (succ-ℕᵉ kᵉ) (pairᵉ xᵉ Hᵉ) = mod-succ-ℕᵉ kᵉ xᵉ

classical-standard-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → classical-Finᵉ kᵉ
pr1ᵉ (classical-standard-Finᵉ kᵉ xᵉ) = nat-Finᵉ kᵉ xᵉ
pr2ᵉ (classical-standard-Finᵉ kᵉ xᵉ) = strict-upper-bound-nat-Finᵉ kᵉ xᵉ
```

#### We show that these maps are mutual inverses

```agda
is-section-classical-standard-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) →
  Idᵉ (standard-classical-Finᵉ kᵉ (classical-standard-Finᵉ kᵉ xᵉ)) xᵉ
is-section-classical-standard-Finᵉ {succ-ℕᵉ kᵉ} xᵉ = is-section-nat-Finᵉ kᵉ xᵉ

is-retraction-classical-standard-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : classical-Finᵉ kᵉ) →
  Idᵉ (classical-standard-Finᵉ kᵉ (standard-classical-Finᵉ kᵉ xᵉ)) xᵉ
is-retraction-classical-standard-Finᵉ {succ-ℕᵉ kᵉ} (pairᵉ xᵉ pᵉ) =
  eq-Eq-classical-Finᵉ (succ-ℕᵉ kᵉ)
    ( classical-standard-Finᵉ
      ( succ-ℕᵉ kᵉ)
      ( standard-classical-Finᵉ (succ-ℕᵉ kᵉ) (pairᵉ xᵉ pᵉ)))
    ( pairᵉ xᵉ pᵉ)
    ( eq-cong-le-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( xᵉ)
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( pᵉ)
      ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ))
```