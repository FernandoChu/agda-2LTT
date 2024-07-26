# Modular arithmetic on the standard finite types

```agda
module elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definitions

### The congruence class of a natural number modulo a successor

```agda
mod-succ-ℕᵉ : (kᵉ : ℕᵉ) → ℕᵉ → Finᵉ (succ-ℕᵉ kᵉ)
mod-succ-ℕᵉ kᵉ zero-ℕᵉ = zero-Finᵉ kᵉ
mod-succ-ℕᵉ kᵉ (succ-ℕᵉ nᵉ) = succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ nᵉ)

mod-two-ℕᵉ : ℕᵉ → Finᵉ 2
mod-two-ℕᵉ = mod-succ-ℕᵉ 1

mod-three-ℕᵉ : ℕᵉ → Finᵉ 3
mod-three-ℕᵉ = mod-succ-ℕᵉ 2
```

## Properties

### `nat-Fin k (succ-Fin k x)` and `succ-ℕ (nat-Fin k x)` are congruent modulo `k`

```agda
cong-nat-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) →
  cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ)) (succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ))
cong-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  cong-identification-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    { nat-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))}
    { succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ)}
    ( nat-succ-Finᵉ kᵉ xᵉ)
cong-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ _) =
  concatenate-eq-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    { nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)}
    { zero-ℕᵉ}
    { succ-ℕᵉ kᵉ}
    ( is-zero-nat-zero-Finᵉ {kᵉ})
    ( cong-zero-ℕ'ᵉ (succ-ℕᵉ kᵉ))

cong-nat-mod-succ-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)) xᵉ
cong-nat-mod-succ-ℕᵉ kᵉ zero-ℕᵉ = cong-is-zero-nat-zero-Finᵉ
cong-nat-mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ) =
  transitive-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))
    ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)))
    ( succ-ℕᵉ xᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ)
    ( cong-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
```

### If the congruence classes of `x` and `y` modulo `k + 1` are equal, then `x` and `y` are congruent modulo `k + 1`

```agda
cong-eq-mod-succ-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → mod-succ-ℕᵉ kᵉ xᵉ ＝ᵉ mod-succ-ℕᵉ kᵉ yᵉ → cong-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ
cong-eq-mod-succ-ℕᵉ kᵉ xᵉ yᵉ pᵉ =
  concatenate-cong-eq-cong-ℕᵉ {succ-ℕᵉ kᵉ} {xᵉ}
    ( symmetric-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)) xᵉ
      ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ))
    ( apᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ)) pᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ yᵉ)
```

### If `x` and `y` are congruent modulo `k + 1` then their congruence classes modulo `k + 1` are equal

```agda
eq-mod-succ-cong-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → cong-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ → mod-succ-ℕᵉ kᵉ xᵉ ＝ᵉ mod-succ-ℕᵉ kᵉ yᵉ
eq-mod-succ-cong-ℕᵉ kᵉ xᵉ yᵉ Hᵉ =
  eq-cong-nat-Finᵉ
    ( succ-ℕᵉ kᵉ)
    ( mod-succ-ℕᵉ kᵉ xᵉ)
    ( mod-succ-ℕᵉ kᵉ yᵉ)
    ( transitive-cong-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( xᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ))
      ( transitive-cong-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ))
        ( symmetric-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)) yᵉ
          ( cong-nat-mod-succ-ℕᵉ kᵉ yᵉ)) Hᵉ)
      ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ))
```

### `k + 1` divides `x` if and only if `x ≡ 0` modulo `k + 1`

```agda
is-zero-mod-succ-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → div-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ → is-zero-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)
is-zero-mod-succ-ℕᵉ kᵉ xᵉ dᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ xᵉ zero-ℕᵉ
    ( concatenate-div-eq-ℕᵉ dᵉ (invᵉ (right-unit-law-dist-ℕᵉ xᵉ)))

div-is-zero-mod-succ-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-zero-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ) → div-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ
div-is-zero-mod-succ-ℕᵉ kᵉ xᵉ pᵉ =
  concatenate-div-eq-ℕᵉ
    ( cong-eq-mod-succ-ℕᵉ kᵉ xᵉ zero-ℕᵉ pᵉ)
    ( right-unit-law-dist-ℕᵉ xᵉ)
```

### The inclusion of `Fin k` into `ℕ` is a section of `mod-succ-ℕ`

```agda
is-section-nat-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → mod-succ-ℕᵉ kᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) ＝ᵉ xᵉ
is-section-nat-Finᵉ kᵉ xᵉ =
  is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ)
    ( eq-cong-le-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( strict-upper-bound-nat-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( mod-succ-ℕᵉ kᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))
      ( strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( cong-nat-mod-succ-ℕᵉ kᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))
```

### `mod-succ-ℕ` is split surjective

```agda
is-split-surjective-mod-succ-ℕᵉ :
  (kᵉ : ℕᵉ) → is-split-surjectiveᵉ (mod-succ-ℕᵉ kᵉ)
pr1ᵉ (is-split-surjective-mod-succ-ℕᵉ kᵉ xᵉ) = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ
pr2ᵉ (is-split-surjective-mod-succ-ℕᵉ kᵉ xᵉ) = is-section-nat-Finᵉ kᵉ xᵉ
```

### `mod-succ-ℕ` is surjective

```agda
is-surjective-mod-succ-ℕᵉ :
  (kᵉ : ℕᵉ) → is-surjectiveᵉ (mod-succ-ℕᵉ kᵉ)
is-surjective-mod-succ-ℕᵉ kᵉ =
  is-surjective-is-split-surjectiveᵉ (is-split-surjective-mod-succ-ℕᵉ kᵉ)
```

### The residue of `x` modulo `k + 1` is less than or equal to `x`

```agda
leq-nat-mod-succ-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → leq-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)) xᵉ
leq-nat-mod-succ-ℕᵉ kᵉ zero-ℕᵉ =
  concatenate-eq-leq-ℕᵉ zero-ℕᵉ (is-zero-nat-zero-Finᵉ {kᵉ}) (refl-leq-ℕᵉ zero-ℕᵉ)
leq-nat-mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ) =
  transitive-leq-ℕᵉ
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))
    ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)))
    ( succ-ℕᵉ xᵉ)
    ( leq-nat-mod-succ-ℕᵉ kᵉ xᵉ)
    ( leq-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
```

## Operations

### Addition on the standard finite sets

```agda
add-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  mod-succ-ℕᵉ kᵉ ((nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))

add-Fin'ᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
add-Fin'ᵉ kᵉ xᵉ yᵉ = add-Finᵉ kᵉ yᵉ xᵉ

ap-add-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ x'ᵉ y'ᵉ : Finᵉ kᵉ} →
  xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → add-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ add-Finᵉ kᵉ x'ᵉ y'ᵉ
ap-add-Finᵉ kᵉ pᵉ qᵉ = ap-binaryᵉ (add-Finᵉ kᵉ) pᵉ qᵉ

cong-add-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ yᵉ : Finᵉ kᵉ) →
  cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ)) ((nat-Finᵉ kᵉ xᵉ) +ℕᵉ (nat-Finᵉ kᵉ yᵉ))
cong-add-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ =
  cong-nat-mod-succ-ℕᵉ kᵉ ((nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))

cong-add-ℕᵉ :
  {kᵉ : ℕᵉ} (xᵉ yᵉ : ℕᵉ) →
  cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)))
    ( xᵉ +ℕᵉ yᵉ)
cong-add-ℕᵉ {kᵉ} xᵉ yᵉ =
  transitive-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)))
    ( xᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)))
    ( xᵉ +ℕᵉ yᵉ)
    ( translation-invariant-cong-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ))
      ( yᵉ)
      ( xᵉ)
      ( cong-nat-mod-succ-ℕᵉ kᵉ yᵉ))
    ( translation-invariant-cong-ℕ'ᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( xᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ))
      ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ))

congruence-add-ℕᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ x'ᵉ y'ᵉ : ℕᵉ} →
  cong-ℕᵉ kᵉ xᵉ x'ᵉ → cong-ℕᵉ kᵉ yᵉ y'ᵉ → cong-ℕᵉ kᵉ (xᵉ +ℕᵉ yᵉ) (x'ᵉ +ℕᵉ y'ᵉ)
congruence-add-ℕᵉ kᵉ {xᵉ} {yᵉ} {x'ᵉ} {y'ᵉ} Hᵉ Kᵉ =
  transitive-cong-ℕᵉ kᵉ (xᵉ +ℕᵉ yᵉ) (xᵉ +ℕᵉ y'ᵉ) (x'ᵉ +ℕᵉ y'ᵉ)
    ( translation-invariant-cong-ℕ'ᵉ kᵉ xᵉ x'ᵉ y'ᵉ Hᵉ)
    ( translation-invariant-cong-ℕᵉ kᵉ yᵉ y'ᵉ xᵉ Kᵉ)

mod-succ-add-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) →
  mod-succ-ℕᵉ kᵉ (xᵉ +ℕᵉ yᵉ) ＝ᵉ
  add-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)
mod-succ-add-ℕᵉ kᵉ xᵉ yᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( xᵉ +ℕᵉ yᵉ)
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)))
    ( congruence-add-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      { xᵉ}
      { yᵉ}
      { nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)}
      { nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)}
      ( symmetric-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)) xᵉ
        ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ))
      ( symmetric-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ yᵉ)) yᵉ
        ( cong-nat-mod-succ-ℕᵉ kᵉ yᵉ)))
```

### Distance on the standard finite sets

```agda
dist-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
dist-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  mod-succ-ℕᵉ kᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))

dist-Fin'ᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
dist-Fin'ᵉ kᵉ xᵉ yᵉ = dist-Finᵉ kᵉ yᵉ xᵉ

ap-dist-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ x'ᵉ y'ᵉ : Finᵉ kᵉ} →
  xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → dist-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ dist-Finᵉ kᵉ x'ᵉ y'ᵉ
ap-dist-Finᵉ kᵉ pᵉ qᵉ = ap-binaryᵉ (dist-Finᵉ kᵉ) pᵉ qᵉ

cong-dist-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ yᵉ : Finᵉ kᵉ) →
  cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ (dist-Finᵉ kᵉ xᵉ yᵉ)) (dist-ℕᵉ (nat-Finᵉ kᵉ xᵉ) (nat-Finᵉ kᵉ yᵉ))
cong-dist-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ =
  cong-nat-mod-succ-ℕᵉ kᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
```

### The negative of an element of a standard finite set

```agda
neg-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ =
  mod-succ-ℕᵉ kᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (succ-ℕᵉ kᵉ))

cong-neg-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) →
  cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)) (dist-ℕᵉ (nat-Finᵉ kᵉ xᵉ) kᵉ)
cong-neg-Finᵉ {succ-ℕᵉ kᵉ} xᵉ =
  cong-nat-mod-succ-ℕᵉ kᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (succ-ℕᵉ kᵉ))
```

### Multiplication on the standard finite sets

```agda
mul-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  mod-succ-ℕᵉ kᵉ ((nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))

mul-Fin'ᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → Finᵉ kᵉ
mul-Fin'ᵉ kᵉ xᵉ yᵉ = mul-Finᵉ kᵉ yᵉ xᵉ

ap-mul-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ x'ᵉ y'ᵉ : Finᵉ kᵉ} →
  xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ mul-Finᵉ kᵉ x'ᵉ y'ᵉ
ap-mul-Finᵉ kᵉ pᵉ qᵉ = ap-binaryᵉ (mul-Finᵉ kᵉ) pᵉ qᵉ

cong-mul-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ yᵉ : Finᵉ kᵉ) →
  cong-ℕᵉ kᵉ (nat-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)) ((nat-Finᵉ kᵉ xᵉ) *ℕᵉ (nat-Finᵉ kᵉ yᵉ))
cong-mul-Finᵉ {succ-ℕᵉ kᵉ} xᵉ yᵉ =
  cong-nat-mod-succ-ℕᵉ kᵉ ((nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
```

## Laws

### Laws for addition

```agda
commutative-add-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → add-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ add-Finᵉ kᵉ yᵉ xᵉ
commutative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  apᵉ
    ( mod-succ-ℕᵉ kᵉ)
    ( commutative-add-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))

associative-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : Finᵉ kᵉ) →
  add-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Finᵉ kᵉ xᵉ (add-Finᵉ kᵉ yᵉ zᵉ)
associative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ zᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)))
    ( concatenate-cong-eq-cong-ℕᵉ
      { x1ᵉ =
        add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
      { x2ᵉ =
        add-ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
      { x3ᵉ =
        add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))}
      { x4ᵉ =
        add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ)
          ( add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ))}
      ( congruence-add-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)}
        { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ}
        { x'ᵉ = (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)}
        { y'ᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ}
        ( cong-add-Finᵉ xᵉ yᵉ)
        ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)))
      ( associative-add-ℕᵉ
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
      ( congruence-add-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
        { yᵉ = (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
        { x'ᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
        { y'ᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)}
        ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
        ( symmetric-cong-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ))
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
          ( cong-add-Finᵉ yᵉ zᵉ))))

right-unit-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ) ＝ᵉ xᵉ
right-unit-law-add-Finᵉ kᵉ xᵉ =
  ( eq-mod-succ-cong-ℕᵉ kᵉ
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)))
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) +ℕᵉ zero-ℕᵉ)
    ( congruence-add-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
      { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)}
      { x'ᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
      { y'ᵉ = zero-ℕᵉ}
      ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
      ( cong-is-zero-nat-zero-Finᵉ {kᵉ}))) ∙ᵉ
  ( is-section-nat-Finᵉ kᵉ xᵉ)

left-unit-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → add-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) xᵉ ＝ᵉ xᵉ
left-unit-law-add-Finᵉ kᵉ xᵉ =
  ( commutative-add-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) xᵉ) ∙ᵉ
  ( right-unit-law-add-Finᵉ kᵉ xᵉ)

left-inverse-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  is-zero-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ)
left-inverse-law-add-Finᵉ kᵉ xᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
    ( zero-ℕᵉ)
    ( concatenate-cong-eq-cong-ℕᵉ
      { succ-ℕᵉ kᵉ}
      { x1ᵉ =
        add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)}
      { x2ᵉ =
        (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (succ-ℕᵉ kᵉ)) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)}
      { x3ᵉ = succ-ℕᵉ kᵉ}
      { x4ᵉ = zero-ℕᵉ}
      ( translation-invariant-cong-ℕ'ᵉ (succ-ℕᵉ kᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
        ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (succ-ℕᵉ kᵉ))
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
        ( cong-neg-Finᵉ xᵉ))
      ( is-difference-dist-ℕ'ᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (succ-ℕᵉ kᵉ)
        ( upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ)))
      ( cong-zero-ℕ'ᵉ (succ-ℕᵉ kᵉ)))

right-inverse-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  is-zero-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
right-inverse-law-add-Finᵉ kᵉ xᵉ =
  ( commutative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) ∙ᵉ
  ( left-inverse-law-add-Finᵉ kᵉ xᵉ)
```

### The successor function on a standard finite set adds one

```agda
is-add-one-succ-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  succ-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ)
is-add-one-succ-Fin'ᵉ zero-ℕᵉ (inrᵉ _) = reflᵉ
is-add-one-succ-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( apᵉ (succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ))) (invᵉ (is-section-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))) ∙ᵉ
  ( apᵉ
    ( mod-succ-ℕᵉ (succ-ℕᵉ kᵉ))
    ( apᵉ
      ( (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ) +ℕᵉ_)
      ( invᵉ (is-one-nat-one-Finᵉ (succ-ℕᵉ kᵉ)))))

is-add-one-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  succ-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ add-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ) xᵉ
is-add-one-succ-Finᵉ kᵉ xᵉ =
  ( is-add-one-succ-Fin'ᵉ kᵉ xᵉ) ∙ᵉ
  ( commutative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ))
```

### Successor laws for addition on Fin k

```agda
right-successor-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  add-Finᵉ kᵉ xᵉ (succ-Finᵉ kᵉ yᵉ) ＝ᵉ succ-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ)
right-successor-law-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (is-add-one-succ-Fin'ᵉ kᵉ yᵉ)) ∙ᵉ
  ( ( invᵉ (associative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ (one-Finᵉ kᵉ))) ∙ᵉ
    ( invᵉ (is-add-one-succ-Fin'ᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))))

left-successor-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  add-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ) yᵉ ＝ᵉ succ-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ)
left-successor-law-add-Finᵉ kᵉ xᵉ yᵉ =
  commutative-add-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ) yᵉ ∙ᵉ
  ( ( right-successor-law-add-Finᵉ kᵉ yᵉ xᵉ) ∙ᵉ
    ( apᵉ (succ-Finᵉ kᵉ) (commutative-add-Finᵉ kᵉ yᵉ xᵉ)))
```

### Laws for multiplication on the standard finite types

```agda
associative-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ) zᵉ ＝ᵉ mul-Finᵉ kᵉ xᵉ (mul-Finᵉ kᵉ yᵉ zᵉ)
associative-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ zᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)) *ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
    ( ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)))
    ( concatenate-cong-eq-cong-ℕᵉ
      { x1ᵉ =
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)) *ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
      { x2ᵉ =
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)) *ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
      { x3ᵉ =
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))}
      { x4ᵉ =
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ))}
      ( congruence-mul-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)}
        { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ}
        ( cong-mul-Finᵉ xᵉ yᵉ)
        ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)))
      ( associative-mul-ℕᵉ
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
      ( symmetric-cong-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        ( ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)))
        ( ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)))
        ( congruence-mul-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
          { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)}
          ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
          ( cong-mul-Finᵉ yᵉ zᵉ))))

commutative-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → mul-Finᵉ kᵉ xᵉ yᵉ ＝ᵉ mul-Finᵉ kᵉ yᵉ xᵉ
commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
    ( cong-identification-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( commutative-mul-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)))

left-unit-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → mul-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ) xᵉ ＝ᵉ xᵉ
left-unit-law-mul-Finᵉ zero-ℕᵉ (inrᵉ _) = reflᵉ
left-unit-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( eq-mod-succ-cong-ℕᵉ (succ-ℕᵉ kᵉ)
    ( ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (one-Finᵉ (succ-ℕᵉ kᵉ))) *ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ))
    ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ)
    ( cong-identification-ℕᵉ
      ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
      ( ( apᵉ
          ( _*ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ))
          ( is-one-nat-one-Finᵉ kᵉ)) ∙ᵉ
        ( left-unit-law-mul-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ))))) ∙ᵉ
  ( is-section-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)

right-unit-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ) ＝ᵉ xᵉ
right-unit-law-mul-Finᵉ kᵉ xᵉ =
  ( commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ)) ∙ᵉ
  ( left-unit-law-mul-Finᵉ kᵉ xᵉ)

left-zero-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → mul-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) xᵉ ＝ᵉ zero-Finᵉ kᵉ
left-zero-law-mul-Finᵉ kᵉ xᵉ =
  ( eq-mod-succ-cong-ℕᵉ kᵉ
    ( (nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ))
    ( cong-identification-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      { (nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)}
      { nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)}
      ( ( apᵉ (_*ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) (is-zero-nat-zero-Finᵉ {kᵉ})) ∙ᵉ
        ( invᵉ (is-zero-nat-zero-Finᵉ {kᵉ}))))) ∙ᵉ
  ( is-section-nat-Finᵉ kᵉ (zero-Finᵉ kᵉ))

right-zero-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ) ＝ᵉ zero-Finᵉ kᵉ
right-zero-law-mul-Finᵉ kᵉ xᵉ =
  ( commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ)) ∙ᵉ
  ( left-zero-law-mul-Finᵉ kᵉ xᵉ)

left-distributive-mul-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ xᵉ (add-Finᵉ kᵉ yᵉ zᵉ) ＝ᵉ add-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ) (mul-Finᵉ kᵉ xᵉ zᵉ)
left-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ zᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)))
    ( add-ℕᵉ
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ zᵉ)))
    ( concatenate-cong-eq-cong-ℕᵉ
      { kᵉ = succ-ℕᵉ kᵉ}
      { x1ᵉ =
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ))}
      { x2ᵉ =
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))}
      { x3ᵉ =
        add-ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))}
      { x4ᵉ =
        add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ zᵉ))}
      ( congruence-mul-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
        { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ zᵉ)}
        { x'ᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ}
        { y'ᵉ = (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) +ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
        ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
        ( cong-add-Finᵉ yᵉ zᵉ))
      ( left-distributive-mul-add-ℕᵉ
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
        ( nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ))
      ( symmetric-cong-ℕᵉ (succ-ℕᵉ kᵉ)
        ( add-ℕᵉ
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
          ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ zᵉ)))
        ( add-ℕᵉ
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ))
          ( (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)))
        ( congruence-add-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          { xᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)}
          { yᵉ = nat-Finᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ zᵉ)}
          { x'ᵉ = (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)}
          { y'ᵉ = (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) zᵉ)}
          ( cong-mul-Finᵉ xᵉ yᵉ)
          ( cong-mul-Finᵉ xᵉ zᵉ))))

right-distributive-mul-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ zᵉ) (mul-Finᵉ kᵉ yᵉ zᵉ)
right-distributive-mul-add-Finᵉ kᵉ xᵉ yᵉ zᵉ =
  ( commutative-mul-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ) zᵉ) ∙ᵉ
  ( ( left-distributive-mul-add-Finᵉ kᵉ zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-add-Finᵉ kᵉ (commutative-mul-Finᵉ kᵉ zᵉ xᵉ) (commutative-mul-Finᵉ kᵉ zᵉ yᵉ)))
```

## Properties

### Addition on `Fin k` is a binary equivalence

```agda
add-add-neg-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → add-Finᵉ kᵉ xᵉ (add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) yᵉ) ＝ᵉ yᵉ
add-add-neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( invᵉ (associative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) yᵉ)) ∙ᵉ
  ( ( apᵉ (add-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (right-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
    ( left-unit-law-add-Finᵉ kᵉ yᵉ))

add-neg-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) (add-Finᵉ kᵉ xᵉ yᵉ) ＝ᵉ yᵉ
add-neg-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( invᵉ (associative-add-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ yᵉ)) ∙ᵉ
  ( ( apᵉ (add-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (left-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
    ( left-unit-law-add-Finᵉ kᵉ yᵉ))

is-equiv-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → is-equivᵉ (add-Finᵉ kᵉ xᵉ)
pr1ᵉ (pr1ᵉ (is-equiv-add-Finᵉ kᵉ xᵉ)) = add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
pr2ᵉ (pr1ᵉ (is-equiv-add-Finᵉ kᵉ xᵉ)) = add-add-neg-Finᵉ kᵉ xᵉ
pr1ᵉ (pr2ᵉ (is-equiv-add-Finᵉ kᵉ xᵉ)) = add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
pr2ᵉ (pr2ᵉ (is-equiv-add-Finᵉ kᵉ xᵉ)) = add-neg-add-Finᵉ kᵉ xᵉ

equiv-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → Finᵉ kᵉ ≃ᵉ Finᵉ kᵉ
pr1ᵉ (equiv-add-Finᵉ kᵉ xᵉ) = add-Finᵉ kᵉ xᵉ
pr2ᵉ (equiv-add-Finᵉ kᵉ xᵉ) = is-equiv-add-Finᵉ kᵉ xᵉ

add-add-neg-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → add-Fin'ᵉ kᵉ xᵉ (add-Fin'ᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) yᵉ) ＝ᵉ yᵉ
add-add-neg-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ) ∙ᵉ
  ( ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) (left-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
    ( right-unit-law-add-Finᵉ kᵉ yᵉ))

add-neg-add-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → add-Fin'ᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) (add-Fin'ᵉ kᵉ xᵉ yᵉ) ＝ᵉ yᵉ
add-neg-add-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ xᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) ∙ᵉ
  ( ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) (right-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
    ( right-unit-law-add-Finᵉ kᵉ yᵉ))

is-equiv-add-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → is-equivᵉ (add-Fin'ᵉ kᵉ xᵉ)
pr1ᵉ (pr1ᵉ (is-equiv-add-Fin'ᵉ kᵉ xᵉ)) = add-Fin'ᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
pr2ᵉ (pr1ᵉ (is-equiv-add-Fin'ᵉ kᵉ xᵉ)) = add-add-neg-Fin'ᵉ kᵉ xᵉ
pr1ᵉ (pr2ᵉ (is-equiv-add-Fin'ᵉ kᵉ xᵉ)) = add-Fin'ᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
pr2ᵉ (pr2ᵉ (is-equiv-add-Fin'ᵉ kᵉ xᵉ)) = add-neg-add-Fin'ᵉ kᵉ xᵉ

equiv-add-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → Finᵉ kᵉ ≃ᵉ Finᵉ kᵉ
pr1ᵉ (equiv-add-Fin'ᵉ kᵉ xᵉ) = add-Fin'ᵉ kᵉ xᵉ
pr2ᵉ (equiv-add-Fin'ᵉ kᵉ xᵉ) = is-equiv-add-Fin'ᵉ kᵉ xᵉ

is-injective-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → is-injectiveᵉ (add-Finᵉ kᵉ xᵉ)
is-injective-add-Finᵉ kᵉ xᵉ {yᵉ} {zᵉ} pᵉ =
  ( invᵉ (add-neg-add-Finᵉ kᵉ xᵉ yᵉ)) ∙ᵉ
  ( ( apᵉ (add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)) pᵉ) ∙ᵉ
    ( add-neg-add-Finᵉ kᵉ xᵉ zᵉ))

is-injective-add-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → is-injectiveᵉ (add-Fin'ᵉ kᵉ xᵉ)
is-injective-add-Fin'ᵉ kᵉ xᵉ {yᵉ} {zᵉ} pᵉ =
  is-injective-add-Finᵉ kᵉ xᵉ
    ( commutative-add-Finᵉ kᵉ xᵉ yᵉ ∙ᵉ (pᵉ ∙ᵉ commutative-add-Finᵉ kᵉ zᵉ xᵉ))
```

### `neg-Fin` multiplies by `-1`

```agda
mul-neg-one-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ ＝ᵉ neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ
mul-neg-one-Finᵉ {kᵉ} xᵉ =
  is-injective-add-Finᵉ
    ( succ-ℕᵉ kᵉ)
    ( xᵉ)
    ( ( ( apᵉ
          ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ))
          ( invᵉ (left-unit-law-mul-Finᵉ kᵉ xᵉ))) ∙ᵉ
        ( ( invᵉ
            ( right-distributive-mul-add-Finᵉ
              ( succ-ℕᵉ kᵉ)
              ( one-Finᵉ kᵉ)
              ( neg-one-Finᵉ kᵉ)
              ( xᵉ))) ∙ᵉ
          ( ( apᵉ
              ( mul-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ)
              ( invᵉ (is-add-one-succ-Finᵉ kᵉ (neg-one-Finᵉ kᵉ)))) ∙ᵉ
            ( left-zero-law-mul-Finᵉ kᵉ xᵉ)))) ∙ᵉ
      ( invᵉ (right-inverse-law-add-Finᵉ kᵉ xᵉ)))
```

### The negative of `-1` is `1`

```agda
is-one-neg-neg-one-Finᵉ :
  (kᵉ : ℕᵉ) → is-one-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ))
is-one-neg-neg-one-Finᵉ kᵉ =
  eq-mod-succ-cong-ℕᵉ kᵉ
    ( dist-ℕᵉ kᵉ (succ-ℕᵉ kᵉ))
    ( 1ᵉ)
    ( cong-identification-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( is-one-dist-succ-ℕᵉ kᵉ))
```

### The negative of `1` is `-1`

```agda
is-neg-one-neg-one-Finᵉ :
  (kᵉ : ℕᵉ) → neg-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ) ＝ᵉ (neg-one-Finᵉ kᵉ)
is-neg-one-neg-one-Finᵉ kᵉ =
  is-injective-add-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ)
    ( ( right-inverse-law-add-Finᵉ kᵉ (one-Finᵉ kᵉ)) ∙ᵉ
      ( ( invᵉ (left-inverse-law-add-Finᵉ kᵉ (neg-one-Finᵉ kᵉ))) ∙ᵉ
        ( apᵉ (add-Fin'ᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ)) (is-one-neg-neg-one-Finᵉ kᵉ))))
```

### The predecessor function adds `-1`

```agda
is-add-neg-one-pred-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ)
is-add-neg-one-pred-Fin'ᵉ kᵉ xᵉ =
  is-injective-succ-Finᵉ
    ( succ-ℕᵉ kᵉ)
    ( ( is-section-pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) ∙ᵉ
      ( ( ( ( invᵉ (right-unit-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
            ( apᵉ
              ( add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
              ( invᵉ
                ( ( apᵉ
                    ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ))
                    ( invᵉ (is-neg-one-neg-one-Finᵉ kᵉ))) ∙ᵉ
                  ( left-inverse-law-add-Finᵉ kᵉ (one-Finᵉ kᵉ)))))) ∙ᵉ
          ( invᵉ
            ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ) (one-Finᵉ kᵉ)))) ∙ᵉ
        ( invᵉ (is-add-one-succ-Fin'ᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ))))))

is-add-neg-one-pred-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ add-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ
is-add-neg-one-pred-Finᵉ kᵉ xᵉ =
  ( is-add-neg-one-pred-Fin'ᵉ kᵉ xᵉ) ∙ᵉ
  ( commutative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ))
```

### `neg-Fin` multiplies by `-1`

```agda
is-mul-neg-one-neg-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ
is-mul-neg-one-neg-Finᵉ kᵉ xᵉ =
  is-injective-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ
    ( ( right-inverse-law-add-Finᵉ kᵉ xᵉ) ∙ᵉ
      ( ( ( ( invᵉ (left-zero-law-mul-Finᵉ kᵉ xᵉ)) ∙ᵉ
            ( apᵉ
              ( mul-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ)
              ( invᵉ
                ( ( apᵉ
                  ( add-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ))
                  ( invᵉ (is-neg-one-neg-one-Finᵉ kᵉ))) ∙ᵉ
                  ( right-inverse-law-add-Finᵉ kᵉ (one-Finᵉ kᵉ)))))) ∙ᵉ
          ( right-distributive-mul-add-Finᵉ
            ( succ-ℕᵉ kᵉ)
            ( one-Finᵉ kᵉ)
            ( neg-one-Finᵉ kᵉ)
            ( xᵉ))) ∙ᵉ
        ( apᵉ
          ( add-Fin'ᵉ
            ( succ-ℕᵉ kᵉ)
            ( mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ))
          ( left-unit-law-mul-Finᵉ kᵉ xᵉ))))

is-mul-neg-one-neg-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ ＝ᵉ mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ)
is-mul-neg-one-neg-Fin'ᵉ kᵉ xᵉ =
  is-mul-neg-one-neg-Finᵉ kᵉ xᵉ ∙ᵉ commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ
```

### The negative of `0` is `0`

```agda
neg-zero-Finᵉ : (kᵉ : ℕᵉ) → neg-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) ＝ᵉ zero-Finᵉ kᵉ
neg-zero-Finᵉ kᵉ =
  ( invᵉ (left-unit-law-add-Finᵉ kᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)))) ∙ᵉ
  ( right-inverse-law-add-Finᵉ kᵉ (zero-Finᵉ kᵉ))
```

### The negative of a successor is the predecessor of the negative

```agda
neg-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → neg-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ) ＝ᵉ pred-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
neg-succ-Finᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( apᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ)) (is-add-one-succ-Fin'ᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( is-mul-neg-one-neg-Finᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ))) ∙ᵉ
    ( ( left-distributive-mul-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( neg-one-Finᵉ kᵉ)
        ( xᵉ)
        ( one-Finᵉ kᵉ)) ∙ᵉ
      ( ( ap-add-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ xᵉ))
          ( ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ (one-Finᵉ kᵉ))) ∙ᵉ
            ( is-neg-one-neg-one-Finᵉ kᵉ))) ∙ᵉ
        ( invᵉ (is-add-neg-one-pred-Fin'ᵉ kᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))))))
```

### The negative of a predecessor is the successor of a negative

```agda
neg-pred-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → neg-Finᵉ kᵉ (pred-Finᵉ kᵉ xᵉ) ＝ᵉ succ-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
neg-pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( apᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ)) (is-add-neg-one-pred-Fin'ᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( is-mul-neg-one-neg-Finᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ))) ∙ᵉ
    ( ( left-distributive-mul-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( neg-one-Finᵉ kᵉ)
        ( xᵉ)
        ( neg-one-Finᵉ kᵉ)) ∙ᵉ
      ( ( ap-add-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ xᵉ))
          ( ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ (neg-one-Finᵉ kᵉ))) ∙ᵉ
            ( is-one-neg-neg-one-Finᵉ kᵉ))) ∙ᵉ
        ( invᵉ (is-add-one-succ-Fin'ᵉ kᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))))))
```

### Taking negatives distributes over addition

```agda
distributive-neg-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  neg-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ) ＝ᵉ add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) (neg-Finᵉ kᵉ yᵉ)
distributive-neg-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( is-mul-neg-one-neg-Finᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)) ∙ᵉ
  ( ( left-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ yᵉ) ∙ᵉ
    ( invᵉ
      ( ap-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( is-mul-neg-one-neg-Finᵉ kᵉ xᵉ)
        ( is-mul-neg-one-neg-Finᵉ kᵉ yᵉ))))
```

### Predecessor laws of addition

```agda
left-predecessor-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  add-Finᵉ kᵉ (pred-Finᵉ kᵉ xᵉ) yᵉ ＝ᵉ pred-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ)
left-predecessor-law-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (add-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (is-add-neg-one-pred-Finᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ yᵉ) ∙ᵉ
    ( invᵉ (is-add-neg-one-pred-Finᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))))

right-predecessor-law-add-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  add-Finᵉ kᵉ xᵉ (pred-Finᵉ kᵉ yᵉ) ＝ᵉ pred-Finᵉ kᵉ (add-Finᵉ kᵉ xᵉ yᵉ)
right-predecessor-law-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (is-add-neg-one-pred-Fin'ᵉ kᵉ yᵉ)) ∙ᵉ
  ( ( invᵉ (associative-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ (neg-one-Finᵉ kᵉ))) ∙ᵉ
    ( invᵉ (is-add-neg-one-pred-Fin'ᵉ kᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))))
```

### Negative laws of multiplication

```agda
left-negative-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) yᵉ ＝ᵉ neg-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)
left-negative-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (mul-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (is-mul-neg-one-neg-Finᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( associative-mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ yᵉ) ∙ᵉ
    ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))))

right-negative-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ xᵉ (neg-Finᵉ kᵉ yᵉ) ＝ᵉ neg-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)
right-negative-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)) ∙ᵉ
  ( ( left-negative-law-mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ xᵉ) ∙ᵉ
    ( apᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ)) (commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) yᵉ xᵉ)))
```

### Successor laws of multiplication

```agda
left-successor-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ) yᵉ ＝ᵉ add-Finᵉ kᵉ yᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)
left-successor-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (mul-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (is-add-one-succ-Finᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( right-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ) xᵉ yᵉ) ∙ᵉ
    ( apᵉ
      ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( left-unit-law-mul-Finᵉ kᵉ yᵉ)))

right-successor-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ xᵉ (succ-Finᵉ kᵉ yᵉ) ＝ᵉ add-Finᵉ kᵉ xᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)
right-successor-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (is-add-one-succ-Finᵉ kᵉ yᵉ)) ∙ᵉ
  ( ( left-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ) yᵉ) ∙ᵉ
    ( apᵉ
      ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( right-unit-law-mul-Finᵉ kᵉ xᵉ)))
```

### Predecessor laws of multiplication

```agda
left-predecessor-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ (pred-Finᵉ kᵉ xᵉ) yᵉ ＝ᵉ add-Finᵉ kᵉ (neg-Finᵉ kᵉ yᵉ) (mul-Finᵉ kᵉ xᵉ yᵉ)
left-predecessor-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (mul-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) (is-add-neg-one-pred-Finᵉ kᵉ xᵉ)) ∙ᵉ
  ( ( right-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) xᵉ yᵉ) ∙ᵉ
    ( apᵉ
      ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( invᵉ (is-mul-neg-one-neg-Finᵉ kᵉ yᵉ))))

right-predecessor-law-mul-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) →
  mul-Finᵉ kᵉ xᵉ (pred-Finᵉ kᵉ yᵉ) ＝ᵉ add-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) (mul-Finᵉ kᵉ xᵉ yᵉ)
right-predecessor-law-mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ =
  ( apᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) (is-add-neg-one-pred-Finᵉ kᵉ yᵉ)) ∙ᵉ
  ( ( left-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ) yᵉ) ∙ᵉ
    ( apᵉ
      ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ))
      ( invᵉ (is-mul-neg-one-neg-Fin'ᵉ kᵉ xᵉ))))
```

### Taking negatives is an involution

```agda
neg-neg-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → neg-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ) ＝ᵉ xᵉ
neg-neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ =
  ( invᵉ
    ( right-unit-law-add-Finᵉ kᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))) ∙ᵉ
  ( ( apᵉ
      ( add-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)))
      ( invᵉ (left-inverse-law-add-Finᵉ kᵉ xᵉ))) ∙ᵉ
    ( ( invᵉ
        ( associative-add-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( neg-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
          ( neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
          ( xᵉ))) ∙ᵉ
      ( ( apᵉ
          ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ)
          ( left-inverse-law-add-Finᵉ kᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))) ∙ᵉ
        ( left-unit-law-add-Finᵉ kᵉ xᵉ))))

is-equiv-neg-Finᵉ :
  (kᵉ : ℕᵉ) → is-equivᵉ (neg-Finᵉ kᵉ)
pr1ᵉ (pr1ᵉ (is-equiv-neg-Finᵉ kᵉ)) = neg-Finᵉ kᵉ
pr2ᵉ (pr1ᵉ (is-equiv-neg-Finᵉ kᵉ)) = neg-neg-Finᵉ kᵉ
pr1ᵉ (pr2ᵉ (is-equiv-neg-Finᵉ kᵉ)) = neg-Finᵉ kᵉ
pr2ᵉ (pr2ᵉ (is-equiv-neg-Finᵉ kᵉ)) = neg-neg-Finᵉ kᵉ

equiv-neg-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ ≃ᵉ Finᵉ kᵉ
pr1ᵉ (equiv-neg-Finᵉ kᵉ) = neg-Finᵉ kᵉ
pr2ᵉ (equiv-neg-Finᵉ kᵉ) = is-equiv-neg-Finᵉ kᵉ
```

## Properties

### Divisibility is a decidable relation on `ℕ`

```agda
is-decidable-div-ℕᵉ : (dᵉ xᵉ : ℕᵉ) → is-decidableᵉ (div-ℕᵉ dᵉ xᵉ)
is-decidable-div-ℕᵉ zero-ℕᵉ xᵉ =
  is-decidable-iffᵉ
    ( div-eq-ℕᵉ zero-ℕᵉ xᵉ)
    ( invᵉ ∘ᵉ (is-zero-div-zero-ℕᵉ xᵉ))
    ( is-decidable-is-zero-ℕ'ᵉ xᵉ)
is-decidable-div-ℕᵉ (succ-ℕᵉ dᵉ) xᵉ =
  is-decidable-iffᵉ
    ( div-is-zero-mod-succ-ℕᵉ dᵉ xᵉ)
    ( is-zero-mod-succ-ℕᵉ dᵉ xᵉ)
    ( is-decidable-is-zero-Finᵉ (mod-succ-ℕᵉ dᵉ xᵉ))

div-ℕ-Decidable-Propᵉ : (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ dᵉ → Decidable-Propᵉ lzero
pr1ᵉ (div-ℕ-Decidable-Propᵉ dᵉ xᵉ Hᵉ) = div-ℕᵉ dᵉ xᵉ
pr1ᵉ (pr2ᵉ (div-ℕ-Decidable-Propᵉ dᵉ xᵉ Hᵉ)) = is-prop-div-ℕᵉ dᵉ xᵉ Hᵉ
pr2ᵉ (pr2ᵉ (div-ℕ-Decidable-Propᵉ dᵉ xᵉ Hᵉ)) = is-decidable-div-ℕᵉ dᵉ xᵉ
```