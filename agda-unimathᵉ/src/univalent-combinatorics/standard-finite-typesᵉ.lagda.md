# The standard finite types

```agda
module univalent-combinatorics.standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.equivalence-injective-type-familiesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-maybeᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.noncontractible-typesᵉ
open import foundation.preunivalent-type-familiesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Theᵉ standardᵉ finiteᵉ typesᵉ areᵉ definedᵉ inductivelyᵉ byᵉ `Finᵉ 0 :=ᵉ empty`ᵉ andᵉ
`Finᵉ (n+1ᵉ) :=ᵉ (Finᵉ nᵉ) +ᵉ 1`.ᵉ **Note**ᵉ thatᵉ theᵉ outermostᵉ coproductᵉ (i.e.ᵉ theᵉ
`inr`ᵉ injectionᵉ) isᵉ theᵉ _topᵉ_ element,ᵉ whenᵉ `Finᵉ n`ᵉ isᵉ consideredᵉ asᵉ anᵉ initialᵉ
segmentᵉ ofᵉ `ℕ`.ᵉ

## Definition

### The standard finite types in universe level zero

```agda
Fin-Setᵉ : ℕᵉ → Setᵉ lzero
Fin-Setᵉ zero-ℕᵉ = empty-Setᵉ
Fin-Setᵉ (succ-ℕᵉ nᵉ) = coproduct-Setᵉ (Fin-Setᵉ nᵉ) unit-Setᵉ

Finᵉ : ℕᵉ → UUᵉ lzero
Finᵉ nᵉ = type-Setᵉ (Fin-Setᵉ nᵉ)

is-set-Finᵉ : (nᵉ : ℕᵉ) → is-setᵉ (Finᵉ nᵉ)
is-set-Finᵉ nᵉ = is-set-type-Setᵉ (Fin-Setᵉ nᵉ)

inl-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ (succ-ℕᵉ kᵉ)
inl-Finᵉ kᵉ = inlᵉ

emb-inl-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ ↪ᵉ Finᵉ (succ-ℕᵉ kᵉ)
pr1ᵉ (emb-inl-Finᵉ kᵉ) = inl-Finᵉ kᵉ
pr2ᵉ (emb-inl-Finᵉ kᵉ) = is-emb-inlᵉ (Finᵉ kᵉ) unitᵉ

neg-one-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ)
neg-one-Finᵉ kᵉ = inrᵉ starᵉ

is-neg-one-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-neg-one-Finᵉ (succ-ℕᵉ kᵉ) xᵉ = xᵉ ＝ᵉ neg-one-Finᵉ kᵉ

neg-two-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ)
neg-two-Finᵉ zero-ℕᵉ = inrᵉ starᵉ
neg-two-Finᵉ (succ-ℕᵉ kᵉ) = inlᵉ (inrᵉ starᵉ)

is-inl-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ) → UUᵉ lzero
is-inl-Finᵉ kᵉ xᵉ = Σᵉ (Finᵉ kᵉ) (λ yᵉ → inlᵉ yᵉ ＝ᵉ xᵉ)

is-neg-one-is-not-inl-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  ¬ᵉ (is-inl-Finᵉ kᵉ xᵉ) → is-neg-one-Finᵉ (succ-ℕᵉ kᵉ) xᵉ
is-neg-one-is-not-inl-Finᵉ kᵉ (inlᵉ xᵉ) Hᵉ = ex-falsoᵉ (Hᵉ (xᵉ ,ᵉ reflᵉ))
is-neg-one-is-not-inl-Finᵉ kᵉ (inrᵉ starᵉ) Hᵉ = reflᵉ

inr-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ (succ-ℕᵉ kᵉ)
inr-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = inlᵉ (inr-Finᵉ kᵉ xᵉ)
inr-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = inrᵉ starᵉ

neq-inl-Fin-inr-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ : Finᵉ nᵉ) → inl-Finᵉ nᵉ kᵉ ≠ᵉ inr-Finᵉ nᵉ kᵉ
neq-inl-Fin-inr-Finᵉ (succ-ℕᵉ nᵉ) (inlᵉ kᵉ) =
  neq-inl-Fin-inr-Finᵉ nᵉ kᵉ ∘ᵉ is-injective-inlᵉ
neq-inl-Fin-inr-Finᵉ (succ-ℕᵉ nᵉ) (inrᵉ starᵉ) = neq-inl-inrᵉ

neq-inr-Fin-inl-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ : Finᵉ nᵉ) → inr-Finᵉ nᵉ kᵉ ≠ᵉ inl-Finᵉ nᵉ kᵉ
neq-inr-Fin-inl-Finᵉ (succ-ℕᵉ nᵉ) (inlᵉ kᵉ) =
  neq-inr-Fin-inl-Finᵉ nᵉ kᵉ ∘ᵉ is-injective-inlᵉ
neq-inr-Fin-inl-Finᵉ (succ-ℕᵉ nᵉ) (inrᵉ kᵉ) = neq-inr-inlᵉ
```

### The standard finite types in an arbitrary universe

```agda
raise-Finᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → UUᵉ lᵉ
raise-Finᵉ lᵉ kᵉ = raiseᵉ lᵉ (Finᵉ kᵉ)

compute-raise-Finᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → Finᵉ kᵉ ≃ᵉ raise-Finᵉ lᵉ kᵉ
compute-raise-Finᵉ lᵉ kᵉ = compute-raiseᵉ lᵉ (Finᵉ kᵉ)

map-raise-Finᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → Finᵉ kᵉ → raise-Finᵉ lᵉ kᵉ
map-raise-Finᵉ lᵉ kᵉ = map-raiseᵉ

raise-Fin-Setᵉ : (lᵉ : Level) (kᵉ : ℕᵉ) → Setᵉ lᵉ
raise-Fin-Setᵉ lᵉ kᵉ = raise-Setᵉ lᵉ (Fin-Setᵉ kᵉ)
```

## Properties

### Being on the left is decidable

```agda
is-decidable-is-inl-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → is-decidableᵉ (is-inl-Finᵉ kᵉ xᵉ)
is-decidable-is-inl-Finᵉ kᵉ (inlᵉ xᵉ) = inlᵉ (xᵉ ,ᵉ reflᵉ)
is-decidable-is-inl-Finᵉ kᵉ (inrᵉ starᵉ) = inrᵉ αᵉ
  where
  αᵉ : is-inl-Finᵉ kᵉ (inrᵉ starᵉ) → emptyᵉ
  αᵉ (yᵉ ,ᵉ ())
```

### `Fin 1` is contractible

```agda
map-equiv-Fin-one-ℕᵉ : Finᵉ 1 → unitᵉ
map-equiv-Fin-one-ℕᵉ (inrᵉ xᵉ) = xᵉ

map-inv-equiv-Fin-one-ℕᵉ : unitᵉ → Finᵉ 1
map-inv-equiv-Fin-one-ℕᵉ xᵉ = inrᵉ xᵉ

is-section-map-inv-equiv-Fin-one-ℕᵉ :
  ( map-equiv-Fin-one-ℕᵉ ∘ᵉ map-inv-equiv-Fin-one-ℕᵉ) ~ᵉ idᵉ
is-section-map-inv-equiv-Fin-one-ℕᵉ _ = reflᵉ

is-retraction-map-inv-equiv-Fin-one-ℕᵉ :
  ( map-inv-equiv-Fin-one-ℕᵉ ∘ᵉ map-equiv-Fin-one-ℕᵉ) ~ᵉ idᵉ
is-retraction-map-inv-equiv-Fin-one-ℕᵉ (inrᵉ _) = reflᵉ

is-equiv-map-equiv-Fin-one-ℕᵉ : is-equivᵉ map-equiv-Fin-one-ℕᵉ
is-equiv-map-equiv-Fin-one-ℕᵉ =
  is-equiv-is-invertibleᵉ
    map-inv-equiv-Fin-one-ℕᵉ
    is-section-map-inv-equiv-Fin-one-ℕᵉ
    is-retraction-map-inv-equiv-Fin-one-ℕᵉ

equiv-Fin-one-ℕᵉ : Finᵉ 1 ≃ᵉ unitᵉ
pr1ᵉ equiv-Fin-one-ℕᵉ = map-equiv-Fin-one-ℕᵉ
pr2ᵉ equiv-Fin-one-ℕᵉ = is-equiv-map-equiv-Fin-one-ℕᵉ

is-contr-Fin-one-ℕᵉ : is-contrᵉ (Finᵉ 1ᵉ)
is-contr-Fin-one-ℕᵉ = is-contr-equivᵉ unitᵉ equiv-Fin-one-ℕᵉ is-contr-unitᵉ

is-not-contractible-Finᵉ :
  (kᵉ : ℕᵉ) → is-not-one-ℕᵉ kᵉ → is-not-contractibleᵉ (Finᵉ kᵉ)
is-not-contractible-Finᵉ zero-ℕᵉ fᵉ = is-not-contractible-emptyᵉ
is-not-contractible-Finᵉ (succ-ℕᵉ zero-ℕᵉ) fᵉ Cᵉ = fᵉ reflᵉ
is-not-contractible-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) fᵉ Cᵉ =
  neq-inl-inrᵉ (eq-is-contr'ᵉ Cᵉ (neg-two-Finᵉ (succ-ℕᵉ kᵉ)) (neg-one-Finᵉ (succ-ℕᵉ kᵉ)))
```

### The inclusion of `Fin k` into `ℕ`

```agda
nat-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → ℕᵉ
nat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = nat-Finᵉ kᵉ xᵉ
nat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) = kᵉ

nat-Fin-reverseᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → ℕᵉ
nat-Fin-reverseᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ)
nat-Fin-reverseᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) = 0

strict-upper-bound-nat-Finᵉ : (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → le-ℕᵉ (nat-Finᵉ kᵉ xᵉ) kᵉ
strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  transitive-le-ℕᵉ
    ( nat-Finᵉ kᵉ xᵉ)
    ( kᵉ)
    ( succ-ℕᵉ kᵉ)
    ( strict-upper-bound-nat-Finᵉ kᵉ xᵉ)
    ( succ-le-ℕᵉ kᵉ)
strict-upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) =
  succ-le-ℕᵉ kᵉ

upper-bound-nat-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → leq-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) kᵉ
upper-bound-nat-Finᵉ zero-ℕᵉ (inrᵉ starᵉ) = starᵉ
upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  preserves-leq-succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) kᵉ (upper-bound-nat-Finᵉ kᵉ xᵉ)
upper-bound-nat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = refl-leq-ℕᵉ (succ-ℕᵉ kᵉ)

upper-bound-nat-Fin'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → leq-ℕᵉ (nat-Finᵉ kᵉ xᵉ) kᵉ
upper-bound-nat-Fin'ᵉ kᵉ xᵉ =
  leq-le-ℕᵉ (nat-Finᵉ kᵉ xᵉ) kᵉ (strict-upper-bound-nat-Finᵉ kᵉ xᵉ)

is-injective-nat-Finᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (nat-Finᵉ kᵉ)
is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} pᵉ =
  apᵉ inlᵉ (is-injective-nat-Finᵉ kᵉ pᵉ)
is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inrᵉ starᵉ} pᵉ =
  ex-falsoᵉ (neq-le-ℕᵉ (strict-upper-bound-nat-Finᵉ kᵉ xᵉ) pᵉ)
is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inlᵉ yᵉ} pᵉ =
  ex-falsoᵉ (neq-le-ℕᵉ (strict-upper-bound-nat-Finᵉ kᵉ yᵉ) (invᵉ pᵉ))
is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ =
  reflᵉ

is-emb-nat-Finᵉ : (kᵉ : ℕᵉ) → is-embᵉ (nat-Finᵉ kᵉ)
is-emb-nat-Finᵉ kᵉ = is-emb-is-injectiveᵉ is-set-ℕᵉ (is-injective-nat-Finᵉ kᵉ)

emb-nat-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ ↪ᵉ ℕᵉ
pr1ᵉ (emb-nat-Finᵉ kᵉ) = nat-Finᵉ kᵉ
pr2ᵉ (emb-nat-Finᵉ kᵉ) = is-emb-nat-Finᵉ kᵉ
```

### The zero elements in the standard finite types

```agda
zero-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ)
zero-Finᵉ zero-ℕᵉ = inrᵉ starᵉ
zero-Finᵉ (succ-ℕᵉ kᵉ) = inlᵉ (zero-Finᵉ kᵉ)

is-zero-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-zero-Finᵉ (succ-ℕᵉ kᵉ) xᵉ = xᵉ ＝ᵉ zero-Finᵉ kᵉ

is-zero-Fin'ᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-zero-Fin'ᵉ (succ-ℕᵉ kᵉ) xᵉ = zero-Finᵉ kᵉ ＝ᵉ xᵉ

is-nonzero-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-nonzero-Finᵉ (succ-ℕᵉ kᵉ) xᵉ = ¬ᵉ (is-zero-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
```

### The successor function on the standard finite types

```agda
skip-zero-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ (succ-ℕᵉ kᵉ)
skip-zero-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = inlᵉ (skip-zero-Finᵉ kᵉ xᵉ)
skip-zero-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = inrᵉ starᵉ

succ-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = skip-zero-Finᵉ kᵉ xᵉ
succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = (zero-Finᵉ kᵉ)

Fin-Type-With-Endomorphismᵉ : ℕᵉ → Type-With-Endomorphismᵉ lzero
pr1ᵉ (Fin-Type-With-Endomorphismᵉ kᵉ) = Finᵉ kᵉ
pr2ᵉ (Fin-Type-With-Endomorphismᵉ kᵉ) = succ-Finᵉ kᵉ
```

```agda
is-zero-nat-zero-Finᵉ : {kᵉ : ℕᵉ} → is-zero-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ))
is-zero-nat-zero-Finᵉ {zero-ℕᵉ} = reflᵉ
is-zero-nat-zero-Finᵉ {succ-ℕᵉ kᵉ} = is-zero-nat-zero-Finᵉ {kᵉ}

nat-skip-zero-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) →
  nat-Finᵉ (succ-ℕᵉ kᵉ) (skip-zero-Finᵉ kᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ)
nat-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = nat-skip-zero-Finᵉ kᵉ xᵉ
nat-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = reflᵉ

nat-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) →
  nat-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ)) ＝ᵉ succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ)
nat-succ-Finᵉ kᵉ xᵉ = nat-skip-zero-Finᵉ kᵉ xᵉ

nat-inr-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → nat-Finᵉ (succ-ℕᵉ kᵉ) (inr-Finᵉ kᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ)
nat-inr-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = nat-inr-Finᵉ kᵉ xᵉ
nat-inr-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = reflᵉ
```

```agda
one-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ)
one-Finᵉ kᵉ = succ-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)

is-one-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-one-Finᵉ (succ-ℕᵉ kᵉ) xᵉ = xᵉ ＝ᵉ one-Finᵉ kᵉ

is-zero-or-one-Fin-two-ℕᵉ :
  (xᵉ : Finᵉ 2ᵉ) → (is-zero-Finᵉ 2 xᵉ) +ᵉ (is-one-Finᵉ 2 xᵉ)
is-zero-or-one-Fin-two-ℕᵉ (inlᵉ (inrᵉ starᵉ)) = inlᵉ reflᵉ
is-zero-or-one-Fin-two-ℕᵉ (inrᵉ starᵉ) = inrᵉ reflᵉ

is-one-nat-one-Finᵉ :
  (kᵉ : ℕᵉ) → is-one-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (one-Finᵉ (succ-ℕᵉ kᵉ)))
is-one-nat-one-Finᵉ zero-ℕᵉ = reflᵉ
is-one-nat-one-Finᵉ (succ-ℕᵉ kᵉ) = is-one-nat-one-Finᵉ kᵉ
```

```agda
is-injective-inl-Finᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (inl-Finᵉ kᵉ)
is-injective-inl-Finᵉ kᵉ reflᵉ = reflᵉ
```

### Exercise 7.5 (c)

```agda
neq-zero-skip-zero-Finᵉ :
  {kᵉ : ℕᵉ} {xᵉ : Finᵉ kᵉ} →
  is-nonzero-Finᵉ (succ-ℕᵉ kᵉ) (skip-zero-Finᵉ kᵉ xᵉ)
neq-zero-skip-zero-Finᵉ {succ-ℕᵉ kᵉ} {inlᵉ xᵉ} pᵉ =
  neq-zero-skip-zero-Finᵉ {kᵉ = kᵉ} {xᵉ = xᵉ} (is-injective-inl-Finᵉ (succ-ℕᵉ kᵉ) pᵉ)

neq-zero-succ-Finᵉ :
  {kᵉ : ℕᵉ} {xᵉ : Finᵉ kᵉ} →
  is-nonzero-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (inl-Finᵉ kᵉ xᵉ))
neq-zero-succ-Finᵉ {succ-ℕᵉ kᵉ} {inlᵉ xᵉ} pᵉ =
  neq-zero-succ-Finᵉ (is-injective-inl-Finᵉ (succ-ℕᵉ kᵉ) pᵉ)
neq-zero-succ-Finᵉ {succ-ℕᵉ kᵉ} {inrᵉ starᵉ} ()
```

### Exercise 7.5 (d)

```agda
is-injective-skip-zero-Finᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (skip-zero-Finᵉ kᵉ)
is-injective-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} pᵉ =
  apᵉ inlᵉ (is-injective-skip-zero-Finᵉ kᵉ (is-injective-inl-Finᵉ (succ-ℕᵉ kᵉ) pᵉ))
is-injective-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inrᵉ starᵉ} ()
is-injective-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inlᵉ yᵉ} ()
is-injective-skip-zero-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ = reflᵉ

is-injective-succ-Finᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (succ-Finᵉ kᵉ)
is-injective-succ-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} pᵉ =
  apᵉ inlᵉ (is-injective-skip-zero-Finᵉ kᵉ {xᵉ} {yᵉ} pᵉ)
is-injective-succ-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inrᵉ starᵉ} pᵉ =
  ex-falsoᵉ (neq-zero-succ-Finᵉ {succ-ℕᵉ kᵉ} {inlᵉ xᵉ} (apᵉ inlᵉ pᵉ))
is-injective-succ-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inlᵉ yᵉ} pᵉ =
  ex-falsoᵉ (neq-zero-succ-Finᵉ {succ-ℕᵉ kᵉ} {inlᵉ yᵉ} (apᵉ inlᵉ (invᵉ pᵉ)))
is-injective-succ-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ = reflᵉ
```

Weᵉ defineᵉ aᵉ functionᵉ `skip-neg-two-Fin`ᵉ in orderᵉ to defineᵉ `pred-Fin`.ᵉ

```agda
skip-neg-two-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ (succ-ℕᵉ kᵉ)
skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = inlᵉ (inlᵉ xᵉ)
skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) = neg-one-Finᵉ (succ-ℕᵉ kᵉ)
```

Weᵉ defineᵉ theᵉ predecessorᵉ functionᵉ onᵉ `Finᵉ k`.ᵉ

```agda
pred-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
pred-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = skip-neg-two-Finᵉ kᵉ (pred-Finᵉ kᵉ xᵉ)
pred-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) = neg-two-Finᵉ kᵉ
```

Weᵉ nowᵉ turnᵉ to theᵉ exercise.ᵉ

```agda
pred-zero-Finᵉ :
  (kᵉ : ℕᵉ) → is-neg-one-Finᵉ (succ-ℕᵉ kᵉ) (pred-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ))
pred-zero-Finᵉ (zero-ℕᵉ) = reflᵉ
pred-zero-Finᵉ (succ-ℕᵉ kᵉ) = apᵉ (skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ)) (pred-zero-Finᵉ kᵉ)

succ-skip-neg-two-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  succ-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) ＝ᵉ
  inlᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
succ-skip-neg-two-Finᵉ zero-ℕᵉ (inrᵉ starᵉ) = reflᵉ
succ-skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = reflᵉ
succ-skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) = reflᵉ

is-section-pred-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → succ-Finᵉ kᵉ (pred-Finᵉ kᵉ xᵉ) ＝ᵉ xᵉ
is-section-pred-Finᵉ (succ-ℕᵉ zero-ℕᵉ) (inrᵉ starᵉ) = reflᵉ
is-section-pred-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inlᵉ xᵉ) =
  ( succ-skip-neg-two-Finᵉ kᵉ (pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) ∙ᵉ
  ( apᵉ inlᵉ (is-section-pred-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))
is-section-pred-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inrᵉ starᵉ) = reflᵉ

is-retraction-pred-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → pred-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ) ＝ᵉ xᵉ
is-retraction-pred-Finᵉ (succ-ℕᵉ zero-ℕᵉ) (inrᵉ starᵉ) = reflᵉ
is-retraction-pred-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inlᵉ (inlᵉ xᵉ)) =
  apᵉ (skip-neg-two-Finᵉ (succ-ℕᵉ kᵉ)) (is-retraction-pred-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))
is-retraction-pred-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inlᵉ (inrᵉ starᵉ)) = reflᵉ
is-retraction-pred-Finᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ)) (inrᵉ starᵉ) = pred-zero-Finᵉ (succ-ℕᵉ kᵉ)

is-equiv-succ-Finᵉ : (kᵉ : ℕᵉ) → is-equivᵉ (succ-Finᵉ kᵉ)
pr1ᵉ (pr1ᵉ (is-equiv-succ-Finᵉ kᵉ)) = pred-Finᵉ kᵉ
pr2ᵉ (pr1ᵉ (is-equiv-succ-Finᵉ kᵉ)) = is-section-pred-Finᵉ kᵉ
pr1ᵉ (pr2ᵉ (is-equiv-succ-Finᵉ kᵉ)) = pred-Finᵉ kᵉ
pr2ᵉ (pr2ᵉ (is-equiv-succ-Finᵉ kᵉ)) = is-retraction-pred-Finᵉ kᵉ

equiv-succ-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ ≃ᵉ Finᵉ kᵉ
pr1ᵉ (equiv-succ-Finᵉ kᵉ) = succ-Finᵉ kᵉ
pr2ᵉ (equiv-succ-Finᵉ kᵉ) = is-equiv-succ-Finᵉ kᵉ

is-equiv-pred-Finᵉ : (kᵉ : ℕᵉ) → is-equivᵉ (pred-Finᵉ kᵉ)
pr1ᵉ (pr1ᵉ (is-equiv-pred-Finᵉ kᵉ)) = succ-Finᵉ kᵉ
pr2ᵉ (pr1ᵉ (is-equiv-pred-Finᵉ kᵉ)) = is-retraction-pred-Finᵉ kᵉ
pr1ᵉ (pr2ᵉ (is-equiv-pred-Finᵉ kᵉ)) = succ-Finᵉ kᵉ
pr2ᵉ (pr2ᵉ (is-equiv-pred-Finᵉ kᵉ)) = is-section-pred-Finᵉ kᵉ

equiv-pred-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ ≃ᵉ Finᵉ kᵉ
pr1ᵉ (equiv-pred-Finᵉ kᵉ) = pred-Finᵉ kᵉ
pr2ᵉ (equiv-pred-Finᵉ kᵉ) = is-equiv-pred-Finᵉ kᵉ
```

```agda
leq-nat-succ-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → leq-ℕᵉ (nat-Finᵉ kᵉ (succ-Finᵉ kᵉ xᵉ)) (succ-ℕᵉ (nat-Finᵉ kᵉ xᵉ))
leq-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  leq-eq-ℕᵉ
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (skip-zero-Finᵉ kᵉ xᵉ))
    ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ)))
    ( nat-skip-zero-Finᵉ kᵉ xᵉ)
leq-nat-succ-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ) =
  concatenate-eq-leq-ℕᵉ
    ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ)))
    ( is-zero-nat-zero-Finᵉ {succ-ℕᵉ kᵉ})
    ( leq-zero-ℕᵉ (succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ starᵉ))))
```

### `Fin` is injective

```agda
is-equivalence-injective-Finᵉ : is-equivalence-injectiveᵉ Finᵉ
is-equivalence-injective-Finᵉ {zero-ℕᵉ} {zero-ℕᵉ} eᵉ =
  reflᵉ
is-equivalence-injective-Finᵉ {zero-ℕᵉ} {succ-ℕᵉ lᵉ} eᵉ =
  ex-falsoᵉ (map-inv-equivᵉ eᵉ (zero-Finᵉ lᵉ))
is-equivalence-injective-Finᵉ {succ-ℕᵉ kᵉ} {zero-ℕᵉ} eᵉ =
  ex-falsoᵉ (map-equivᵉ eᵉ (zero-Finᵉ kᵉ))
is-equivalence-injective-Finᵉ {succ-ℕᵉ kᵉ} {succ-ℕᵉ lᵉ} eᵉ =
  apᵉ succ-ℕᵉ (is-equivalence-injective-Finᵉ (equiv-equiv-Maybeᵉ eᵉ))

abstract
  is-injective-Finᵉ : is-injectiveᵉ Finᵉ
  is-injective-Finᵉ =
    is-injective-is-equivalence-injectiveᵉ is-equivalence-injective-Finᵉ

compute-is-equivalence-injective-Fin-id-equivᵉ :
  {nᵉ : ℕᵉ} → is-equivalence-injective-Finᵉ {nᵉ} {nᵉ} id-equivᵉ ＝ᵉ reflᵉ
compute-is-equivalence-injective-Fin-id-equivᵉ {zero-ℕᵉ} = reflᵉ
compute-is-equivalence-injective-Fin-id-equivᵉ {succ-ℕᵉ nᵉ} =
  ap²ᵉ succ-ℕᵉ
    ( ( apᵉ is-equivalence-injective-Finᵉ compute-equiv-equiv-Maybe-id-equivᵉ) ∙ᵉ
      ( compute-is-equivalence-injective-Fin-id-equivᵉ {nᵉ}))
```

### `Fin` is a preunivalent type family

Theᵉ proofᵉ doesᵉ notᵉ relyᵉ onᵉ theᵉ (pre-)univalenceᵉ axiom.ᵉ

```agda
is-section-on-diagonal-is-equivalence-injective-Finᵉ :
  {nᵉ : ℕᵉ} →
  equiv-trᵉ Finᵉ (is-equivalence-injective-Finᵉ {nᵉ} {nᵉ} id-equivᵉ) ＝ᵉ id-equivᵉ
is-section-on-diagonal-is-equivalence-injective-Finᵉ =
  apᵉ (equiv-trᵉ Finᵉ) compute-is-equivalence-injective-Fin-id-equivᵉ

is-retraction-is-equivalence-injective-Finᵉ :
  {nᵉ mᵉ : ℕᵉ} →
  is-retractionᵉ (equiv-trᵉ Finᵉ) (is-equivalence-injective-Finᵉ {nᵉ} {mᵉ})
is-retraction-is-equivalence-injective-Finᵉ reflᵉ =
  compute-is-equivalence-injective-Fin-id-equivᵉ

retraction-equiv-tr-Finᵉ : (nᵉ mᵉ : ℕᵉ) → retractionᵉ (equiv-trᵉ Finᵉ {nᵉ} {mᵉ})
pr1ᵉ (retraction-equiv-tr-Finᵉ nᵉ mᵉ) = is-equivalence-injective-Finᵉ
pr2ᵉ (retraction-equiv-tr-Finᵉ nᵉ mᵉ) = is-retraction-is-equivalence-injective-Finᵉ

is-preunivalent-Finᵉ : is-preunivalentᵉ Finᵉ
is-preunivalent-Finᵉ =
  is-preunivalent-retraction-equiv-tr-Setᵉ Fin-Setᵉ retraction-equiv-tr-Finᵉ
```