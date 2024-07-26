# The pigeonhole principle

```agda
module univalent-combinatorics.pigeonhole-principleᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.pairs-of-distinct-elementsᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.embeddings-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.repetitions-of-valuesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Ifᵉ `fᵉ : Xᵉ → Y`ᵉ isᵉ anᵉ injectiveᵉ mapᵉ betweenᵉ finiteᵉ typesᵉ `X`ᵉ andᵉ `Y`ᵉ with `k`ᵉ andᵉ
`l`ᵉ elements,ᵉ thenᵉ `kᵉ ≤ᵉ l`.ᵉ Conversely,ᵉ ifᵉ `lᵉ <ᵉ k`,ᵉ thenᵉ noᵉ mapᵉ `fᵉ : Xᵉ → Y`ᵉ isᵉ
injective.ᵉ

## Theorems

### The pigeonhole principle for standard finite types

#### Given an embedding `Fin k ↪ Fin l`, it follows that `k ≤ l`

```agda
leq-emb-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) → Finᵉ kᵉ ↪ᵉ Finᵉ lᵉ → kᵉ ≤-ℕᵉ lᵉ
leq-emb-Finᵉ zero-ℕᵉ zero-ℕᵉ fᵉ = refl-leq-ℕᵉ zero-ℕᵉ
leq-emb-Finᵉ (succ-ℕᵉ kᵉ) zero-ℕᵉ fᵉ = ex-falsoᵉ (map-embᵉ fᵉ (inrᵉ starᵉ))
leq-emb-Finᵉ zero-ℕᵉ (succ-ℕᵉ lᵉ) fᵉ = leq-zero-ℕᵉ (succ-ℕᵉ lᵉ)
leq-emb-Finᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ lᵉ) fᵉ = leq-emb-Finᵉ kᵉ lᵉ (reduce-emb-Finᵉ kᵉ lᵉ fᵉ)

leq-is-emb-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) {fᵉ : Finᵉ kᵉ → Finᵉ lᵉ} → is-embᵉ fᵉ → kᵉ ≤-ℕᵉ lᵉ
leq-is-emb-Finᵉ kᵉ lᵉ {fᵉ = fᵉ} Hᵉ = leq-emb-Finᵉ kᵉ lᵉ (pairᵉ fᵉ Hᵉ)
```

#### Given an injective map `Fin k → Fin l`, it follows that `k ≤ l`

```agda
leq-is-injective-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) {fᵉ : Finᵉ kᵉ → Finᵉ lᵉ} → is-injectiveᵉ fᵉ → kᵉ ≤-ℕᵉ lᵉ
leq-is-injective-Finᵉ kᵉ lᵉ Hᵉ =
  leq-is-emb-Finᵉ kᵉ lᵉ (is-emb-is-injectiveᵉ (is-set-Finᵉ lᵉ) Hᵉ)
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not an embedding

```agda
is-not-emb-le-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) → le-ℕᵉ lᵉ kᵉ → ¬ᵉ (is-embᵉ fᵉ)
is-not-emb-le-Finᵉ kᵉ lᵉ fᵉ pᵉ =
  map-negᵉ (leq-is-emb-Finᵉ kᵉ lᵉ) (contradiction-le-ℕᵉ lᵉ kᵉ pᵉ)
```

#### If `l < k`, then any map `f : Fin k → Fin l` is not injective

```agda
is-not-injective-le-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) → le-ℕᵉ lᵉ kᵉ → is-not-injectiveᵉ fᵉ
is-not-injective-le-Finᵉ kᵉ lᵉ fᵉ pᵉ =
  map-negᵉ (is-emb-is-injectiveᵉ (is-set-Finᵉ lᵉ)) (is-not-emb-le-Finᵉ kᵉ lᵉ fᵉ pᵉ)
```

#### There is no injective map `Fin (k + 1) → Fin k`

```agda
is-not-injective-map-Fin-succ-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ kᵉ) → is-not-injectiveᵉ fᵉ
is-not-injective-map-Fin-succ-Finᵉ kᵉ fᵉ =
  is-not-injective-le-Finᵉ (succ-ℕᵉ kᵉ) kᵉ fᵉ (succ-le-ℕᵉ kᵉ)
```

#### There is no embedding `ℕ ↪ Fin k`

```agda
no-embedding-ℕ-Finᵉ :
  (kᵉ : ℕᵉ) → ¬ᵉ (ℕᵉ ↪ᵉ Finᵉ kᵉ)
no-embedding-ℕ-Finᵉ kᵉ eᵉ =
  contradiction-leq-ℕᵉ kᵉ kᵉ
    ( refl-leq-ℕᵉ kᵉ)
    ( leq-emb-Finᵉ (succ-ℕᵉ kᵉ) kᵉ (comp-embᵉ eᵉ (emb-nat-Finᵉ (succ-ℕᵉ kᵉ))))
```

#### For any `f : Fin k → Fin l`, where `l < k`, we construct a pair of distinct elements of `Fin k` on which `f` assumes the same value

```agda
module _
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) (pᵉ : le-ℕᵉ lᵉ kᵉ)
  where

  repetition-of-values-le-Finᵉ : repetition-of-valuesᵉ fᵉ
  repetition-of-values-le-Finᵉ =
    repetition-of-values-is-not-injective-Finᵉ kᵉ lᵉ fᵉ
      ( is-not-injective-le-Finᵉ kᵉ lᵉ fᵉ pᵉ)

  pair-of-distinct-elements-repetition-of-values-le-Finᵉ :
    pair-of-distinct-elementsᵉ (Finᵉ kᵉ)
  pair-of-distinct-elements-repetition-of-values-le-Finᵉ =
    pr1ᵉ repetition-of-values-le-Finᵉ

  first-repetition-of-values-le-Finᵉ : Finᵉ kᵉ
  first-repetition-of-values-le-Finᵉ =
    first-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-Finᵉ

  second-repetition-of-values-le-Finᵉ : Finᵉ kᵉ
  second-repetition-of-values-le-Finᵉ =
    second-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-Finᵉ

  distinction-repetition-of-values-le-Finᵉ :
    first-repetition-of-values-le-Finᵉ ≠ᵉ second-repetition-of-values-le-Finᵉ
  distinction-repetition-of-values-le-Finᵉ =
    distinction-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-Finᵉ

  is-repetition-of-values-repetition-of-values-le-Finᵉ :
    is-repetition-of-valuesᵉ fᵉ
      pair-of-distinct-elements-repetition-of-values-le-Finᵉ
  is-repetition-of-values-repetition-of-values-le-Finᵉ =
    is-repetition-of-values-repetition-of-valuesᵉ fᵉ
      repetition-of-values-le-Finᵉ

repetition-of-values-Fin-succ-to-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ kᵉ) → repetition-of-valuesᵉ fᵉ
repetition-of-values-Fin-succ-to-Finᵉ kᵉ fᵉ =
  repetition-of-values-le-Finᵉ (succ-ℕᵉ kᵉ) kᵉ fᵉ (succ-le-ℕᵉ kᵉ)
```

### The pigeonhole principle for types equipped with a counting

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eAᵉ : countᵉ Aᵉ) (eBᵉ : countᵉ Bᵉ)
  where
```

#### If `f : A ↪ B` is an embedding between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-emb-countᵉ :
    (Aᵉ ↪ᵉ Bᵉ) → (number-of-elements-countᵉ eAᵉ) ≤-ℕᵉ (number-of-elements-countᵉ eBᵉ)
  leq-emb-countᵉ fᵉ =
    leq-emb-Finᵉ
      ( number-of-elements-countᵉ eAᵉ)
      ( number-of-elements-countᵉ eBᵉ)
      ( comp-embᵉ
        ( comp-embᵉ (emb-equivᵉ (inv-equiv-countᵉ eBᵉ)) fᵉ)
        ( emb-equivᵉ (equiv-countᵉ eAᵉ)))

  leq-is-emb-countᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ →
    (number-of-elements-countᵉ eAᵉ) ≤-ℕᵉ (number-of-elements-countᵉ eBᵉ)
  leq-is-emb-countᵉ {fᵉ} Hᵉ = leq-emb-countᵉ (pairᵉ fᵉ Hᵉ)
```

#### If `f : A → B` is an injective map between types equipped with a counting, then the number of elements of `A` is less than the number of elements of `B`

```agda
  leq-is-injective-countᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-injectiveᵉ fᵉ →
    (number-of-elements-countᵉ eAᵉ) ≤-ℕᵉ (number-of-elements-countᵉ eBᵉ)
  leq-is-injective-countᵉ Hᵉ =
    leq-is-emb-countᵉ (is-emb-is-injectiveᵉ (is-set-countᵉ eBᵉ) Hᵉ)
```

#### There is no embedding `A ↪ B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-emb-le-countᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    le-ℕᵉ (number-of-elements-countᵉ eBᵉ) (number-of-elements-countᵉ eAᵉ) →
    ¬ᵉ (is-embᵉ fᵉ)
  is-not-emb-le-countᵉ fᵉ pᵉ Hᵉ =
    is-not-emb-le-Finᵉ
      ( number-of-elements-countᵉ eAᵉ)
      ( number-of-elements-countᵉ eBᵉ)
      ( map-embᵉ hᵉ)
      ( pᵉ)
      ( is-emb-map-embᵉ hᵉ)
    where
    hᵉ : Finᵉ (number-of-elements-countᵉ eAᵉ) ↪ᵉ Finᵉ (number-of-elements-countᵉ eBᵉ)
    hᵉ = comp-embᵉ
        ( emb-equivᵉ (inv-equiv-countᵉ eBᵉ))
          ( comp-embᵉ (pairᵉ fᵉ Hᵉ) (emb-equivᵉ (equiv-countᵉ eAᵉ)))
```

#### There is no injective map `A → B` between types equipped with a counting if the number of elements of `B` is strictly less than the number of elements of `A`

```agda
  is-not-injective-le-countᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    le-ℕᵉ (number-of-elements-countᵉ eBᵉ) (number-of-elements-countᵉ eAᵉ) →
    is-not-injectiveᵉ fᵉ
  is-not-injective-le-countᵉ fᵉ pᵉ Hᵉ =
    is-not-emb-le-countᵉ fᵉ pᵉ (is-emb-is-injectiveᵉ (is-set-countᵉ eBᵉ) Hᵉ)
```

#### There is no embedding `ℕ ↪ A` into a type equipped with a counting

```agda
no-embedding-ℕ-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) → ¬ᵉ (ℕᵉ ↪ᵉ Aᵉ)
no-embedding-ℕ-countᵉ eᵉ fᵉ =
  no-embedding-ℕ-Finᵉ
  ( number-of-elements-countᵉ eᵉ)
  ( comp-embᵉ (emb-equivᵉ (inv-equiv-countᵉ eᵉ)) fᵉ)
```

#### For any map `f : A → B` between types equipped with a counting, if `|A| < |B|` then we construct a pair of distinct elements of `A` on which `f` assumes the same value

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eAᵉ : countᵉ Aᵉ) (eBᵉ : countᵉ Bᵉ)
  (fᵉ : Aᵉ → Bᵉ)
  (pᵉ : le-ℕᵉ (number-of-elements-countᵉ eBᵉ) (number-of-elements-countᵉ eAᵉ))
  where

  repetition-of-values-le-countᵉ : repetition-of-valuesᵉ fᵉ
  repetition-of-values-le-countᵉ =
    map-equiv-repetition-of-valuesᵉ
      ( (map-inv-equiv-countᵉ eBᵉ ∘ᵉ fᵉ) ∘ᵉ (map-equiv-countᵉ eAᵉ))
      ( fᵉ)
      ( equiv-countᵉ eAᵉ)
      ( equiv-countᵉ eBᵉ)
      ( is-section-map-inv-equiv-countᵉ eBᵉ ·rᵉ (fᵉ ∘ᵉ (map-equiv-countᵉ eAᵉ)))
      ( repetition-of-values-le-Finᵉ
        ( number-of-elements-countᵉ eAᵉ)
        ( number-of-elements-countᵉ eBᵉ)
        ( (map-inv-equiv-countᵉ eBᵉ ∘ᵉ fᵉ) ∘ᵉ (map-equiv-countᵉ eAᵉ))
        ( pᵉ))

  pair-of-distinct-elements-repetition-of-values-le-countᵉ :
    pair-of-distinct-elementsᵉ Aᵉ
  pair-of-distinct-elements-repetition-of-values-le-countᵉ =
    pr1ᵉ repetition-of-values-le-countᵉ

  first-repetition-of-values-le-countᵉ : Aᵉ
  first-repetition-of-values-le-countᵉ =
    first-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-countᵉ

  second-repetition-of-values-le-countᵉ : Aᵉ
  second-repetition-of-values-le-countᵉ =
    second-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-countᵉ

  distinction-repetition-of-values-le-countᵉ :
    first-repetition-of-values-le-countᵉ ≠ᵉ second-repetition-of-values-le-countᵉ
  distinction-repetition-of-values-le-countᵉ =
    distinction-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-le-countᵉ

  is-repetition-of-values-repetition-of-values-le-countᵉ :
    is-repetition-of-valuesᵉ fᵉ
      pair-of-distinct-elements-repetition-of-values-le-countᵉ
  is-repetition-of-values-repetition-of-values-le-countᵉ =
    is-repetition-of-values-repetition-of-valuesᵉ fᵉ
      repetition-of-values-le-countᵉ
```

### The pigeonhole principle for finite types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Hᵉ : is-finiteᵉ Aᵉ) (Kᵉ : is-finiteᵉ Bᵉ)
  where
```

#### If `A ↪ B` is an embedding between finite types, then `|A| ≤ |B|`

```agda
  leq-emb-is-finiteᵉ :
    (Aᵉ ↪ᵉ Bᵉ) →
    (number-of-elements-is-finiteᵉ Hᵉ) ≤-ℕᵉ (number-of-elements-is-finiteᵉ Kᵉ)
  leq-emb-is-finiteᵉ fᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ Pᵉ
      ( λ eAᵉ →
        apply-universal-property-trunc-Propᵉ Kᵉ Pᵉ
          ( λ eBᵉ →
            concatenate-eq-leq-eq-ℕᵉ
              ( invᵉ (compute-number-of-elements-is-finiteᵉ eAᵉ Hᵉ))
              ( leq-emb-countᵉ eAᵉ eBᵉ fᵉ)
              ( compute-number-of-elements-is-finiteᵉ eBᵉ Kᵉ)))
    where
    Pᵉ : Propᵉ lzero
    Pᵉ = leq-ℕ-Propᵉ
        ( number-of-elements-is-finiteᵉ Hᵉ)
          ( number-of-elements-is-finiteᵉ Kᵉ)

  leq-is-emb-is-finiteᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-embᵉ fᵉ →
    (number-of-elements-is-finiteᵉ Hᵉ) ≤-ℕᵉ (number-of-elements-is-finiteᵉ Kᵉ)
  leq-is-emb-is-finiteᵉ {fᵉ} Hᵉ =
    leq-emb-is-finiteᵉ (pairᵉ fᵉ Hᵉ)
```

#### If `A → B` is an injective map between finite types, then `|A| ≤ |B|`

```agda
  leq-is-injective-is-finiteᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-injectiveᵉ fᵉ →
    (number-of-elements-is-finiteᵉ Hᵉ) ≤-ℕᵉ (number-of-elements-is-finiteᵉ Kᵉ)
  leq-is-injective-is-finiteᵉ Iᵉ =
    leq-is-emb-is-finiteᵉ (is-emb-is-injectiveᵉ (is-set-is-finiteᵉ Kᵉ) Iᵉ)
```

#### There are no embeddings between finite types `A` and `B` such that `|B| < |A|

```agda
  is-not-emb-le-is-finiteᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    le-ℕᵉ (number-of-elements-is-finiteᵉ Kᵉ) (number-of-elements-is-finiteᵉ Hᵉ) →
    ¬ᵉ (is-embᵉ fᵉ)
  is-not-emb-le-is-finiteᵉ fᵉ pᵉ Eᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ empty-Propᵉ
      ( λ eᵉ →
        apply-universal-property-trunc-Propᵉ Kᵉ empty-Propᵉ
          ( λ dᵉ → is-not-emb-le-countᵉ eᵉ dᵉ fᵉ
            ( concatenate-eq-le-eq-ℕᵉ
              ( compute-number-of-elements-is-finiteᵉ dᵉ Kᵉ)
              ( pᵉ)
              ( invᵉ (compute-number-of-elements-is-finiteᵉ eᵉ Hᵉ)))
            ( Eᵉ)))
```

#### There are no injective maps between finite types `A` and `B` such that `|B| < |A|

```agda
  is-not-injective-le-is-finiteᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    le-ℕᵉ (number-of-elements-is-finiteᵉ Kᵉ) (number-of-elements-is-finiteᵉ Hᵉ) →
    is-not-injectiveᵉ fᵉ
  is-not-injective-le-is-finiteᵉ fᵉ pᵉ Iᵉ =
    is-not-emb-le-is-finiteᵉ fᵉ pᵉ (is-emb-is-injectiveᵉ (is-set-is-finiteᵉ Kᵉ) Iᵉ)
```

#### There are no embeddings `ℕ ↪ A` into a finite type `A`

```agda
no-embedding-ℕ-is-finiteᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (Hᵉ : is-finiteᵉ Aᵉ) → ¬ᵉ (ℕᵉ ↪ᵉ Aᵉ)
no-embedding-ℕ-is-finiteᵉ Hᵉ fᵉ =
  apply-universal-property-trunc-Propᵉ Hᵉ empty-Propᵉ
    ( λ eᵉ → no-embedding-ℕ-countᵉ eᵉ fᵉ)
```