# Decidable propositions

```agda
module foundation.decidable-propositionsᵉ where

open import foundation-core.decidable-propositionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.booleansᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.transport-along-identificationsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Aᵉ decidableᵉ propositionᵉ isᵉ aᵉ propositionᵉ thatᵉ hasᵉ aᵉ decidableᵉ underlyingᵉ type.ᵉ

## Properties

### The forgetful map from decidable propositions to propositions is an embedding

```agda
is-emb-prop-Decidable-Propᵉ : {lᵉ : Level} → is-embᵉ (prop-Decidable-Propᵉ {lᵉ})
is-emb-prop-Decidable-Propᵉ =
  is-emb-totᵉ
    ( λ Xᵉ →
      is-emb-inclusion-subtypeᵉ
        ( λ Hᵉ → pairᵉ (is-decidableᵉ Xᵉ) (is-prop-is-decidableᵉ Hᵉ)))

emb-prop-Decidable-Propᵉ : {lᵉ : Level} → Decidable-Propᵉ lᵉ ↪ᵉ Propᵉ lᵉ
pr1ᵉ emb-prop-Decidable-Propᵉ = prop-Decidable-Propᵉ
pr2ᵉ emb-prop-Decidable-Propᵉ = is-emb-prop-Decidable-Propᵉ
```

### The type of decidable propositions in universe level `l` is equivalent to the type of booleans

```agda
module _
  {lᵉ : Level}
  where

  split-Decidable-Propᵉ :
    Decidable-Propᵉ lᵉ ≃ᵉ
    ((Σᵉ (Propᵉ lᵉ) type-Propᵉ) +ᵉ (Σᵉ (Propᵉ lᵉ) (λ Qᵉ → ¬ᵉ (type-Propᵉ Qᵉ))))
  split-Decidable-Propᵉ =
    ( left-distributive-Σ-coproductᵉ (Propᵉ lᵉ) (λ Qᵉ → pr1ᵉ Qᵉ) (λ Qᵉ → ¬ᵉ (pr1ᵉ Qᵉ))) ∘eᵉ
    ( inv-associative-Σᵉ (UUᵉ lᵉ) is-propᵉ (λ Xᵉ → is-decidableᵉ (pr1ᵉ Xᵉ)))

  map-equiv-bool-Decidable-Prop'ᵉ :
    (Σᵉ (Propᵉ lᵉ) type-Propᵉ) +ᵉ (Σᵉ (Propᵉ lᵉ) (λ Qᵉ → ¬ᵉ (type-Propᵉ Qᵉ))) →
    boolᵉ
  map-equiv-bool-Decidable-Prop'ᵉ (inlᵉ xᵉ) = trueᵉ
  map-equiv-bool-Decidable-Prop'ᵉ (inrᵉ xᵉ) = falseᵉ

  map-inv-equiv-bool-Decidable-Prop'ᵉ :
    boolᵉ →
    (Σᵉ (Propᵉ lᵉ) type-Propᵉ) +ᵉ (Σᵉ (Propᵉ lᵉ) (λ Qᵉ → ¬ᵉ (type-Propᵉ Qᵉ)))
  map-inv-equiv-bool-Decidable-Prop'ᵉ trueᵉ =
    inlᵉ (pairᵉ (raise-unit-Propᵉ lᵉ) raise-starᵉ)
  map-inv-equiv-bool-Decidable-Prop'ᵉ falseᵉ =
    inrᵉ (pairᵉ (raise-empty-Propᵉ lᵉ) is-empty-raise-emptyᵉ)

  is-section-map-inv-equiv-bool-Decidable-Prop'ᵉ :
    (map-equiv-bool-Decidable-Prop'ᵉ ∘ᵉ map-inv-equiv-bool-Decidable-Prop'ᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-bool-Decidable-Prop'ᵉ trueᵉ = reflᵉ
  is-section-map-inv-equiv-bool-Decidable-Prop'ᵉ falseᵉ = reflᵉ

  is-retraction-map-inv-equiv-bool-Decidable-Prop'ᵉ :
    (map-inv-equiv-bool-Decidable-Prop'ᵉ ∘ᵉ map-equiv-bool-Decidable-Prop'ᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-bool-Decidable-Prop'ᵉ (inlᵉ xᵉ) =
    apᵉ inlᵉ (eq-is-contrᵉ is-torsorial-true-Propᵉ)
  is-retraction-map-inv-equiv-bool-Decidable-Prop'ᵉ (inrᵉ xᵉ) =
    apᵉ inrᵉ (eq-is-contrᵉ is-torsorial-false-Propᵉ)

  is-equiv-map-equiv-bool-Decidable-Prop'ᵉ :
    is-equivᵉ map-equiv-bool-Decidable-Prop'ᵉ
  is-equiv-map-equiv-bool-Decidable-Prop'ᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-bool-Decidable-Prop'ᵉ
      is-section-map-inv-equiv-bool-Decidable-Prop'ᵉ
      is-retraction-map-inv-equiv-bool-Decidable-Prop'ᵉ

  equiv-bool-Decidable-Prop'ᵉ :
    ((Σᵉ (Propᵉ lᵉ) type-Propᵉ) +ᵉ (Σᵉ (Propᵉ lᵉ) (λ Qᵉ → ¬ᵉ (type-Propᵉ Qᵉ)))) ≃ᵉ
    boolᵉ
  pr1ᵉ equiv-bool-Decidable-Prop'ᵉ = map-equiv-bool-Decidable-Prop'ᵉ
  pr2ᵉ equiv-bool-Decidable-Prop'ᵉ = is-equiv-map-equiv-bool-Decidable-Prop'ᵉ

  equiv-bool-Decidable-Propᵉ : Decidable-Propᵉ lᵉ ≃ᵉ boolᵉ
  equiv-bool-Decidable-Propᵉ = equiv-bool-Decidable-Prop'ᵉ ∘eᵉ split-Decidable-Propᵉ

  abstract
    compute-equiv-bool-Decidable-Propᵉ :
      (Pᵉ : Decidable-Propᵉ lᵉ) →
      type-Decidable-Propᵉ Pᵉ ≃ᵉ (map-equivᵉ equiv-bool-Decidable-Propᵉ Pᵉ ＝ᵉ trueᵉ)
    compute-equiv-bool-Decidable-Propᵉ (pairᵉ Pᵉ (pairᵉ Hᵉ (inlᵉ pᵉ))) =
      equiv-is-contrᵉ
        ( is-proof-irrelevant-is-propᵉ Hᵉ pᵉ)
        ( is-proof-irrelevant-is-propᵉ (is-set-boolᵉ trueᵉ trueᵉ) reflᵉ)
    compute-equiv-bool-Decidable-Propᵉ (pairᵉ Pᵉ (pairᵉ Hᵉ (inrᵉ npᵉ))) =
      equiv-is-emptyᵉ npᵉ neq-false-true-boolᵉ
```

### Types of decidable propositions of any universe level are equivalent

```agda
equiv-universes-Decidable-Propᵉ :
  (lᵉ l'ᵉ : Level) → Decidable-Propᵉ lᵉ ≃ᵉ Decidable-Propᵉ l'ᵉ
equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ =
  inv-equivᵉ equiv-bool-Decidable-Propᵉ ∘eᵉ equiv-bool-Decidable-Propᵉ

iff-universes-Decidable-Propᵉ :
  (lᵉ l'ᵉ : Level) (Pᵉ : Decidable-Propᵉ lᵉ) →
  ( type-Decidable-Propᵉ Pᵉ) ↔ᵉ
  ( type-Decidable-Propᵉ (map-equivᵉ (equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ) Pᵉ))
pr1ᵉ (iff-universes-Decidable-Propᵉ lᵉ l'ᵉ Pᵉ) pᵉ =
  map-inv-equivᵉ
    ( compute-equiv-bool-Decidable-Propᵉ
      ( map-equivᵉ (equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ) Pᵉ))
    ( trᵉ
      ( λ eᵉ → map-equivᵉ eᵉ (map-equivᵉ equiv-bool-Decidable-Propᵉ Pᵉ) ＝ᵉ trueᵉ)
      ( invᵉ (right-inverse-law-equivᵉ equiv-bool-Decidable-Propᵉ))
      ( map-equivᵉ (compute-equiv-bool-Decidable-Propᵉ Pᵉ) pᵉ))
pr2ᵉ (iff-universes-Decidable-Propᵉ lᵉ l'ᵉ Pᵉ) pᵉ =
  map-inv-equivᵉ
    ( compute-equiv-bool-Decidable-Propᵉ Pᵉ)
    ( trᵉ
      ( λ eᵉ → map-equivᵉ eᵉ (map-equivᵉ equiv-bool-Decidable-Propᵉ Pᵉ) ＝ᵉ trueᵉ)
      ( right-inverse-law-equivᵉ equiv-bool-Decidable-Propᵉ)
      ( map-equivᵉ
        ( compute-equiv-bool-Decidable-Propᵉ
          ( map-equivᵉ (equiv-universes-Decidable-Propᵉ lᵉ l'ᵉ) Pᵉ))
        ( pᵉ)))
```

### The type of decidable propositions in any universe is a set

```agda
is-set-Decidable-Propᵉ : {lᵉ : Level} → is-setᵉ (Decidable-Propᵉ lᵉ)
is-set-Decidable-Propᵉ {lᵉ} =
  is-set-equivᵉ boolᵉ equiv-bool-Decidable-Propᵉ is-set-boolᵉ

Decidable-Prop-Setᵉ : (lᵉ : Level) → Setᵉ (lsuc lᵉ)
pr1ᵉ (Decidable-Prop-Setᵉ lᵉ) = Decidable-Propᵉ lᵉ
pr2ᵉ (Decidable-Prop-Setᵉ lᵉ) = is-set-Decidable-Propᵉ
```

### Extensionality of decidable propositions

```agda
module _
  {lᵉ : Level} (Pᵉ Qᵉ : Decidable-Propᵉ lᵉ)
  where

  extensionality-Decidable-Propᵉ :
    (Pᵉ ＝ᵉ Qᵉ) ≃ᵉ (type-Decidable-Propᵉ Pᵉ ↔ᵉ type-Decidable-Propᵉ Qᵉ)
  extensionality-Decidable-Propᵉ =
    ( propositional-extensionalityᵉ
      ( prop-Decidable-Propᵉ Pᵉ)
      ( prop-Decidable-Propᵉ Qᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ emb-prop-Decidable-Propᵉ)

  iff-eq-Decidable-Propᵉ :
    Pᵉ ＝ᵉ Qᵉ → type-Decidable-Propᵉ Pᵉ ↔ᵉ type-Decidable-Propᵉ Qᵉ
  iff-eq-Decidable-Propᵉ = map-equivᵉ extensionality-Decidable-Propᵉ

  eq-iff-Decidable-Propᵉ :
    (type-Decidable-Propᵉ Pᵉ → type-Decidable-Propᵉ Qᵉ) →
    (type-Decidable-Propᵉ Qᵉ → type-Decidable-Propᵉ Pᵉ) → Pᵉ ＝ᵉ Qᵉ
  eq-iff-Decidable-Propᵉ fᵉ gᵉ =
    map-inv-equivᵉ extensionality-Decidable-Propᵉ (pairᵉ fᵉ gᵉ)
```

### The type of decidable propositions in any universe is small

```agda
abstract
  is-small-Decidable-Propᵉ :
    (l1ᵉ l2ᵉ : Level) → is-smallᵉ l2ᵉ (Decidable-Propᵉ l1ᵉ)
  pr1ᵉ (is-small-Decidable-Propᵉ l1ᵉ l2ᵉ) = raiseᵉ l2ᵉ boolᵉ
  pr2ᵉ (is-small-Decidable-Propᵉ l1ᵉ l2ᵉ) =
    compute-raiseᵉ l2ᵉ boolᵉ ∘eᵉ equiv-bool-Decidable-Propᵉ
```

### Decidable propositions have a count

```agda
count-is-decidable-Propᵉ :
    {lᵉ : Level} (Pᵉ : Propᵉ lᵉ) →
    is-decidableᵉ (type-Propᵉ Pᵉ) → countᵉ (type-Propᵉ Pᵉ)
count-is-decidable-Propᵉ Pᵉ (inlᵉ xᵉ) =
  count-is-contrᵉ (is-proof-irrelevant-is-propᵉ (is-prop-type-Propᵉ Pᵉ) xᵉ)
count-is-decidable-Propᵉ Pᵉ (inrᵉ xᵉ) =
  count-is-emptyᵉ xᵉ
```

### Decidable propositions are finite

```agda
abstract
  is-finite-is-decidable-Propᵉ :
    {lᵉ : Level} (Pᵉ : Propᵉ lᵉ) →
    is-decidableᵉ (type-Propᵉ Pᵉ) → is-finiteᵉ (type-Propᵉ Pᵉ)
  is-finite-is-decidable-Propᵉ Pᵉ xᵉ =
    is-finite-countᵉ (count-is-decidable-Propᵉ Pᵉ xᵉ)

is-finite-type-Decidable-Propᵉ :
  {lᵉ : Level} (Pᵉ : Decidable-Propᵉ lᵉ) → is-finiteᵉ (type-Decidable-Propᵉ Pᵉ)
is-finite-type-Decidable-Propᵉ Pᵉ =
  is-finite-is-decidable-Propᵉ
    ( prop-Decidable-Propᵉ Pᵉ)
    ( is-decidable-Decidable-Propᵉ Pᵉ)
```

### The type of decidable propositions of any universe level is finite

```agda
is-finite-Decidable-Propᵉ : {lᵉ : Level} → is-finiteᵉ (Decidable-Propᵉ lᵉ)
is-finite-Decidable-Propᵉ {lᵉ} =
  is-finite-equiv'ᵉ equiv-bool-Decidable-Propᵉ is-finite-boolᵉ

decidable-Prop-𝔽ᵉ : (lᵉ : Level) → 𝔽ᵉ (lsuc lᵉ)
pr1ᵉ (decidable-Prop-𝔽ᵉ lᵉ) = Decidable-Propᵉ lᵉ
pr2ᵉ (decidable-Prop-𝔽ᵉ lᵉ) = is-finite-Decidable-Propᵉ
```

### The negation of a decidable proposition is a decidable proposition

```agda
neg-Decidable-Propᵉ :
  {lᵉ : Level} → Decidable-Propᵉ lᵉ → Decidable-Propᵉ lᵉ
pr1ᵉ (neg-Decidable-Propᵉ Pᵉ) = ¬ᵉ (type-Decidable-Propᵉ Pᵉ)
pr1ᵉ (pr2ᵉ (neg-Decidable-Propᵉ Pᵉ)) = is-prop-negᵉ
pr2ᵉ (pr2ᵉ (neg-Decidable-Propᵉ Pᵉ)) =
  is-decidable-negᵉ (is-decidable-Decidable-Propᵉ Pᵉ)
```