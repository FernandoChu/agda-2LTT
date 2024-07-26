# Subsingleton induction

```agda
module foundation.subsingleton-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.singleton-inductionᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

{{#conceptᵉ "Subsingletonᵉ induction"ᵉ Agda=ind-subsingletonᵉ}} onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
slightᵉ variantᵉ ofᵉ [singletonᵉ induction](foundation.singleton-induction.mdᵉ) whichᵉ
in turnᵉ isᵉ aᵉ principleᵉ analogousᵉ to inductionᵉ forᵉ theᵉ
[unitᵉ type](foundation.unit-type.md).ᵉ Subsingletonᵉ inductionᵉ usesᵉ theᵉ
observationᵉ thatᵉ aᵉ typeᵉ equippedᵉ with anᵉ elementᵉ isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ aᵉ
[proposition](foundation-core.propositions.md).ᵉ

Subsingletonᵉ inductionᵉ statesᵉ thatᵉ givenᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ to
constructᵉ aᵉ sectionᵉ ofᵉ `B`ᵉ itᵉ sufficesᵉ to provideᵉ anᵉ elementᵉ ofᵉ `Bᵉ a`ᵉ forᵉ someᵉ
`aᵉ : A`.ᵉ

## Definition

### Subsingleton induction

```agda
is-subsingletonᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} (Aᵉ : UUᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-subsingletonᵉ lᵉ Aᵉ = {Bᵉ : Aᵉ → UUᵉ lᵉ} (aᵉ : Aᵉ) → sectionᵉ (ev-pointᵉ aᵉ {Bᵉ})

ind-is-subsingletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  ({lᵉ : Level} → is-subsingletonᵉ lᵉ Aᵉ) → {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) →
  Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ
ind-is-subsingletonᵉ is-subsingleton-Aᵉ aᵉ = pr1ᵉ (is-subsingleton-Aᵉ aᵉ)

compute-ind-is-subsingletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : {lᵉ : Level} → is-subsingletonᵉ lᵉ Aᵉ) →
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) → ev-pointᵉ aᵉ {Bᵉ} ∘ᵉ ind-is-subsingletonᵉ Hᵉ {Bᵉ} aᵉ ~ᵉ idᵉ
compute-ind-is-subsingletonᵉ is-subsingleton-Aᵉ aᵉ = pr2ᵉ (is-subsingleton-Aᵉ aᵉ)
```

## Properties

### Propositions satisfy subsingleton induction

```agda
abstract
  ind-subsingletonᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (is-prop-Aᵉ : is-propᵉ Aᵉ)
    {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) → Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ
  ind-subsingletonᵉ is-prop-Aᵉ {Bᵉ} aᵉ =
    ind-singletonᵉ aᵉ (is-proof-irrelevant-is-propᵉ is-prop-Aᵉ aᵉ) Bᵉ

abstract
  compute-ind-subsingletonᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
    (is-prop-Aᵉ : is-propᵉ Aᵉ) {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) →
    ev-pointᵉ aᵉ {Bᵉ} ∘ᵉ ind-subsingletonᵉ is-prop-Aᵉ {Bᵉ} aᵉ ~ᵉ idᵉ
  compute-ind-subsingletonᵉ is-prop-Aᵉ {Bᵉ} aᵉ =
    compute-ind-singletonᵉ aᵉ (is-proof-irrelevant-is-propᵉ is-prop-Aᵉ aᵉ) Bᵉ
```

### A type satisfies subsingleton induction if and only if it is a proposition

```agda
is-subsingleton-is-propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-propᵉ Aᵉ → is-subsingletonᵉ l2ᵉ Aᵉ
is-subsingleton-is-propᵉ is-prop-Aᵉ {Bᵉ} aᵉ =
  is-singleton-is-contrᵉ aᵉ (is-proof-irrelevant-is-propᵉ is-prop-Aᵉ aᵉ) Bᵉ

abstract
  is-prop-ind-subsingletonᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
    ({l2ᵉ : Level} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (aᵉ : Aᵉ) → Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-propᵉ Aᵉ
  is-prop-ind-subsingletonᵉ Aᵉ Sᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( λ aᵉ → is-contr-ind-singletonᵉ Aᵉ aᵉ (λ Bᵉ → Sᵉ {Bᵉ = Bᵉ} aᵉ))

abstract
  is-prop-is-subsingletonᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → ({l2ᵉ : Level} → is-subsingletonᵉ l2ᵉ Aᵉ) → is-propᵉ Aᵉ
  is-prop-is-subsingletonᵉ Aᵉ Sᵉ = is-prop-ind-subsingletonᵉ Aᵉ (pr1ᵉ ∘ᵉ Sᵉ)
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}