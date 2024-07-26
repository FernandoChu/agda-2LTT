# Weak function extensionality

```agda
module foundation.weak-function-extensionalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

**Weakᵉ functionᵉ extensionality**ᵉ isᵉ theᵉ principleᵉ thatᵉ anyᵉ dependentᵉ productᵉ ofᵉ
[contractibleᵉ types](foundation-core.contractible-types.mdᵉ) isᵉ contractible.ᵉ
Thisᵉ principleᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to
[theᵉ functionᵉ extensionalityᵉ axiom](foundation.function-extensionality.md).ᵉ

## Definition

### Weak function extensionality

```agda
instance-weak-function-extensionalityᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
instance-weak-function-extensionalityᵉ Aᵉ Bᵉ =
  ((xᵉ : Aᵉ) → is-contrᵉ (Bᵉ xᵉ)) → is-contrᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)

weak-function-extensionality-Levelᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
weak-function-extensionality-Levelᵉ l1ᵉ l2ᵉ =
  (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → instance-weak-function-extensionalityᵉ Aᵉ Bᵉ

weak-function-extensionalityᵉ : UUωᵉ
weak-function-extensionalityᵉ =
  {l1ᵉ l2ᵉ : Level} → weak-function-extensionality-Levelᵉ l1ᵉ l2ᵉ
```

### Weaker function extensionality

```agda
instance-weaker-function-extensionalityᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
instance-weaker-function-extensionalityᵉ Aᵉ Bᵉ =
  ((xᵉ : Aᵉ) → is-propᵉ (Bᵉ xᵉ)) → is-propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)

weaker-function-extensionality-Levelᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
weaker-function-extensionality-Levelᵉ l1ᵉ l2ᵉ =
  (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → instance-weaker-function-extensionalityᵉ Aᵉ Bᵉ

weaker-function-extensionalityᵉ : UUωᵉ
weaker-function-extensionalityᵉ =
  {l1ᵉ l2ᵉ : Level} → weaker-function-extensionality-Levelᵉ l1ᵉ l2ᵉ
```

## Properties

### Weak function extensionality is logically equivalent to function extensionality

```agda
abstract
  weak-funext-funextᵉ :
    {l1ᵉ l2ᵉ : Level} →
    function-extensionality-Levelᵉ l1ᵉ l2ᵉ →
    weak-function-extensionality-Levelᵉ l1ᵉ l2ᵉ
  pr1ᵉ (weak-funext-funextᵉ funextᵉ Aᵉ Bᵉ is-contr-Bᵉ) xᵉ =
    centerᵉ (is-contr-Bᵉ xᵉ)
  pr2ᵉ (weak-funext-funextᵉ funextᵉ Aᵉ Bᵉ is-contr-Bᵉ) fᵉ =
    map-inv-is-equivᵉ
      ( funextᵉ (λ xᵉ → centerᵉ (is-contr-Bᵉ xᵉ)) fᵉ)
      ( λ xᵉ → contractionᵉ (is-contr-Bᵉ xᵉ) (fᵉ xᵉ))

abstract
  funext-weak-funextᵉ :
    {l1ᵉ l2ᵉ : Level} →
    weak-function-extensionality-Levelᵉ l1ᵉ l2ᵉ →
    function-extensionality-Levelᵉ l1ᵉ l2ᵉ
  funext-weak-funextᵉ weak-funextᵉ {Aᵉ = Aᵉ} {Bᵉ} fᵉ =
    fundamental-theorem-idᵉ
      ( is-contr-retract-ofᵉ
        ( (xᵉ : Aᵉ) → Σᵉ (Bᵉ xᵉ) (λ bᵉ → fᵉ xᵉ ＝ᵉ bᵉ))
        ( ( λ tᵉ xᵉ → (pr1ᵉ tᵉ xᵉ ,ᵉ pr2ᵉ tᵉ xᵉ)) ,ᵉ
          ( λ tᵉ → (pr1ᵉ ∘ᵉ tᵉ ,ᵉ pr2ᵉ ∘ᵉ tᵉ)) ,ᵉ
          ( λ tᵉ → eq-pair-eq-fiberᵉ reflᵉ))
        ( weak-funextᵉ Aᵉ
          ( λ xᵉ → Σᵉ (Bᵉ xᵉ) (λ bᵉ → fᵉ xᵉ ＝ᵉ bᵉ))
          ( λ xᵉ → is-torsorial-Idᵉ (fᵉ xᵉ))))
      ( λ gᵉ → htpy-eqᵉ {gᵉ = gᵉ})
```

### A partial converse to weak function extensionality

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ}
  (dᵉ : has-decidable-equalityᵉ Iᵉ)
  (Hᵉ : is-contrᵉ ((iᵉ : Iᵉ) → Aᵉ iᵉ))
  where

  cases-function-converse-weak-funextᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (jᵉ : Iᵉ) (eᵉ : is-decidableᵉ (iᵉ ＝ᵉ jᵉ)) → Aᵉ jᵉ
  cases-function-converse-weak-funextᵉ iᵉ xᵉ .iᵉ (inlᵉ reflᵉ) = xᵉ
  cases-function-converse-weak-funextᵉ iᵉ xᵉ jᵉ (inrᵉ fᵉ) = centerᵉ Hᵉ jᵉ

  function-converse-weak-funextᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (jᵉ : Iᵉ) → Aᵉ jᵉ
  function-converse-weak-funextᵉ iᵉ xᵉ jᵉ =
    cases-function-converse-weak-funextᵉ iᵉ xᵉ jᵉ (dᵉ iᵉ jᵉ)

  cases-eq-function-converse-weak-funextᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) (eᵉ : is-decidableᵉ (iᵉ ＝ᵉ iᵉ)) →
    cases-function-converse-weak-funextᵉ iᵉ xᵉ iᵉ eᵉ ＝ᵉ xᵉ
  cases-eq-function-converse-weak-funextᵉ iᵉ xᵉ (inlᵉ pᵉ) =
    apᵉ
      ( λ tᵉ → cases-function-converse-weak-funextᵉ iᵉ xᵉ iᵉ (inlᵉ tᵉ))
      ( eq-is-propᵉ
        ( is-set-has-decidable-equalityᵉ dᵉ iᵉ iᵉ)
        { pᵉ}
        { reflᵉ})
  cases-eq-function-converse-weak-funextᵉ iᵉ xᵉ (inrᵉ fᵉ) =
    ex-falsoᵉ (fᵉ reflᵉ)

  eq-function-converse-weak-funextᵉ :
    (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) →
    function-converse-weak-funextᵉ iᵉ xᵉ iᵉ ＝ᵉ xᵉ
  eq-function-converse-weak-funextᵉ iᵉ xᵉ =
    cases-eq-function-converse-weak-funextᵉ iᵉ xᵉ (dᵉ iᵉ iᵉ)

  converse-weak-funextᵉ : (iᵉ : Iᵉ) → is-contrᵉ (Aᵉ iᵉ)
  pr1ᵉ (converse-weak-funextᵉ iᵉ) = centerᵉ Hᵉ iᵉ
  pr2ᵉ (converse-weak-funextᵉ iᵉ) yᵉ =
    ( htpy-eqᵉ
      ( contractionᵉ Hᵉ (function-converse-weak-funextᵉ iᵉ yᵉ))
      ( iᵉ)) ∙ᵉ
    ( eq-function-converse-weak-funextᵉ iᵉ yᵉ)
```

### Weaker function extensionality implies weak function extensionality

```agda
weak-funext-weaker-funextᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  instance-weaker-function-extensionalityᵉ Aᵉ Bᵉ →
  instance-weak-function-extensionalityᵉ Aᵉ Bᵉ
weak-funext-weaker-funextᵉ Hᵉ Cᵉ =
  is-proof-irrelevant-is-propᵉ
    ( Hᵉ (λ xᵉ → is-prop-is-contrᵉ (Cᵉ xᵉ)))
    ( λ xᵉ → centerᵉ (Cᵉ xᵉ))
```