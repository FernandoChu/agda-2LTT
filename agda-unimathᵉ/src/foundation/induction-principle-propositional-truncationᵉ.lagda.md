# The induction principle for propositional truncation

```agda
module foundation.induction-principle-propositional-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ inductionᵉ principleᵉ forᵉ theᵉ propositionalᵉ truncationsᵉ presentᵉ propositionalᵉ
truncationsᵉ asᵉ higherᵉ inductive types.ᵉ

## Definition

```agda
case-paths-induction-principle-propositional-truncationᵉ :
  { lᵉ : Level} {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( Pᵉ : Propᵉ l2ᵉ) (αᵉ : (pᵉ qᵉ : type-Propᵉ Pᵉ) → pᵉ ＝ᵉ qᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
  ( Bᵉ : type-Propᵉ Pᵉ → UUᵉ lᵉ) → UUᵉ (lᵉ ⊔ l2ᵉ)
case-paths-induction-principle-propositional-truncationᵉ Pᵉ αᵉ fᵉ Bᵉ =
  (pᵉ qᵉ : type-Propᵉ Pᵉ) (xᵉ : Bᵉ pᵉ) (yᵉ : Bᵉ qᵉ) → trᵉ Bᵉ (αᵉ pᵉ qᵉ) xᵉ ＝ᵉ yᵉ

induction-principle-propositional-truncationᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Pᵉ : Propᵉ l2ᵉ) (αᵉ : (pᵉ qᵉ : type-Propᵉ Pᵉ) → pᵉ ＝ᵉ qᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
  UUᵉ (lsuc lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
induction-principle-propositional-truncationᵉ lᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} Pᵉ αᵉ fᵉ =
  ( Bᵉ : type-Propᵉ Pᵉ → UUᵉ lᵉ) →
  ( gᵉ : (xᵉ : Aᵉ) → (Bᵉ (fᵉ xᵉ))) →
  ( βᵉ : case-paths-induction-principle-propositional-truncationᵉ Pᵉ αᵉ fᵉ Bᵉ) →
  Σᵉ ((pᵉ : type-Propᵉ Pᵉ) → Bᵉ pᵉ) (λ hᵉ → (xᵉ : Aᵉ) → hᵉ (fᵉ xᵉ) ＝ᵉ gᵉ xᵉ)
```

## Properties

### A type family over the propositional truncation comes equipped with the structure to satisfy the path clause of the induction principle if and only if it is a family of propositions

```agda
abstract
  is-prop-case-paths-induction-principle-propositional-truncationᵉ :
    { lᵉ : Level} {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
    ( Pᵉ : Propᵉ l2ᵉ) (αᵉ : (pᵉ qᵉ : type-Propᵉ Pᵉ) → pᵉ ＝ᵉ qᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    ( Bᵉ : type-Propᵉ Pᵉ → UUᵉ lᵉ) →
    case-paths-induction-principle-propositional-truncationᵉ Pᵉ αᵉ fᵉ Bᵉ →
    ( pᵉ : type-Propᵉ Pᵉ) → is-propᵉ (Bᵉ pᵉ)
  is-prop-case-paths-induction-principle-propositional-truncationᵉ Pᵉ αᵉ fᵉ Bᵉ βᵉ pᵉ =
    is-prop-is-proof-irrelevantᵉ (λ xᵉ → pairᵉ (trᵉ Bᵉ (αᵉ pᵉ pᵉ) xᵉ) (βᵉ pᵉ pᵉ xᵉ))

  case-paths-induction-principle-propositional-truncation-is-propᵉ :
    { lᵉ : Level} {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
    ( Pᵉ : Propᵉ l2ᵉ) (αᵉ : (pᵉ qᵉ : type-Propᵉ Pᵉ) → pᵉ ＝ᵉ qᵉ) (fᵉ : Aᵉ → type-Propᵉ Pᵉ) →
    ( Bᵉ : type-Propᵉ Pᵉ → UUᵉ lᵉ) →
    ( (pᵉ : type-Propᵉ Pᵉ) → is-propᵉ (Bᵉ pᵉ)) →
    case-paths-induction-principle-propositional-truncationᵉ Pᵉ αᵉ fᵉ Bᵉ
  case-paths-induction-principle-propositional-truncation-is-propᵉ
    Pᵉ αᵉ fᵉ Bᵉ is-prop-Bᵉ pᵉ qᵉ xᵉ yᵉ =
    eq-is-propᵉ (is-prop-Bᵉ qᵉ)
```