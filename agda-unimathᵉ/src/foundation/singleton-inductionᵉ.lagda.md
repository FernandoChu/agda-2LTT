# Singleton induction

```agda
module foundation.singleton-inductionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

**Singletonᵉ induction**ᵉ onᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with aᵉ pointᵉ `aᵉ : A`ᵉ isᵉ aᵉ
principleᵉ analogousᵉ to theᵉ inductionᵉ principleᵉ ofᵉ theᵉ
[unitᵉ type](foundation.unit-type.md).ᵉ Aᵉ typeᵉ satisfiesᵉ singletonᵉ inductionᵉ ifᵉ
andᵉ onlyᵉ ifᵉ itᵉ isᵉ [contractible](foundation-core.contractible-types.md).ᵉ

Singletonᵉ inductionᵉ statesᵉ thatᵉ givenᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ to constructᵉ aᵉ
sectionᵉ ofᵉ `B`ᵉ itᵉ sufficesᵉ to constructᵉ anᵉ elementᵉ in `Bᵉ a`.ᵉ

## Definition

### Singleton induction

```agda
is-singletonᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} (Aᵉ : UUᵉ l2ᵉ) → Aᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
is-singletonᵉ lᵉ Aᵉ aᵉ = (Bᵉ : Aᵉ → UUᵉ lᵉ) → sectionᵉ (ev-pointᵉ aᵉ {Bᵉ})

ind-is-singletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) →
  ({lᵉ : Level} → is-singletonᵉ lᵉ Aᵉ aᵉ) → (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ
ind-is-singletonᵉ aᵉ is-sing-Aᵉ Bᵉ = pr1ᵉ (is-sing-Aᵉ Bᵉ)

compute-ind-is-singletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) (Hᵉ : {lᵉ : Level} → is-singletonᵉ lᵉ Aᵉ aᵉ) →
  (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → (ev-pointᵉ aᵉ {Bᵉ} ∘ᵉ ind-is-singletonᵉ aᵉ Hᵉ Bᵉ) ~ᵉ idᵉ
compute-ind-is-singletonᵉ aᵉ Hᵉ Bᵉ = pr2ᵉ (Hᵉ Bᵉ)
```

## Properties

### Contractible types satisfy singleton induction

```agda
ind-singletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) (is-contr-Aᵉ : is-contrᵉ Aᵉ)
  (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ
ind-singletonᵉ aᵉ is-contr-Aᵉ Bᵉ bᵉ xᵉ =
  trᵉ Bᵉ (invᵉ (contractionᵉ is-contr-Aᵉ aᵉ) ∙ᵉ contractionᵉ is-contr-Aᵉ xᵉ) bᵉ

compute-ind-singletonᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (aᵉ : Aᵉ) (is-contr-Aᵉ : is-contrᵉ Aᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  (ev-pointᵉ aᵉ {Bᵉ} ∘ᵉ ind-singletonᵉ aᵉ is-contr-Aᵉ Bᵉ) ~ᵉ idᵉ
compute-ind-singletonᵉ aᵉ is-contr-Aᵉ Bᵉ bᵉ =
  apᵉ (λ pᵉ → trᵉ Bᵉ pᵉ bᵉ) (left-invᵉ (contractionᵉ is-contr-Aᵉ aᵉ))
```

### A type satisfies singleton induction if and only if it is contractible

```agda
is-singleton-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) → is-contrᵉ Aᵉ → is-singletonᵉ l2ᵉ Aᵉ aᵉ
pr1ᵉ (is-singleton-is-contrᵉ aᵉ is-contr-Aᵉ Bᵉ) =
  ind-singletonᵉ aᵉ is-contr-Aᵉ Bᵉ
pr2ᵉ (is-singleton-is-contrᵉ aᵉ is-contr-Aᵉ Bᵉ) =
  compute-ind-singletonᵉ aᵉ is-contr-Aᵉ Bᵉ

abstract
  is-contr-ind-singletonᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (aᵉ : Aᵉ) →
    ({l2ᵉ : Level} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → Bᵉ aᵉ → (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-contrᵉ Aᵉ
  pr1ᵉ (is-contr-ind-singletonᵉ Aᵉ aᵉ Sᵉ) = aᵉ
  pr2ᵉ (is-contr-ind-singletonᵉ Aᵉ aᵉ Sᵉ) = Sᵉ (λ xᵉ → aᵉ ＝ᵉ xᵉ) reflᵉ

abstract
  is-contr-is-singletonᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (aᵉ : Aᵉ) →
    ({l2ᵉ : Level} → is-singletonᵉ l2ᵉ Aᵉ aᵉ) → is-contrᵉ Aᵉ
  is-contr-is-singletonᵉ Aᵉ aᵉ Sᵉ = is-contr-ind-singletonᵉ Aᵉ aᵉ (pr1ᵉ ∘ᵉ Sᵉ)
```

## Examples

### The total space of an identity type satisfies singleton induction

```agda
abstract
  is-singleton-total-pathᵉ :
    {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (aᵉ : Aᵉ) →
    is-singletonᵉ l2ᵉ (Σᵉ Aᵉ (λ xᵉ → aᵉ ＝ᵉ xᵉ)) (aᵉ ,ᵉ reflᵉ)
  pr1ᵉ (is-singleton-total-pathᵉ Aᵉ aᵉ Bᵉ) = ind-Σᵉ ∘ᵉ ind-Idᵉ aᵉ _
  pr2ᵉ (is-singleton-total-pathᵉ Aᵉ aᵉ Bᵉ) = refl-htpyᵉ
```

## See also

-ᵉ Theᵉ equivalentᵉ principleᵉ ofᵉ
  [subsingletonᵉ induction](foundation.subsingleton-induction.mdᵉ)
-ᵉ [Singletonᵉ subsets](foundation.singleton-subtypes.mdᵉ)