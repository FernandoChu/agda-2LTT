# Action on equivalences of functions

```agda
module foundation.action-on-equivalences-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ mapᵉ betweenᵉ universesᵉ `fᵉ : 𝒰ᵉ → 𝒱`,ᵉ thenᵉ applyingᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
to [identifications](foundation-core.identity-types.mdᵉ) arisingᵉ fromᵉ theᵉ
[univalenceᵉ axiom](foundation.univalence.mdᵉ) givesᵉ usᵉ theᵉ
{{#conceptᵉ "actionᵉ onᵉ equivalences"ᵉ Agda=action-equiv-functionᵉ}}

```text
  action-equiv-functionᵉ fᵉ : Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ≃ᵉ fᵉ Y.ᵉ
```

Alternatively,ᵉ oneᵉ canᵉ applyᵉ
[transportᵉ alongᵉ identifications](foundation-core.transport-along-identifications.mdᵉ)
to getᵉ
[transportᵉ alongᵉ equivalences](foundation.transport-along-equivalences.md).ᵉ
However,ᵉ byᵉ univalenceᵉ suchᵉ anᵉ actionᵉ mustᵉ alsoᵉ beᵉ unique,ᵉ henceᵉ theseᵉ twoᵉ
constructionsᵉ coincide.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : UUᵉ l1ᵉ → Bᵉ)
  where

  abstract
    unique-action-equiv-functionᵉ :
      (Xᵉ : UUᵉ l1ᵉ) →
      is-contrᵉ
        ( Σᵉ ((Yᵉ : UUᵉ l1ᵉ) → Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ) (λ hᵉ → hᵉ Xᵉ id-equivᵉ ＝ᵉ reflᵉ))
    unique-action-equiv-functionᵉ Xᵉ =
      is-contr-map-ev-id-equivᵉ (λ Yᵉ eᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ) reflᵉ

  action-equiv-functionᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → Xᵉ ≃ᵉ Yᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ
  action-equiv-functionᵉ eᵉ = apᵉ fᵉ (eq-equivᵉ eᵉ)

  compute-action-equiv-function-id-equivᵉ :
    (Xᵉ : UUᵉ l1ᵉ) → action-equiv-functionᵉ id-equivᵉ ＝ᵉ reflᵉ
  compute-action-equiv-function-id-equivᵉ Xᵉ =
    ap²ᵉ fᵉ (compute-eq-equiv-id-equivᵉ Xᵉ)
```

## Properties

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-function-constᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} (bᵉ : Bᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (action-equiv-functionᵉ (constᵉ (UUᵉ l1ᵉ) bᵉ) eᵉ) ＝ᵉ reflᵉ
compute-action-equiv-function-constᵉ bᵉ eᵉ = ap-constᵉ bᵉ (eq-equivᵉ eᵉ)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-function-comp-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : UUᵉ l1ᵉ → Bᵉ) {Xᵉ Yᵉ Zᵉ : UUᵉ l1ᵉ} →
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) (e'ᵉ : Yᵉ ≃ᵉ Zᵉ) →
  action-equiv-functionᵉ fᵉ (e'ᵉ ∘eᵉ eᵉ) ＝ᵉ
  action-equiv-functionᵉ fᵉ eᵉ ∙ᵉ action-equiv-functionᵉ fᵉ e'ᵉ
distributive-action-equiv-function-comp-equivᵉ fᵉ eᵉ e'ᵉ =
    ( ap²ᵉ fᵉ (invᵉ (compute-eq-equiv-comp-equivᵉ eᵉ e'ᵉ))) ∙ᵉ
    ( ap-concatᵉ fᵉ (eq-equivᵉ eᵉ) (eq-equivᵉ e'ᵉ))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-function-inv-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : UUᵉ l1ᵉ → Bᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
  action-equiv-functionᵉ fᵉ (inv-equivᵉ eᵉ) ＝ᵉ invᵉ (action-equiv-functionᵉ fᵉ eᵉ)
compute-action-equiv-function-inv-equivᵉ fᵉ eᵉ =
  ( ap²ᵉ fᵉ (invᵉ (commutativity-inv-eq-equivᵉ eᵉ))) ∙ᵉ
  ( ap-invᵉ fᵉ (eq-equivᵉ eᵉ))
```