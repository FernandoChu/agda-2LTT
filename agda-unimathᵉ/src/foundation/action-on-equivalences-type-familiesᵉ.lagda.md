# Action on equivalences of type families

```agda
module foundation.action-on-equivalences-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Ideas

Anyᵉ familyᵉ ofᵉ typesᵉ `Bᵉ : 𝒰ᵉ → 𝒱`ᵉ overᵉ aᵉ universeᵉ `𝒰`ᵉ hasᵉ anᵉ **actionᵉ onᵉ
equivalences**ᵉ

```text
  (Aᵉ ≃ᵉ Bᵉ) → Pᵉ Aᵉ ≃ᵉ Pᵉ Bᵉ
```

obtainedᵉ byᵉ [equivalenceᵉ induction](foundation.equivalence-induction.md).ᵉ Theᵉ
acionᵉ onᵉ equivalencesᵉ ofᵉ aᵉ typeᵉ familyᵉ `B`ᵉ onᵉ aᵉ universeᵉ `𝒰`ᵉ isᵉ uniquelyᵉ
determinedᵉ byᵉ theᵉ identificationᵉ `Bᵉ id-equivᵉ ＝ᵉ id-equiv`,ᵉ andᵉ fitsᵉ in aᵉ
[commutingᵉ square](foundation.commuting-squares-of-maps.mdᵉ)

```text
                   apᵉ Bᵉ
        (Xᵉ ＝ᵉ Yᵉ) -------->ᵉ (Bᵉ Xᵉ ＝ᵉ Bᵉ Yᵉ)
           |                    |
  equiv-eqᵉ |                    | equiv-eqᵉ
           ∨ᵉ                    ∨ᵉ
        (Xᵉ ≃ᵉ Yᵉ) --------->ᵉ (Bᵉ Xᵉ ≃ᵉ Bᵉ Y).ᵉ
                     Bᵉ
```

**Note:**ᵉ Inᵉ generalᵉ --ᵉ in particularᵉ in ourᵉ generalᵉ constructionsᵉ belowᵉ --ᵉ weᵉ
needᵉ theᵉ [univalenceᵉ axiom](foundation.univalence.mdᵉ) to constructᵉ theᵉ actionᵉ onᵉ
equivalencesᵉ ofᵉ aᵉ familyᵉ ofᵉ types.ᵉ However,ᵉ forᵉ manyᵉ specificᵉ typeᵉ familiesᵉ thatᵉ
areᵉ definedᵉ in termsᵉ ofᵉ theᵉ basicᵉ typeᵉ constructors,ᵉ weᵉ canᵉ constructᵉ theᵉ actionᵉ
onᵉ equivalencesᵉ directlyᵉ withoutᵉ invokingᵉ theᵉ univalenceᵉ axiom.ᵉ

## Definitions

### The action on equivalences of a family of types over a universe

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Bᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  where

  abstract
    unique-action-equiv-familyᵉ :
      {Xᵉ : UUᵉ l1ᵉ} →
      is-contrᵉ (fiberᵉ (ev-id-equivᵉ (λ Yᵉ eᵉ → Bᵉ Xᵉ ≃ᵉ Bᵉ Yᵉ)) id-equivᵉ)
    unique-action-equiv-familyᵉ =
      is-contr-map-ev-id-equivᵉ (λ Yᵉ eᵉ → Bᵉ _ ≃ᵉ Bᵉ Yᵉ) id-equivᵉ

  action-equiv-familyᵉ :
    {Xᵉ Yᵉ : UUᵉ l1ᵉ} → (Xᵉ ≃ᵉ Yᵉ) → Bᵉ Xᵉ ≃ᵉ Bᵉ Yᵉ
  action-equiv-familyᵉ {Xᵉ} {Yᵉ} =
    equiv-eqᵉ ∘ᵉ action-equiv-functionᵉ Bᵉ

  compute-action-equiv-family-id-equivᵉ :
    {Xᵉ : UUᵉ l1ᵉ} →
    action-equiv-familyᵉ {Xᵉ} {Xᵉ} id-equivᵉ ＝ᵉ id-equivᵉ
  compute-action-equiv-family-id-equivᵉ {Xᵉ} =
    apᵉ equiv-eqᵉ (compute-action-equiv-function-id-equivᵉ Bᵉ Xᵉ)

  map-action-equiv-familyᵉ : {Xᵉ Yᵉ : UUᵉ l1ᵉ} → Xᵉ ≃ᵉ Yᵉ → Bᵉ Xᵉ → Bᵉ Yᵉ
  map-action-equiv-familyᵉ = map-equivᵉ ∘ᵉ action-equiv-familyᵉ
```

## Properties

### The action on equivalences of a family of types over a universe fits in a commuting square with `equiv-eq`

Weᵉ claimᵉ thatᵉ theᵉ squareᵉ

```text
                   apᵉ Bᵉ
        (Xᵉ ＝ᵉ Yᵉ) -------->ᵉ (Bᵉ Xᵉ ＝ᵉ Bᵉ Yᵉ)
           |                    |
  equiv-eqᵉ |                    | equiv-eqᵉ
           ∨ᵉ                    ∨ᵉ
        (Xᵉ ≃ᵉ Yᵉ) --------->ᵉ (Bᵉ Xᵉ ≃ᵉ Bᵉ Y).ᵉ
                     Bᵉ
```

commutesᵉ forᵉ anyᵉ twoᵉ typesᵉ `Xᵉ Yᵉ : 𝒰`ᵉ andᵉ anyᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `𝒰`.ᵉ

```agda
coherence-square-action-equiv-familyᵉ :
  {l1ᵉ l2ᵉ : Level} (Bᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) (Xᵉ Yᵉ : UUᵉ l1ᵉ) →
  coherence-square-mapsᵉ
    ( apᵉ Bᵉ {Xᵉ} {Yᵉ})
    ( equiv-eqᵉ)
    ( equiv-eqᵉ)
    ( action-equiv-familyᵉ Bᵉ)
coherence-square-action-equiv-familyᵉ Bᵉ Xᵉ .Xᵉ reflᵉ =
  compute-action-equiv-family-id-equivᵉ Bᵉ
```

### The identity function acts trivially on equivalences

```agda
compute-action-equiv-family-idᵉ :
  {lᵉ : Level} {Xᵉ Yᵉ : UUᵉ lᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (action-equiv-familyᵉ idᵉ eᵉ) ＝ᵉ eᵉ
compute-action-equiv-family-idᵉ eᵉ =
  apᵉ equiv-eqᵉ (ap-idᵉ (eq-equivᵉ eᵉ)) ∙ᵉ is-section-eq-equivᵉ eᵉ
```

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-family-constᵉ :
  {l1ᵉ l2ᵉ : Level} (Bᵉ : UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) → (action-equiv-familyᵉ (constᵉ (UUᵉ l1ᵉ) Bᵉ) eᵉ) ＝ᵉ id-equivᵉ
compute-action-equiv-family-constᵉ Bᵉ {Xᵉ} {Yᵉ} eᵉ =
  apᵉ equiv-eqᵉ (compute-action-equiv-function-constᵉ Bᵉ eᵉ)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
distributive-action-equiv-function-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Cᵉ : UUᵉ l3ᵉ} (gᵉ : UUᵉ l2ᵉ → Cᵉ) (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  {Xᵉ Yᵉ : UUᵉ l1ᵉ} →
  action-equiv-functionᵉ (gᵉ ∘ᵉ fᵉ) {Xᵉ} {Yᵉ} ~ᵉ
  action-equiv-functionᵉ gᵉ ∘ᵉ action-equiv-familyᵉ fᵉ
distributive-action-equiv-function-compᵉ gᵉ fᵉ eᵉ =
  ( ap-compᵉ gᵉ fᵉ (eq-equivᵉ eᵉ)) ∙ᵉ
  ( left-whisker-comp²ᵉ gᵉ
    ( inv-htpyᵉ is-retraction-eq-equivᵉ)
    ( action-equiv-functionᵉ fᵉ eᵉ))

distributive-action-equiv-family-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (gᵉ : UUᵉ l2ᵉ → UUᵉ l3ᵉ) (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ)
  {Xᵉ Yᵉ : UUᵉ l1ᵉ} →
  action-equiv-familyᵉ (gᵉ ∘ᵉ fᵉ) {Xᵉ} {Yᵉ} ~ᵉ
  action-equiv-familyᵉ gᵉ ∘ᵉ action-equiv-familyᵉ fᵉ
distributive-action-equiv-family-compᵉ gᵉ fᵉ eᵉ =
  apᵉ equiv-eqᵉ (distributive-action-equiv-function-compᵉ gᵉ fᵉ eᵉ)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-family-comp-equivᵉ :
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ Zᵉ : UUᵉ l1ᵉ} →
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) (e'ᵉ : Yᵉ ≃ᵉ Zᵉ) →
  action-equiv-familyᵉ fᵉ (e'ᵉ ∘eᵉ eᵉ) ＝ᵉ
  action-equiv-familyᵉ fᵉ e'ᵉ ∘eᵉ action-equiv-familyᵉ fᵉ eᵉ
distributive-action-equiv-family-comp-equivᵉ fᵉ eᵉ e'ᵉ =
  ( apᵉ equiv-eqᵉ (distributive-action-equiv-function-comp-equivᵉ fᵉ eᵉ e'ᵉ)) ∙ᵉ
  ( invᵉ
    ( compute-equiv-eq-concatᵉ
      ( action-equiv-functionᵉ fᵉ eᵉ)
      ( action-equiv-functionᵉ fᵉ e'ᵉ)))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-family-inv-equivᵉ :
  {l1ᵉ l2ᵉ : Level} (fᵉ : UUᵉ l1ᵉ → UUᵉ l2ᵉ) {Xᵉ Yᵉ : UUᵉ l1ᵉ}
  (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
  action-equiv-familyᵉ fᵉ (inv-equivᵉ eᵉ) ＝ᵉ inv-equivᵉ (action-equiv-familyᵉ fᵉ eᵉ)
compute-action-equiv-family-inv-equivᵉ fᵉ eᵉ =
  ( apᵉ equiv-eqᵉ (compute-action-equiv-function-inv-equivᵉ fᵉ eᵉ)) ∙ᵉ
  ( invᵉ (commutativity-inv-equiv-eqᵉ (action-equiv-functionᵉ fᵉ eᵉ)))
```