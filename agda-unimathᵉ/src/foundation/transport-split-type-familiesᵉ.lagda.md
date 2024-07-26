# Transport-split type families

```agda
module foundation.transport-split-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-equivalences-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalence-injective-type-familiesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.univalent-type-familiesᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "transport-split"ᵉ Disambiguation="typeᵉ family"ᵉ Agda=is-transport-splitᵉ}}
ifᵉ theᵉ mapᵉ

```text
  equiv-trᵉ Bᵉ : xᵉ ＝ᵉ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ
```

admitsᵉ aᵉ [section](foundation-core.sections.mdᵉ) forᵉ everyᵉ `xᵉ yᵉ : A`.ᵉ Byᵉ aᵉ
corollaryᵉ ofᵉ
[theᵉ fundamentalᵉ theoremᵉ ofᵉ identityᵉ types](foundation.fundamental-theorem-of-identity-types.mdᵉ)
everyᵉ transport-splitᵉ typeᵉ familyᵉ isᵉ
[univalent](foundation.univalent-type-families.md),ᵉ meaningᵉ thatᵉ `equiv-trᵉ B`ᵉ isᵉ
in factᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ allᵉ `xᵉ yᵉ : A`.ᵉ

## Definition

### Transport-split type families

```agda
is-transport-splitᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-transport-splitᵉ {Aᵉ = Aᵉ} Bᵉ =
  (xᵉ yᵉ : Aᵉ) → sectionᵉ (λ (pᵉ : xᵉ ＝ᵉ yᵉ) → equiv-trᵉ Bᵉ pᵉ)
```

## Properties

### Transport-split type families are equivalence injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-equivalence-injective-is-transport-splitᵉ :
    is-transport-splitᵉ Bᵉ → is-equivalence-injectiveᵉ Bᵉ
  is-equivalence-injective-is-transport-splitᵉ sᵉ {xᵉ} {yᵉ} =
    map-sectionᵉ (equiv-trᵉ Bᵉ) (sᵉ xᵉ yᵉ)
```

### Transport-split type families are univalent

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-transport-split-is-univalentᵉ :
    is-univalentᵉ Bᵉ → is-transport-splitᵉ Bᵉ
  is-transport-split-is-univalentᵉ Uᵉ xᵉ yᵉ = section-is-equivᵉ (Uᵉ xᵉ yᵉ)

  is-univalent-is-transport-splitᵉ :
    is-transport-splitᵉ Bᵉ → is-univalentᵉ Bᵉ
  is-univalent-is-transport-splitᵉ sᵉ xᵉ =
    fundamental-theorem-id-sectionᵉ xᵉ (λ yᵉ → equiv-trᵉ Bᵉ) (sᵉ xᵉ)
```

### The type `is-transport-split` is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-proof-irrelevant-is-transport-splitᵉ :
    is-proof-irrelevantᵉ (is-transport-splitᵉ Bᵉ)
  is-proof-irrelevant-is-transport-splitᵉ sᵉ =
    is-contr-iterated-Πᵉ 2
      ( λ xᵉ yᵉ →
        is-contr-section-is-equivᵉ (is-univalent-is-transport-splitᵉ sᵉ xᵉ yᵉ))

  is-prop-is-transport-splitᵉ :
    is-propᵉ (is-transport-splitᵉ Bᵉ)
  is-prop-is-transport-splitᵉ =
    is-prop-is-proof-irrelevantᵉ is-proof-irrelevant-is-transport-splitᵉ
```

### Assuming the univalence axiom, type families are transport-split if and only if they are embeddings as maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-emb-is-transport-splitᵉ : is-transport-splitᵉ Bᵉ → is-embᵉ Bᵉ
  is-emb-is-transport-splitᵉ sᵉ =
    is-emb-is-univalentᵉ (is-univalent-is-transport-splitᵉ sᵉ)

  is-transport-split-is-embᵉ : is-embᵉ Bᵉ → is-transport-splitᵉ Bᵉ
  is-transport-split-is-embᵉ Hᵉ =
    is-transport-split-is-univalentᵉ (is-univalent-is-embᵉ Hᵉ)
```

### Transport-split type families satisfy equivalence induction

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (sᵉ : is-transport-splitᵉ Bᵉ)
  where

  is-torsorial-fam-equiv-is-transport-splitᵉ :
    {xᵉ : Aᵉ} → is-torsorialᵉ (λ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ)
  is-torsorial-fam-equiv-is-transport-splitᵉ =
    is-torsorial-fam-equiv-is-univalentᵉ (is-univalent-is-transport-splitᵉ sᵉ)

  dependent-universal-property-identity-system-fam-equiv-is-transport-splitᵉ :
    {xᵉ : Aᵉ} →
    dependent-universal-property-identity-systemᵉ (λ yᵉ → Bᵉ xᵉ ≃ᵉ Bᵉ yᵉ) id-equivᵉ
  dependent-universal-property-identity-system-fam-equiv-is-transport-splitᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( id-equivᵉ)
      ( is-torsorial-fam-equiv-is-transport-splitᵉ)
```

## See also

-ᵉ [Univalentᵉ typeᵉ families](foundation.univalent-type-families.mdᵉ)
-ᵉ [Preunivalentᵉ typeᵉ families](foundation.preunivalent-type-families.mdᵉ)