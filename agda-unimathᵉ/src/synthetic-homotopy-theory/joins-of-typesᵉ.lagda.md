# Joins of types

```agda
module synthetic-homotopy-theory.joins-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "join"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=_*ᵉ_}} ofᵉ `A`ᵉ andᵉ `B`ᵉ isᵉ theᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ
[span](foundation.spans.mdᵉ) `Aᵉ ←ᵉ Aᵉ ×ᵉ Bᵉ → B`.ᵉ

## Definitions

### The standard join of types

```agda
joinᵉ : {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
joinᵉ Aᵉ Bᵉ = pushoutᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} pr1ᵉ pr2ᵉ

infixr 15 _*ᵉ_
_*ᵉ_ = joinᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  cocone-joinᵉ : coconeᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} pr1ᵉ pr2ᵉ (Aᵉ *ᵉ Bᵉ)
  cocone-joinᵉ = cocone-pushoutᵉ pr1ᵉ pr2ᵉ

  inl-joinᵉ : Aᵉ → Aᵉ *ᵉ Bᵉ
  inl-joinᵉ = horizontal-map-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ

  inr-joinᵉ : Bᵉ → Aᵉ *ᵉ Bᵉ
  inr-joinᵉ = vertical-map-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ

  glue-joinᵉ : (tᵉ : Aᵉ ×ᵉ Bᵉ) → inl-joinᵉ (pr1ᵉ tᵉ) ＝ᵉ inr-joinᵉ (pr2ᵉ tᵉ)
  glue-joinᵉ = coherence-square-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ
```

### The universal property of the join

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  up-joinᵉ : universal-property-pushoutᵉ {Aᵉ = Aᵉ} {Bᵉ} pr1ᵉ pr2ᵉ cocone-joinᵉ
  up-joinᵉ = up-pushoutᵉ pr1ᵉ pr2ᵉ

  equiv-up-joinᵉ :
    {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → (Aᵉ *ᵉ Bᵉ → Xᵉ) ≃ᵉ coconeᵉ pr1ᵉ pr2ᵉ Xᵉ
  equiv-up-joinᵉ = equiv-up-pushoutᵉ pr1ᵉ pr2ᵉ
```

### The dependent cogap map of the join

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Pᵉ : Aᵉ *ᵉ Bᵉ → UUᵉ l3ᵉ}
  (cᵉ : dependent-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ Pᵉ)
  where

  dependent-cogap-joinᵉ : (xᵉ : Aᵉ *ᵉ Bᵉ) → Pᵉ xᵉ
  dependent-cogap-joinᵉ = dependent-cogapᵉ pr1ᵉ pr2ᵉ {Pᵉ = Pᵉ} cᵉ

  compute-inl-dependent-cogap-joinᵉ :
    dependent-cogap-joinᵉ ∘ᵉ inl-joinᵉ ~ᵉ
    horizontal-map-dependent-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ Pᵉ cᵉ
  compute-inl-dependent-cogap-joinᵉ = compute-inl-dependent-cogapᵉ pr1ᵉ pr2ᵉ cᵉ

  compute-inr-dependent-cogap-joinᵉ :
    dependent-cogap-joinᵉ ∘ᵉ inr-joinᵉ ~ᵉ
    vertical-map-dependent-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ Pᵉ cᵉ
  compute-inr-dependent-cogap-joinᵉ = compute-inr-dependent-cogapᵉ pr1ᵉ pr2ᵉ cᵉ

  compute-glue-dependent-cogap-joinᵉ :
    coherence-htpy-dependent-coconeᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ Pᵉ
      ( dependent-cocone-mapᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ Pᵉ dependent-cogap-joinᵉ)
      ( cᵉ)
      ( compute-inl-dependent-cogap-joinᵉ)
      ( compute-inr-dependent-cogap-joinᵉ)
  compute-glue-dependent-cogap-joinᵉ = compute-glue-dependent-cogapᵉ pr1ᵉ pr2ᵉ cᵉ
```

### The cogap map of the join

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  cogap-joinᵉ :
    {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → coconeᵉ pr1ᵉ pr2ᵉ Xᵉ → Aᵉ *ᵉ Bᵉ → Xᵉ
  cogap-joinᵉ Xᵉ = cogapᵉ pr1ᵉ pr2ᵉ

  compute-inl-cogap-joinᵉ :
    {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coconeᵉ pr1ᵉ pr2ᵉ Xᵉ) →
    cogap-joinᵉ Xᵉ cᵉ ∘ᵉ inl-joinᵉ ~ᵉ horizontal-map-coconeᵉ pr1ᵉ pr2ᵉ cᵉ
  compute-inl-cogap-joinᵉ = compute-inl-cogapᵉ pr1ᵉ pr2ᵉ

  compute-inr-cogap-joinᵉ :
    {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coconeᵉ pr1ᵉ pr2ᵉ Xᵉ) →
    cogap-joinᵉ Xᵉ cᵉ ∘ᵉ inr-joinᵉ ~ᵉ vertical-map-coconeᵉ pr1ᵉ pr2ᵉ cᵉ
  compute-inr-cogap-joinᵉ = compute-inr-cogapᵉ pr1ᵉ pr2ᵉ

  compute-glue-cogap-joinᵉ :
    {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coconeᵉ pr1ᵉ pr2ᵉ Xᵉ) →
    statement-coherence-htpy-coconeᵉ pr1ᵉ pr2ᵉ
      ( cocone-mapᵉ pr1ᵉ pr2ᵉ cocone-joinᵉ (cogap-joinᵉ Xᵉ cᵉ))
      ( cᵉ)
      ( compute-inl-cogap-joinᵉ cᵉ)
      ( compute-inr-cogap-joinᵉ cᵉ)
  compute-glue-cogap-joinᵉ = compute-glue-cogapᵉ pr1ᵉ pr2ᵉ
```

## Properties

### The left unit law for joins

```agda
is-equiv-inr-join-emptyᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (inr-joinᵉ {Aᵉ = emptyᵉ} {Bᵉ = Xᵉ})
is-equiv-inr-join-emptyᵉ Xᵉ =
  is-equiv-universal-property-pushoutᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr1-product-emptyᵉ Xᵉ)
    ( up-joinᵉ)

left-unit-law-joinᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → Xᵉ ≃ᵉ (emptyᵉ *ᵉ Xᵉ)
pr1ᵉ (left-unit-law-joinᵉ Xᵉ) = inr-joinᵉ
pr2ᵉ (left-unit-law-joinᵉ Xᵉ) = is-equiv-inr-join-emptyᵉ Xᵉ

is-equiv-inr-join-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-emptyᵉ Aᵉ → is-equivᵉ (inr-joinᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
is-equiv-inr-join-is-emptyᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} is-empty-Aᵉ =
  is-equiv-universal-property-pushoutᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr1-product-is-emptyᵉ Aᵉ Bᵉ is-empty-Aᵉ)
    ( up-joinᵉ)

left-unit-law-join-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-emptyᵉ Aᵉ → Bᵉ ≃ᵉ (Aᵉ *ᵉ Bᵉ)
pr1ᵉ (left-unit-law-join-is-emptyᵉ is-empty-Aᵉ) = inr-joinᵉ
pr2ᵉ (left-unit-law-join-is-emptyᵉ is-empty-Aᵉ) =
  is-equiv-inr-join-is-emptyᵉ is-empty-Aᵉ
```

### The right unit law for joins

```agda
is-equiv-inl-join-emptyᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (inl-joinᵉ {Aᵉ = Xᵉ} {Bᵉ = emptyᵉ})
is-equiv-inl-join-emptyᵉ Xᵉ =
  is-equiv-universal-property-pushout'ᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr2-product-emptyᵉ Xᵉ)
    ( up-joinᵉ)

right-unit-law-joinᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → Xᵉ ≃ᵉ (Xᵉ *ᵉ emptyᵉ)
pr1ᵉ (right-unit-law-joinᵉ Xᵉ) = inl-joinᵉ
pr2ᵉ (right-unit-law-joinᵉ Xᵉ) = is-equiv-inl-join-emptyᵉ Xᵉ

is-equiv-inl-join-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-emptyᵉ Bᵉ → is-equivᵉ (inl-joinᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
is-equiv-inl-join-is-emptyᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} is-empty-Bᵉ =
  is-equiv-universal-property-pushout'ᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr2-product-is-emptyᵉ Aᵉ Bᵉ is-empty-Bᵉ)
    ( up-joinᵉ)

right-unit-law-join-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-emptyᵉ Bᵉ → Aᵉ ≃ᵉ (Aᵉ *ᵉ Bᵉ)
pr1ᵉ (right-unit-law-join-is-emptyᵉ is-empty-Bᵉ) = inl-joinᵉ
pr2ᵉ (right-unit-law-join-is-emptyᵉ is-empty-Bᵉ) =
  is-equiv-inl-join-is-emptyᵉ is-empty-Bᵉ

map-inv-right-unit-law-join-is-emptyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-emptyᵉ Bᵉ → Aᵉ *ᵉ Bᵉ → Aᵉ
map-inv-right-unit-law-join-is-emptyᵉ Hᵉ =
  map-inv-equivᵉ (right-unit-law-join-is-emptyᵉ Hᵉ)
```

### The left zero law for joins

```agda
is-equiv-inl-join-unitᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (inl-joinᵉ {Aᵉ = unitᵉ} {Bᵉ = Xᵉ})
is-equiv-inl-join-unitᵉ Xᵉ =
  is-equiv-universal-property-pushout'ᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-map-left-unit-law-productᵉ)
    ( up-joinᵉ)

left-zero-law-joinᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-contrᵉ (unitᵉ *ᵉ Xᵉ)
left-zero-law-joinᵉ Xᵉ =
  is-contr-equiv'ᵉ
    ( unitᵉ)
    ( inl-joinᵉ ,ᵉ is-equiv-inl-join-unitᵉ Xᵉ)
    ( is-contr-unitᵉ)

is-equiv-inl-join-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  is-contrᵉ Aᵉ → is-equivᵉ (inl-joinᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
is-equiv-inl-join-is-contrᵉ Aᵉ Bᵉ is-contr-Aᵉ =
  is-equiv-universal-property-pushout'ᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr2-product-is-contrᵉ is-contr-Aᵉ)
    ( up-joinᵉ)

left-zero-law-join-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → is-contrᵉ Aᵉ → is-contrᵉ (Aᵉ *ᵉ Bᵉ)
left-zero-law-join-is-contrᵉ Aᵉ Bᵉ is-contr-Aᵉ =
  is-contr-equiv'ᵉ
    ( Aᵉ)
    ( inl-joinᵉ ,ᵉ is-equiv-inl-join-is-contrᵉ Aᵉ Bᵉ is-contr-Aᵉ)
    ( is-contr-Aᵉ)
```

### The right zero law for joins

```agda
is-equiv-inr-join-unitᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (inr-joinᵉ {Aᵉ = Xᵉ} {Bᵉ = unitᵉ})
is-equiv-inr-join-unitᵉ Xᵉ =
  is-equiv-universal-property-pushoutᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-map-right-unit-law-productᵉ)
    ( up-joinᵉ)

right-zero-law-joinᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-contrᵉ (Xᵉ *ᵉ unitᵉ)
right-zero-law-joinᵉ Xᵉ =
  is-contr-equiv'ᵉ
    ( unitᵉ)
    ( inr-joinᵉ ,ᵉ is-equiv-inr-join-unitᵉ Xᵉ)
    ( is-contr-unitᵉ)

is-equiv-inr-join-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) →
  is-contrᵉ Bᵉ → is-equivᵉ (inr-joinᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
is-equiv-inr-join-is-contrᵉ Aᵉ Bᵉ is-contr-Bᵉ =
  is-equiv-universal-property-pushoutᵉ
    ( pr1ᵉ)
    ( pr2ᵉ)
    ( cocone-joinᵉ)
    ( is-equiv-pr1-is-contrᵉ (λ _ → is-contr-Bᵉ))
    ( up-joinᵉ)

right-zero-law-join-is-contrᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → is-contrᵉ Bᵉ → is-contrᵉ (Aᵉ *ᵉ Bᵉ)
right-zero-law-join-is-contrᵉ Aᵉ Bᵉ is-contr-Bᵉ =
  is-contr-equiv'ᵉ
    ( Bᵉ)
    ( inr-joinᵉ ,ᵉ is-equiv-inr-join-is-contrᵉ Aᵉ Bᵉ is-contr-Bᵉ)
    ( is-contr-Bᵉ)
```

### The join of propositions is a proposition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-proof-irrelevant-join-is-proof-irrelevantᵉ :
    is-proof-irrelevantᵉ Aᵉ → is-proof-irrelevantᵉ Bᵉ → is-proof-irrelevantᵉ (Aᵉ *ᵉ Bᵉ)
  is-proof-irrelevant-join-is-proof-irrelevantᵉ
    is-proof-irrelevant-Aᵉ is-proof-irrelevant-Bᵉ =
    cogap-joinᵉ
      ( is-contrᵉ (Aᵉ *ᵉ Bᵉ))
      ( ( left-zero-law-join-is-contrᵉ Aᵉ Bᵉ ∘ᵉ is-proof-irrelevant-Aᵉ) ,ᵉ
        ( right-zero-law-join-is-contrᵉ Aᵉ Bᵉ ∘ᵉ is-proof-irrelevant-Bᵉ) ,ᵉ
        ( λ (aᵉ ,ᵉ bᵉ) →
          centerᵉ
            ( is-property-is-contrᵉ
              ( left-zero-law-join-is-contrᵉ Aᵉ Bᵉ (is-proof-irrelevant-Aᵉ aᵉ))
              ( right-zero-law-join-is-contrᵉ Aᵉ Bᵉ (is-proof-irrelevant-Bᵉ bᵉ)))))

  is-prop-join-is-propᵉ :
    is-propᵉ Aᵉ → is-propᵉ Bᵉ → is-propᵉ (Aᵉ *ᵉ Bᵉ)
  is-prop-join-is-propᵉ is-prop-Aᵉ is-prop-Bᵉ =
    is-prop-is-proof-irrelevantᵉ
      ( is-proof-irrelevant-join-is-proof-irrelevantᵉ
        ( is-proof-irrelevant-is-propᵉ is-prop-Aᵉ)
        ( is-proof-irrelevant-is-propᵉ is-prop-Bᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  join-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ join-Propᵉ = (type-Propᵉ Pᵉ) *ᵉ (type-Propᵉ Qᵉ)
  pr2ᵉ join-Propᵉ =
    is-prop-join-is-propᵉ (is-prop-type-Propᵉ Pᵉ) (is-prop-type-Propᵉ Qᵉ)

  type-join-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-join-Propᵉ = type-Propᵉ join-Propᵉ

  is-prop-type-join-Propᵉ : is-propᵉ type-join-Propᵉ
  is-prop-type-join-Propᵉ = is-prop-type-Propᵉ join-Propᵉ

  inl-join-Propᵉ : type-hom-Propᵉ Pᵉ join-Propᵉ
  inl-join-Propᵉ = inl-joinᵉ

  inr-join-Propᵉ : type-hom-Propᵉ Qᵉ join-Propᵉ
  inr-join-Propᵉ = inr-joinᵉ
```

### Disjunction is the join of propositions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Propᵉ l1ᵉ) (Bᵉ : Propᵉ l2ᵉ)
  where

  cocone-disjunctionᵉ : coconeᵉ pr1ᵉ pr2ᵉ (type-disjunction-Propᵉ Aᵉ Bᵉ)
  pr1ᵉ cocone-disjunctionᵉ = inl-disjunctionᵉ
  pr1ᵉ (pr2ᵉ cocone-disjunctionᵉ) = inr-disjunctionᵉ
  pr2ᵉ (pr2ᵉ cocone-disjunctionᵉ) (aᵉ ,ᵉ bᵉ) =
    eq-is-prop'ᵉ
      ( is-prop-disjunction-Propᵉ Aᵉ Bᵉ)
      ( inl-disjunctionᵉ aᵉ)
      ( inr-disjunctionᵉ bᵉ)

  map-disjunction-join-Propᵉ : type-join-Propᵉ Aᵉ Bᵉ → type-disjunction-Propᵉ Aᵉ Bᵉ
  map-disjunction-join-Propᵉ =
    cogap-joinᵉ (type-disjunction-Propᵉ Aᵉ Bᵉ) cocone-disjunctionᵉ

  map-join-disjunction-Propᵉ : type-disjunction-Propᵉ Aᵉ Bᵉ → type-join-Propᵉ Aᵉ Bᵉ
  map-join-disjunction-Propᵉ =
    elim-disjunctionᵉ
      ( join-Propᵉ Aᵉ Bᵉ)
      ( inl-join-Propᵉ Aᵉ Bᵉ)
      ( inr-join-Propᵉ Aᵉ Bᵉ)

  is-equiv-map-disjunction-join-Propᵉ : is-equivᵉ map-disjunction-join-Propᵉ
  is-equiv-map-disjunction-join-Propᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-join-Propᵉ Aᵉ Bᵉ)
      ( is-prop-disjunction-Propᵉ Aᵉ Bᵉ)
      ( map-join-disjunction-Propᵉ)

  equiv-disjunction-join-Propᵉ :
    (type-join-Propᵉ Aᵉ Bᵉ) ≃ᵉ (type-disjunction-Propᵉ Aᵉ Bᵉ)
  pr1ᵉ equiv-disjunction-join-Propᵉ = map-disjunction-join-Propᵉ
  pr2ᵉ equiv-disjunction-join-Propᵉ = is-equiv-map-disjunction-join-Propᵉ

  is-equiv-map-join-disjunction-Propᵉ : is-equivᵉ map-join-disjunction-Propᵉ
  is-equiv-map-join-disjunction-Propᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-disjunction-Propᵉ Aᵉ Bᵉ)
      ( is-prop-type-join-Propᵉ Aᵉ Bᵉ)
      ( map-disjunction-join-Propᵉ)

  equiv-join-disjunction-Propᵉ :
    (type-disjunction-Propᵉ Aᵉ Bᵉ) ≃ᵉ (type-join-Propᵉ Aᵉ Bᵉ)
  pr1ᵉ equiv-join-disjunction-Propᵉ = map-join-disjunction-Propᵉ
  pr2ᵉ equiv-join-disjunction-Propᵉ = is-equiv-map-join-disjunction-Propᵉ

  up-join-disjunctionᵉ : universal-property-pushoutᵉ pr1ᵉ pr2ᵉ cocone-disjunctionᵉ
  up-join-disjunctionᵉ =
    up-pushout-up-pushout-is-equivᵉ
      ( pr1ᵉ)
      ( pr2ᵉ)
      ( cocone-joinᵉ)
      ( cocone-disjunctionᵉ)
      ( map-disjunction-join-Propᵉ)
      ( ( λ _ → eq-is-propᵉ (is-prop-disjunction-Propᵉ Aᵉ Bᵉ)) ,ᵉ
        ( λ _ → eq-is-propᵉ (is-prop-disjunction-Propᵉ Aᵉ Bᵉ)) ,ᵉ
        ( λ (aᵉ ,ᵉ bᵉ) →
          eq-is-contrᵉ
            ( is-prop-disjunction-Propᵉ Aᵉ Bᵉ
              ( horizontal-map-coconeᵉ pr1ᵉ pr2ᵉ
                ( cocone-mapᵉ pr1ᵉ pr2ᵉ
                  ( cocone-joinᵉ)
                  ( map-disjunction-join-Propᵉ))
                ( aᵉ))
              ( vertical-map-coconeᵉ pr1ᵉ pr2ᵉ cocone-disjunctionᵉ bᵉ))))
      ( is-equiv-map-disjunction-join-Propᵉ)
      ( up-joinᵉ)
```

## See also

-ᵉ [Joinsᵉ ofᵉ maps](synthetic-homotopy-theory.joins-of-maps.mdᵉ)
-ᵉ [Pushout-products](synthetic-homotopy-theory.pushout-products.mdᵉ)
-ᵉ [Dependentᵉ pushout-products](synthetic-homotopy-theory.dependent-pushout-products.mdᵉ)

## References

{{#bibliographyᵉ}} {{#referenceᵉ Rij17ᵉ}}