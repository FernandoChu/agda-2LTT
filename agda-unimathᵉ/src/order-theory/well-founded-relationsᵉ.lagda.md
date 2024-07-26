# Well-founded relations

```agda
module order-theory.well-founded-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.accessible-elements-relationsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ
[binaryᵉ relation](foundation.binary-relations.mdᵉ) `_ϵᵉ_ : Xᵉ → Xᵉ → Type`ᵉ weᵉ sayᵉ
thatᵉ theᵉ relationᵉ `_ϵ_`ᵉ isᵉ **well-founded**ᵉ ifᵉ allᵉ elementsᵉ ofᵉ `X`ᵉ areᵉ
[accessible](order-theory.accessible-elements-relations.mdᵉ) with respectᵉ to
`_ϵ_`.ᵉ

Well-foundedᵉ relationsᵉ satisfyᵉ anᵉ inductionᵉ principleᵉ: Inᵉ orderᵉ to constructᵉ anᵉ
elementᵉ ofᵉ `Pᵉ x`ᵉ forᵉ allᵉ `xᵉ : X`ᵉ itᵉ sufficesᵉ to constructᵉ anᵉ elementᵉ ofᵉ `Pᵉ y`ᵉ
forᵉ allᵉ elementsᵉ `yᵉ ϵᵉ x`.ᵉ Moreᵉ precisely,ᵉ theᵉ **well-foundedᵉ inductionᵉ
principle**ᵉ isᵉ aᵉ functionᵉ

```text
  (xᵉ : Xᵉ) → ((yᵉ : Yᵉ) → yᵉ ϵᵉ xᵉ → Pᵉ yᵉ) → Pᵉ x.ᵉ
```

## Definitions

### The predicate of being a well-founded relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (_ϵᵉ_ : Relationᵉ l2ᵉ Xᵉ)
  where

  is-well-founded-prop-Relationᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-well-founded-prop-Relationᵉ =
    Π-Propᵉ Xᵉ (is-accessible-element-prop-Relationᵉ _ϵᵉ_)

  is-well-founded-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-well-founded-Relationᵉ = (xᵉ : Xᵉ) → is-accessible-element-Relationᵉ _ϵᵉ_ xᵉ
```

### Well-founded relations

```agda
Well-Founded-Relationᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Well-Founded-Relationᵉ lᵉ Xᵉ = Σᵉ (Relationᵉ lᵉ Xᵉ) is-well-founded-Relationᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Well-Founded-Relationᵉ l2ᵉ Xᵉ)
  where

  rel-Well-Founded-Relationᵉ : Relationᵉ l2ᵉ Xᵉ
  rel-Well-Founded-Relationᵉ = pr1ᵉ Rᵉ

  is-well-founded-Well-Founded-Relationᵉ :
    is-well-founded-Relationᵉ rel-Well-Founded-Relationᵉ
  is-well-founded-Well-Founded-Relationᵉ = pr2ᵉ Rᵉ
```

## Properties

### Well-founded induction

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} ((_ϵᵉ_ ,ᵉ wᵉ) : Well-Founded-Relationᵉ l2ᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  ind-Well-Founded-Relationᵉ :
    ({xᵉ : Xᵉ} → ({yᵉ : Xᵉ} → yᵉ ϵᵉ xᵉ → Pᵉ yᵉ) → Pᵉ xᵉ) → (xᵉ : Xᵉ) → Pᵉ xᵉ
  ind-Well-Founded-Relationᵉ IHᵉ xᵉ =
    ind-accessible-element-Relationᵉ _ϵᵉ_ Pᵉ (λ _ → IHᵉ) (wᵉ xᵉ)
```

### A well-founded relation is asymmetric (and thus irreflexive)

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} ((_ϵᵉ_ ,ᵉ wᵉ) : Well-Founded-Relationᵉ l2ᵉ Xᵉ)
  where

  is-asymmetric-Well-Founded-Relationᵉ :
    is-asymmetricᵉ _ϵᵉ_
  is-asymmetric-Well-Founded-Relationᵉ xᵉ yᵉ =
    is-asymmetric-is-accessible-element-Relationᵉ _ϵᵉ_ (wᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (ϵᵉ : Well-Founded-Relationᵉ l2ᵉ Xᵉ)
  where

  is-irreflexive-Well-Founded-Relationᵉ :
    is-irreflexiveᵉ (rel-Well-Founded-Relationᵉ ϵᵉ)
  is-irreflexive-Well-Founded-Relationᵉ =
    is-irreflexive-is-asymmetricᵉ
      ( rel-Well-Founded-Relationᵉ ϵᵉ)
      ( is-asymmetric-Well-Founded-Relationᵉ ϵᵉ)
```