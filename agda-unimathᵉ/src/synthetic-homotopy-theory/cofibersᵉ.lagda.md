# Cofibers

```agda
module synthetic-homotopy-theory.cofibersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **cofiber**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ theᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ theᵉ spanᵉ `1ᵉ ←ᵉ Aᵉ → B`.ᵉ

## Definitions

### The cofiber of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  cofiberᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  cofiberᵉ fᵉ = pushoutᵉ fᵉ (terminal-mapᵉ Aᵉ)

  cocone-cofiberᵉ :
    (fᵉ : Aᵉ → Bᵉ) → coconeᵉ fᵉ (terminal-mapᵉ Aᵉ) (cofiberᵉ fᵉ)
  cocone-cofiberᵉ fᵉ = cocone-pushoutᵉ fᵉ (terminal-mapᵉ Aᵉ)

  inl-cofiberᵉ : (fᵉ : Aᵉ → Bᵉ) → Bᵉ → cofiberᵉ fᵉ
  inl-cofiberᵉ fᵉ = pr1ᵉ (cocone-cofiberᵉ fᵉ)

  inr-cofiberᵉ : (fᵉ : Aᵉ → Bᵉ) → unitᵉ → cofiberᵉ fᵉ
  inr-cofiberᵉ fᵉ = pr1ᵉ (pr2ᵉ (cocone-cofiberᵉ fᵉ))

  point-cofiberᵉ : (fᵉ : Aᵉ → Bᵉ) → cofiberᵉ fᵉ
  point-cofiberᵉ fᵉ = inr-cofiberᵉ fᵉ starᵉ

  cofiber-Pointed-Typeᵉ : (fᵉ : Aᵉ → Bᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (cofiber-Pointed-Typeᵉ fᵉ) = cofiberᵉ fᵉ
  pr2ᵉ (cofiber-Pointed-Typeᵉ fᵉ) = point-cofiberᵉ fᵉ

  universal-property-cofiberᵉ :
    (fᵉ : Aᵉ → Bᵉ) →
    universal-property-pushoutᵉ fᵉ (terminal-mapᵉ Aᵉ) (cocone-cofiberᵉ fᵉ)
  universal-property-cofiberᵉ fᵉ = up-pushoutᵉ fᵉ (terminal-mapᵉ Aᵉ)
```

## Properties

### The cofiber of an equivalence is contractible

Noteᵉ thatᵉ thisᵉ isᵉ notᵉ aᵉ logicalᵉ equivalence.ᵉ Notᵉ everyᵉ mapᵉ whoseᵉ cofibersᵉ areᵉ
allᵉ contractibleᵉ isᵉ anᵉ equivalence.ᵉ Forᵉ instance,ᵉ theᵉ cofiberᵉ ofᵉ `Xᵉ → 1`ᵉ where
`X`ᵉ isᵉ anᵉ [acyclicᵉ type](synthetic-homotopy-theory.acyclic-types.mdᵉ) isᵉ byᵉ
definitionᵉ contractible.ᵉ Examplesᵉ ofᵉ noncontractibleᵉ acyclicᵉ typesᵉ includeᵉ
[Hatcher'sᵉ acyclicᵉ type](synthetic-homotopy-theory.hatchers-acyclic-type.md).ᵉ

```agda
is-contr-cofiber-is-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  is-equivᵉ fᵉ → is-contrᵉ (cofiberᵉ fᵉ)
is-contr-cofiber-is-equivᵉ {Aᵉ = Aᵉ} fᵉ is-equiv-fᵉ =
  is-contr-is-equiv'ᵉ
    ( unitᵉ)
    ( pr1ᵉ (pr2ᵉ (cocone-cofiberᵉ fᵉ)))
    ( is-equiv-universal-property-pushoutᵉ
      ( fᵉ)
      ( terminal-mapᵉ Aᵉ)
      ( cocone-cofiberᵉ fᵉ)
      ( is-equiv-fᵉ)
      ( universal-property-cofiberᵉ fᵉ))
    ( is-contr-unitᵉ)
```

### The cofiber of the point inclusion of `X` is equivalent to `X`

```agda
is-equiv-inl-cofiber-pointᵉ :
  {lᵉ : Level} {Bᵉ : UUᵉ lᵉ} (bᵉ : Bᵉ) → is-equivᵉ (inl-cofiberᵉ (pointᵉ bᵉ))
is-equiv-inl-cofiber-pointᵉ {Bᵉ = Bᵉ} bᵉ =
  is-equiv-universal-property-pushout'ᵉ
    ( pointᵉ bᵉ)
    ( terminal-mapᵉ unitᵉ)
    ( cocone-pushoutᵉ (pointᵉ bᵉ) (terminal-mapᵉ unitᵉ))
    ( is-equiv-is-contrᵉ (terminal-mapᵉ unitᵉ) is-contr-unitᵉ is-contr-unitᵉ)
    ( up-pushoutᵉ (pointᵉ bᵉ) (terminal-mapᵉ unitᵉ))
```