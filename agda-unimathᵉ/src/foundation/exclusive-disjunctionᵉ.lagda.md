# Exclusive disjunctions

```agda
module foundation.exclusive-disjunctionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.exclusive-sumᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "exclusiveᵉ disjunction"ᵉ Disambiguation="ofᵉ propositions"ᵉ WDID=Q498186ᵉ WD="exclusiveᵉ or"ᵉ Agda=xor-Propᵉ}}
ofᵉ twoᵉ [propositions](foundation-core.propositions.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ theᵉ
propositionᵉ thatᵉ preciselyᵉ oneᵉ ofᵉ `P`ᵉ andᵉ `Q`ᵉ holds,ᵉ andᵉ isᵉ definedᵉ asᵉ theᵉ
propositionᵉ thatᵉ theᵉ [coproduct](foundation-core.coproduct-types.mdᵉ) ofᵉ theirᵉ
underlyingᵉ typesᵉ isᵉ [contractible](foundation-core.contractible-types.mdᵉ)

```text
  Pᵉ ⊻ᵉ Qᵉ :=ᵉ is-contrᵉ (Pᵉ +ᵉ Qᵉ)
```

Itᵉ necessarilyᵉ followsᵉ thatᵉ preciselyᵉ oneᵉ ofᵉ theᵉ twoᵉ propositionsᵉ hold,ᵉ andᵉ theᵉ
otherᵉ doesᵉ not.ᵉ Thisᵉ isᵉ capturedᵉ byᵉ theᵉ
[exclusiveᵉ sum](foundation.exclusive-sum.md).ᵉ

## Definitions

### The exclusive disjunction of arbitrary types

Theᵉ definitionᵉ ofᵉ exclusiveᵉ sumᵉ isᵉ sometimesᵉ generalizedᵉ to arbitraryᵉ types,ᵉ
whichᵉ weᵉ record hereᵉ forᵉ completeness.ᵉ

Theᵉ
{{#conceptᵉ "exclusiveᵉ disjunction"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=xor-type-Propᵉ}}
ofᵉ theᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ isᵉ theᵉ propositionᵉ thatᵉ theirᵉ coproductᵉ isᵉ contractibleᵉ

```text
  Aᵉ ⊻ᵉ Bᵉ :=ᵉ is-contrᵉ (Aᵉ +ᵉ B).ᵉ
```

Noteᵉ thatᵉ unlikeᵉ theᵉ caseᵉ forᵉ [disjunction](foundation.disjunction.mdᵉ) andᵉ
[existentialᵉ quantification](foundation.existential-quantification.md),ᵉ butᵉ
analogousᵉ to theᵉ caseᵉ ofᵉ
[uniquenessᵉ quantification](foundation.uniqueness-quantification.md),ᵉ theᵉ
exclusiveᵉ disjunctionᵉ ofᵉ typesᵉ doesᵉ _notᵉ_ coincideᵉ with theᵉ exclusiveᵉ
disjunctionᵉ ofᵉ theᵉ summands'ᵉ
[propositionalᵉ reflections](foundation.propositional-truncations.mdᵉ):

```text
  Aᵉ ⊻ᵉ Bᵉ ≠ᵉ ║ᵉ Aᵉ ║₋₁ᵉ ⊻ᵉ ║ᵉ Bᵉ ║₋₁.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  xor-type-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  xor-type-Propᵉ = is-contr-Propᵉ (Aᵉ +ᵉ Bᵉ)

  xor-typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  xor-typeᵉ = type-Propᵉ xor-type-Propᵉ

  is-prop-xor-typeᵉ : is-propᵉ xor-typeᵉ
  is-prop-xor-typeᵉ = is-prop-type-Propᵉ xor-type-Propᵉ
```

### The exclusive disjunction

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  xor-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  xor-Propᵉ = xor-type-Propᵉ (type-Propᵉ Pᵉ) (type-Propᵉ Qᵉ)

  type-xor-Propᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-xor-Propᵉ = type-Propᵉ xor-Propᵉ

  is-prop-xor-Propᵉ : is-propᵉ type-xor-Propᵉ
  is-prop-xor-Propᵉ = is-prop-type-Propᵉ xor-Propᵉ

  infixr 10 _⊻ᵉ_
  _⊻ᵉ_ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  _⊻ᵉ_ = xor-Propᵉ
```

**Notation.**ᵉ Theᵉ
[symbolᵉ usedᵉ forᵉ exclusiveᵉ disjunction](https://codepoints.net/U+22BB?lang=enᵉ)
`⊻`ᵉ canᵉ beᵉ writtenᵉ with theᵉ escapeᵉ sequenceᵉ `\veebar`.ᵉ

## Properties

### The canonical map from the exclusive disjunction into the exclusive sum

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-exclusive-sum-xorᵉ : xor-typeᵉ Aᵉ Bᵉ → exclusive-sumᵉ Aᵉ Bᵉ
  map-exclusive-sum-xorᵉ (inlᵉ aᵉ ,ᵉ Hᵉ) =
    inlᵉ (aᵉ ,ᵉ (λ bᵉ → is-empty-eq-coproduct-inl-inrᵉ aᵉ bᵉ (Hᵉ (inrᵉ bᵉ))))
  map-exclusive-sum-xorᵉ (inrᵉ bᵉ ,ᵉ Hᵉ) =
    inrᵉ (bᵉ ,ᵉ (λ aᵉ → is-empty-eq-coproduct-inr-inlᵉ bᵉ aᵉ (Hᵉ (inlᵉ aᵉ))))
```

### The exclusive disjunction of two propositions is equivalent to their exclusive sum

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Propᵉ l1ᵉ) (Qᵉ : Propᵉ l2ᵉ)
  where

  equiv-exclusive-sum-xor-Propᵉ : type-xor-Propᵉ Pᵉ Qᵉ ≃ᵉ type-exclusive-sum-Propᵉ Pᵉ Qᵉ
  equiv-exclusive-sum-xor-Propᵉ =
    ( equiv-coproductᵉ
      ( equiv-totᵉ
        ( λ pᵉ →
          ( ( equiv-Π-equiv-familyᵉ (compute-eq-coproduct-inl-inrᵉ pᵉ)) ∘eᵉ
            ( left-unit-law-product-is-contrᵉ
              ( is-contr-Πᵉ
                ( λ p'ᵉ →
                  is-contr-equiv'ᵉ
                    ( pᵉ ＝ᵉ p'ᵉ)
                    ( equiv-ap-embᵉ (emb-inlᵉ (type-Propᵉ Pᵉ) (type-Propᵉ Qᵉ)))
                    ( is-prop-type-Propᵉ Pᵉ pᵉ p'ᵉ))))) ∘eᵉ
          ( equiv-dependent-universal-property-coproductᵉ (inlᵉ pᵉ ＝ᵉ_))))
      ( equiv-totᵉ
        ( λ qᵉ →
          ( ( equiv-Π-equiv-familyᵉ (compute-eq-coproduct-inr-inlᵉ qᵉ)) ∘eᵉ
            ( right-unit-law-product-is-contrᵉ
              ( is-contr-Πᵉ
                ( λ q'ᵉ →
                  is-contr-equiv'ᵉ
                    ( qᵉ ＝ᵉ q'ᵉ)
                    ( equiv-ap-embᵉ (emb-inrᵉ (type-Propᵉ Pᵉ) (type-Propᵉ Qᵉ)))
                    ( is-prop-type-Propᵉ Qᵉ qᵉ q'ᵉ))))) ∘eᵉ
          ( equiv-dependent-universal-property-coproductᵉ (inrᵉ qᵉ ＝ᵉ_))))) ∘eᵉ
    ( right-distributive-Σ-coproductᵉ
      ( type-Propᵉ Pᵉ)
      ( type-Propᵉ Qᵉ)
      ( λ xᵉ → (yᵉ : type-Propᵉ Pᵉ +ᵉ type-Propᵉ Qᵉ) → xᵉ ＝ᵉ yᵉ))
```

## See also

-ᵉ Theᵉ indexedᵉ counterpartᵉ to exclusiveᵉ disjunctionᵉ isᵉ
  [uniqueᵉ existence](foundation.uniqueness-quantification.md).ᵉ

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [exclusiveᵉ disjunction](https://ncatlab.org/nlab/show/exclusive+disjunctionᵉ)
  atᵉ $n$Labᵉ
-ᵉ [Exclusiveᵉ disjunction](https://simple.wikipedia.org/wiki/Exclusive_disjunctionᵉ)
  atᵉ Wikipediaᵉ