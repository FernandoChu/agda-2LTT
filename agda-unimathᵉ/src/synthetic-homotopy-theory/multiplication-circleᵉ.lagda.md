# The multiplication operation on the circle

```agda
module synthetic-homotopy-theory.multiplication-circleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ

open import synthetic-homotopy-theory.circleᵉ
open import synthetic-homotopy-theory.loop-homotopy-circleᵉ
```

</details>

## Idea

Classically,ᵉ theᵉ circleᵉ canᵉ beᵉ viewedᵉ asᵉ theᵉ subsetᵉ ofᵉ theᵉ complexᵉ numbersᵉ ofᵉ
absoluteᵉ valueᵉ 1.ᵉ Theᵉ absoluteᵉ valueᵉ ofᵉ aᵉ productᵉ ofᵉ complexᵉ numbersᵉ isᵉ theᵉ
productᵉ ofᵉ theirᵉ absoluteᵉ values.ᵉ Thisᵉ impliesᵉ thatᵉ whenᵉ weᵉ multiplyᵉ twoᵉ complexᵉ
numbersᵉ onᵉ theᵉ unitᵉ circle,ᵉ theᵉ resultᵉ isᵉ aᵉ complexᵉ numberᵉ onᵉ theᵉ unitᵉ circle.ᵉ
Thisᵉ multiplicativeᵉ structureᵉ carriesᵉ overᵉ to theᵉ homotopyᵉ typeᵉ ofᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.md).ᵉ

## Definitions

### Multiplication on the circle

```agda
Mul-Π-𝕊¹ᵉ : 𝕊¹ᵉ → UUᵉ lzero
Mul-Π-𝕊¹ᵉ xᵉ = 𝕊¹-Pointed-Typeᵉ →∗ᵉ (𝕊¹ᵉ ,ᵉ xᵉ)

dependent-identification-Mul-Π-𝕊¹ᵉ :
  {xᵉ : 𝕊¹ᵉ} (pᵉ : base-𝕊¹ᵉ ＝ᵉ xᵉ) (qᵉ : Mul-Π-𝕊¹ᵉ base-𝕊¹ᵉ) (rᵉ : Mul-Π-𝕊¹ᵉ xᵉ) →
  (Hᵉ : pr1ᵉ qᵉ ~ᵉ pr1ᵉ rᵉ) →
  pr2ᵉ qᵉ ∙ᵉ pᵉ ＝ᵉ Hᵉ base-𝕊¹ᵉ ∙ᵉ pr2ᵉ rᵉ →
  trᵉ Mul-Π-𝕊¹ᵉ pᵉ qᵉ ＝ᵉ rᵉ
dependent-identification-Mul-Π-𝕊¹ᵉ reflᵉ qᵉ rᵉ Hᵉ uᵉ =
  eq-pointed-htpyᵉ qᵉ rᵉ (Hᵉ ,ᵉ invᵉ right-unitᵉ ∙ᵉ uᵉ)

eq-id-id-𝕊¹-Pointed-Typeᵉ :
  trᵉ Mul-Π-𝕊¹ᵉ loop-𝕊¹ᵉ id-pointed-mapᵉ ＝ᵉ id-pointed-mapᵉ
eq-id-id-𝕊¹-Pointed-Typeᵉ =
  dependent-identification-Mul-Π-𝕊¹ᵉ loop-𝕊¹ᵉ
    ( id-pointed-mapᵉ)
    ( id-pointed-mapᵉ)
    ( loop-htpy-𝕊¹ᵉ)
    ( invᵉ compute-base-loop-htpy-𝕊¹ᵉ ∙ᵉ invᵉ right-unitᵉ)

mul-Π-𝕊¹ᵉ : Π-𝕊¹ᵉ (Mul-Π-𝕊¹ᵉ) (id-pointed-mapᵉ) (eq-id-id-𝕊¹-Pointed-Typeᵉ)
mul-Π-𝕊¹ᵉ =
  apply-dependent-universal-property-𝕊¹ᵉ
    ( Mul-Π-𝕊¹ᵉ)
    ( id-pointed-mapᵉ)
    ( eq-id-id-𝕊¹-Pointed-Typeᵉ)

mul-𝕊¹ᵉ : 𝕊¹ᵉ → 𝕊¹ᵉ → 𝕊¹ᵉ
mul-𝕊¹ᵉ xᵉ = pr1ᵉ (pr1ᵉ mul-Π-𝕊¹ᵉ xᵉ)
```

## Properties

### The unit laws of multiplication on the circle

```agda
left-unit-law-mul-𝕊¹ᵉ : (xᵉ : 𝕊¹ᵉ) → mul-𝕊¹ᵉ base-𝕊¹ᵉ xᵉ ＝ᵉ xᵉ
left-unit-law-mul-𝕊¹ᵉ = htpy-eqᵉ (apᵉ pr1ᵉ (pr1ᵉ (pr2ᵉ mul-Π-𝕊¹ᵉ)))

right-unit-law-mul-𝕊¹ᵉ : (xᵉ : 𝕊¹ᵉ) → mul-𝕊¹ᵉ xᵉ base-𝕊¹ᵉ ＝ᵉ xᵉ
right-unit-law-mul-𝕊¹ᵉ xᵉ = pr2ᵉ (pr1ᵉ mul-Π-𝕊¹ᵉ xᵉ)
```