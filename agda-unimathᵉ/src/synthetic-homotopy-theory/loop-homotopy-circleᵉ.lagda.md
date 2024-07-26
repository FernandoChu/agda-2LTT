# The loop homotopy on the circle

```agda
module synthetic-homotopy-theory.loop-homotopy-circleᵉ where
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
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "loopᵉ homotopy"ᵉ Disambiguation="onᵉ theᵉ circleᵉ type"ᵉ Agda=loop-htpy-𝕊¹ᵉ}}
onᵉ theᵉ [circle](synthetic-homotopy-theory.circle.mdᵉ) isᵉ theᵉ familyᵉ ofᵉ
[equalities](foundation-core.identity-types.mdᵉ)

```text
  loop-htpy-𝕊¹ᵉ : (xᵉ : 𝕊¹ᵉ) → xᵉ ＝ᵉ xᵉ
```

definedᵉ byᵉ [transporting](foundation-core.transport-along-identifications.mdᵉ)
alongᵉ theᵉ loopᵉ ofᵉ theᵉ circle.ᵉ Thisᵉ [homotopy](foundation-core.homotopies.mdᵉ) isᵉ
distinctᵉ fromᵉ theᵉ constantᵉ homotopyᵉ andᵉ hasᵉ windingᵉ numberᵉ 1.ᵉ

## Definitions

### The loop homotopy on the circle

```agda
loop-htpy-𝕊¹ᵉ : (xᵉ : 𝕊¹ᵉ) → xᵉ ＝ᵉ xᵉ
loop-htpy-𝕊¹ᵉ =
  function-apply-dependent-universal-property-𝕊¹ᵉ
    ( eq-valueᵉ idᵉ idᵉ)
    ( loop-𝕊¹ᵉ)
    ( map-compute-dependent-identification-eq-value-id-idᵉ
      ( loop-𝕊¹ᵉ)
      ( loop-𝕊¹ᵉ)
      ( loop-𝕊¹ᵉ)
      ( reflᵉ))

compute-base-loop-htpy-𝕊¹ᵉ : loop-htpy-𝕊¹ᵉ base-𝕊¹ᵉ ＝ᵉ loop-𝕊¹ᵉ
compute-base-loop-htpy-𝕊¹ᵉ =
  base-dependent-universal-property-𝕊¹ᵉ
    ( eq-valueᵉ idᵉ idᵉ)
    ( loop-𝕊¹ᵉ)
    ( map-compute-dependent-identification-eq-value-id-idᵉ
      ( loop-𝕊¹ᵉ)
      ( loop-𝕊¹ᵉ)
      ( loop-𝕊¹ᵉ)
      ( reflᵉ))
```

## Properties

### The loop homotopy on the circle is nontrivial

```agda
abstract
  is-not-refl-ev-base-loop-htpy-𝕊¹ᵉ : loop-htpy-𝕊¹ᵉ base-𝕊¹ᵉ ≠ᵉ reflᵉ
  is-not-refl-ev-base-loop-htpy-𝕊¹ᵉ pᵉ =
    is-nontrivial-loop-𝕊¹ᵉ (invᵉ compute-base-loop-htpy-𝕊¹ᵉ ∙ᵉ pᵉ)

is-nontrivial-loop-htpy-𝕊¹'ᵉ : ¬ᵉ (loop-htpy-𝕊¹ᵉ ~ᵉ refl-htpyᵉ)
is-nontrivial-loop-htpy-𝕊¹'ᵉ Hᵉ =
  is-not-refl-ev-base-loop-htpy-𝕊¹ᵉ (Hᵉ base-𝕊¹ᵉ)

is-nontrivial-loop-htpy-𝕊¹ᵉ : loop-htpy-𝕊¹ᵉ ≠ᵉ refl-htpyᵉ
is-nontrivial-loop-htpy-𝕊¹ᵉ =
  nonequal-Πᵉ loop-htpy-𝕊¹ᵉ refl-htpyᵉ base-𝕊¹ᵉ is-not-refl-ev-base-loop-htpy-𝕊¹ᵉ
```