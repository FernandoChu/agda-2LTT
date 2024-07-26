# Function extensionality

```agda
module foundation.function-extensionalityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.evaluation-functionsᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coherently-invertible-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "functionᵉ extensionalityᵉ axiom"ᵉ Agda=function-extensionalityᵉ Agda=funextᵉ}}
assertsᵉ thatᵉ [identifications](foundation-core.identity-types.mdᵉ) ofᵉ (dependentᵉ)
functionsᵉ areᵉ [equivalently](foundation-core.equivalences.mdᵉ) describedᵉ asᵉ
[homotopies](foundation-core.homotopies.mdᵉ) betweenᵉ them.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ
functionᵉ isᵉ completelyᵉ determinedᵉ byᵉ itsᵉ values.ᵉ

Functionᵉ extensionalityᵉ isᵉ postulatedᵉ byᵉ statingᵉ thatᵉ theᵉ canonicalᵉ mapᵉ

```text
  htpy-eqᵉ : fᵉ ＝ᵉ gᵉ → fᵉ ~ᵉ gᵉ
```

fromᵉ identificationsᵉ betweenᵉ twoᵉ functionsᵉ to homotopiesᵉ betweenᵉ themᵉ isᵉ anᵉ
equivalence.ᵉ Theᵉ mapᵉ `htpy-eq`ᵉ isᵉ theᵉ uniqueᵉ mapᵉ thatᵉ fitsᵉ in aᵉ
[commutingᵉ triangle](foundation-core.commuting-triangles-of-maps.mdᵉ)

```text
              htpy-eqᵉ
    (fᵉ ＝ᵉ gᵉ) ---------->ᵉ (fᵉ ~ᵉ gᵉ)
           \ᵉ            /ᵉ
  apᵉ (evᵉ xᵉ) \ᵉ          /ᵉ evᵉ xᵉ
             ∨ᵉ        ∨ᵉ
            (fᵉ xᵉ ＝ᵉ gᵉ xᵉ)
```

Inᵉ otherᵉ words,ᵉ weᵉ defineᵉ

```text
  htpy-eqᵉ pᵉ xᵉ :=ᵉ apᵉ (evᵉ xᵉ) p.ᵉ
```

Itᵉ followsᵉ fromᵉ thisᵉ definitionᵉ thatᵉ `htpy-eqᵉ reflᵉ ≐ᵉ refl-htpy`,ᵉ asᵉ expected.ᵉ

## Definitions

### Equalities induce homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  htpy-eqᵉ : {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → fᵉ ＝ᵉ gᵉ → fᵉ ~ᵉ gᵉ
  htpy-eqᵉ pᵉ aᵉ = apᵉ (evᵉ aᵉ) pᵉ

  compute-htpy-eq-reflᵉ : {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → htpy-eqᵉ reflᵉ ＝ᵉ refl-htpy'ᵉ fᵉ
  compute-htpy-eq-reflᵉ = reflᵉ
```

### An instance of function extensionality

Thisᵉ propertyᵉ assertsᵉ that,ᵉ _givenᵉ_ twoᵉ functionsᵉ `f`ᵉ andᵉ `g`,ᵉ theᵉ mapᵉ

```text
  htpy-eqᵉ : fᵉ ＝ᵉ gᵉ → fᵉ ~ᵉ gᵉ
```

isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  instance-function-extensionalityᵉ : (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  instance-function-extensionalityᵉ fᵉ gᵉ = is-equivᵉ (htpy-eqᵉ {fᵉ = fᵉ} {gᵉ})
```

### Based function extensionality

Thisᵉ propertyᵉ assertsᵉ that,ᵉ _givenᵉ_ aᵉ functionᵉ `f`,ᵉ theᵉ mapᵉ

```text
  htpy-eqᵉ : fᵉ ＝ᵉ gᵉ → fᵉ ~ᵉ gᵉ
```

isᵉ anᵉ equivalenceᵉ forᵉ anyᵉ functionᵉ `g`ᵉ ofᵉ theᵉ sameᵉ type.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  based-function-extensionalityᵉ : (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  based-function-extensionalityᵉ fᵉ =
    (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → instance-function-extensionalityᵉ fᵉ gᵉ
```

### The function extensionality principle with respect to a universe level

```agda
function-extensionality-Levelᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
function-extensionality-Levelᵉ l1ᵉ l2ᵉ =
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → based-function-extensionalityᵉ fᵉ
```

### The function extensionality axiom

```agda
function-extensionalityᵉ : UUωᵉ
function-extensionalityᵉ = {l1ᵉ l2ᵉ : Level} → function-extensionality-Levelᵉ l1ᵉ l2ᵉ
```

Ratherᵉ thanᵉ postulatingᵉ aᵉ witnessᵉ ofᵉ `function-extensionality`ᵉ directly,ᵉ weᵉ
postulate theᵉ constituentsᵉ ofᵉ aᵉ coherentᵉ two-sidedᵉ inverseᵉ to `htpy-eq`.ᵉ Theᵉ
benefitsᵉ areᵉ thatᵉ weᵉ endᵉ upᵉ with aᵉ singleᵉ converseᵉ mapᵉ to `htpy-eq`,ᵉ ratherᵉ thanᵉ
aᵉ separateᵉ sectionᵉ andᵉ retraction,ᵉ althoughᵉ theyᵉ wouldᵉ beᵉ homotopicᵉ regardless.ᵉ
Inᵉ addition,ᵉ thisᵉ formulationᵉ helpsᵉ Agdaᵉ displayᵉ goalsᵉ involvingᵉ functionᵉ
extensionalityᵉ in aᵉ moreᵉ readableᵉ way.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  postulate
    eq-htpyᵉ : fᵉ ~ᵉ gᵉ → fᵉ ＝ᵉ gᵉ

    is-section-eq-htpyᵉ : is-sectionᵉ htpy-eqᵉ eq-htpyᵉ

    is-retraction-eq-htpy'ᵉ : is-retractionᵉ htpy-eqᵉ eq-htpyᵉ

    coh-eq-htpy'ᵉ :
      coherence-is-coherently-invertibleᵉ
        ( htpy-eqᵉ)
        ( eq-htpyᵉ)
        ( is-section-eq-htpyᵉ)
        ( is-retraction-eq-htpy'ᵉ)

funextᵉ : function-extensionalityᵉ
funextᵉ fᵉ gᵉ =
  is-equiv-is-invertibleᵉ eq-htpyᵉ is-section-eq-htpyᵉ is-retraction-eq-htpy'ᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  equiv-funextᵉ : {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → (fᵉ ＝ᵉ gᵉ) ≃ᵉ (fᵉ ~ᵉ gᵉ)
  pr1ᵉ (equiv-funextᵉ) = htpy-eqᵉ
  pr2ᵉ (equiv-funextᵉ {fᵉ} {gᵉ}) = funextᵉ fᵉ gᵉ

  is-equiv-eq-htpyᵉ :
    (fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-equivᵉ (eq-htpyᵉ {fᵉ = fᵉ} {gᵉ})
  is-equiv-eq-htpyᵉ fᵉ gᵉ =
    is-equiv-is-invertibleᵉ htpy-eqᵉ is-retraction-eq-htpy'ᵉ is-section-eq-htpyᵉ

  abstract
    is-retraction-eq-htpyᵉ :
      {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → is-retractionᵉ (htpy-eqᵉ {fᵉ = fᵉ} {gᵉ}) eq-htpyᵉ
    is-retraction-eq-htpyᵉ {fᵉ} {gᵉ} = is-retraction-map-inv-is-equivᵉ (funextᵉ fᵉ gᵉ)

  eq-htpy-refl-htpyᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → eq-htpyᵉ (refl-htpyᵉ {fᵉ = fᵉ}) ＝ᵉ reflᵉ
  eq-htpy-refl-htpyᵉ fᵉ = is-retraction-eq-htpyᵉ reflᵉ

  equiv-eq-htpyᵉ : {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} → (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ＝ᵉ gᵉ)
  pr1ᵉ (equiv-eq-htpyᵉ {fᵉ} {gᵉ}) = eq-htpyᵉ
  pr2ᵉ (equiv-eq-htpyᵉ {fᵉ} {gᵉ}) = is-equiv-eq-htpyᵉ fᵉ gᵉ
```

### Function extensionality for implicit functions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ}
  where

  equiv-funext-implicitᵉ :
    (Idᵉ {Aᵉ = {xᵉ : Aᵉ} → Bᵉ xᵉ} fᵉ gᵉ) ≃ᵉ ((xᵉ : Aᵉ) → fᵉ {xᵉ} ＝ᵉ gᵉ {xᵉ})
  equiv-funext-implicitᵉ =
    equiv-funextᵉ ∘eᵉ equiv-apᵉ equiv-explicit-implicit-Πᵉ fᵉ gᵉ

  htpy-eq-implicitᵉ :
    Idᵉ {Aᵉ = {xᵉ : Aᵉ} → Bᵉ xᵉ} fᵉ gᵉ → (xᵉ : Aᵉ) → fᵉ {xᵉ} ＝ᵉ gᵉ {xᵉ}
  htpy-eq-implicitᵉ = map-equivᵉ equiv-funext-implicitᵉ

  funext-implicitᵉ : is-equivᵉ htpy-eq-implicitᵉ
  funext-implicitᵉ = is-equiv-map-equivᵉ equiv-funext-implicitᵉ

  eq-htpy-implicitᵉ :
    ((xᵉ : Aᵉ) → fᵉ {xᵉ} ＝ᵉ gᵉ {xᵉ}) → Idᵉ {Aᵉ = {xᵉ : Aᵉ} → Bᵉ xᵉ} fᵉ gᵉ
  eq-htpy-implicitᵉ = map-inv-equivᵉ equiv-funext-implicitᵉ
```

## Properties

### `htpy-eq` preserves concatenation of identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  htpy-eq-concatᵉ :
    (pᵉ : fᵉ ＝ᵉ gᵉ) (qᵉ : gᵉ ＝ᵉ hᵉ) → htpy-eqᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ htpy-eqᵉ pᵉ ∙hᵉ htpy-eqᵉ qᵉ
  htpy-eq-concatᵉ reflᵉ reflᵉ = reflᵉ
```

### `eq-htpy` preserves concatenation of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  eq-htpy-concat-htpyᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) → eq-htpyᵉ (Hᵉ ∙hᵉ Kᵉ) ＝ᵉ (eq-htpyᵉ Hᵉ ∙ᵉ eq-htpyᵉ Kᵉ)
  eq-htpy-concat-htpyᵉ Hᵉ Kᵉ =
      ( apᵉ
        ( eq-htpyᵉ)
        ( invᵉ (ap-binaryᵉ _∙hᵉ_ (is-section-eq-htpyᵉ Hᵉ) (is-section-eq-htpyᵉ Kᵉ)) ∙ᵉ
          invᵉ (htpy-eq-concatᵉ (eq-htpyᵉ Hᵉ) (eq-htpyᵉ Kᵉ)))) ∙ᵉ
      ( is-retraction-eq-htpyᵉ (eq-htpyᵉ Hᵉ ∙ᵉ eq-htpyᵉ Kᵉ))
```

### `htpy-eq` preserves inverses

Forᵉ anyᵉ twoᵉ functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ x`ᵉ weᵉ haveᵉ aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                  invᵉ
       (fᵉ = gᵉ) --------->ᵉ (gᵉ = fᵉ)
          |                  |
  htpy-eqᵉ |                  | htpy-eqᵉ
          ∨ᵉ                  ∨ᵉ
       (fᵉ ~ᵉ gᵉ) --------->ᵉ (gᵉ ~ᵉ f).ᵉ
                inv-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-htpy-eq-invᵉ : inv-htpyᵉ {fᵉ = fᵉ} {gᵉ} ∘ᵉ htpy-eqᵉ ~ᵉ htpy-eqᵉ ∘ᵉ invᵉ
  compute-htpy-eq-invᵉ reflᵉ = reflᵉ

  compute-inv-htpy-htpy-eqᵉ : htpy-eqᵉ ∘ᵉ invᵉ ~ᵉ inv-htpyᵉ {fᵉ = fᵉ} {gᵉ} ∘ᵉ htpy-eqᵉ
  compute-inv-htpy-htpy-eqᵉ = inv-htpyᵉ compute-htpy-eq-invᵉ
```

### `eq-htpy` preserves inverses

Forᵉ anyᵉ twoᵉ functionsᵉ `fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ x`ᵉ weᵉ haveᵉ aᵉ commutingᵉ squareᵉ

```text
                inv-htpyᵉ
       (fᵉ ~ᵉ gᵉ) --------->ᵉ (gᵉ ~ᵉ fᵉ)
          |                  |
  eq-htpyᵉ |                  | eq-htpyᵉ
          ∨ᵉ                  ∨ᵉ
       (fᵉ = gᵉ) --------->ᵉ (gᵉ = f).ᵉ
                  invᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-eq-htpy-inv-htpyᵉ :
    invᵉ ∘ᵉ eq-htpyᵉ ~ᵉ eq-htpyᵉ ∘ᵉ inv-htpyᵉ {fᵉ = fᵉ} {gᵉ}
  compute-eq-htpy-inv-htpyᵉ Hᵉ =
    ( invᵉ (is-retraction-eq-htpyᵉ _)) ∙ᵉ
    ( invᵉ (apᵉ eq-htpyᵉ (compute-htpy-eq-invᵉ (eq-htpyᵉ Hᵉ))) ∙ᵉ
      apᵉ (eq-htpyᵉ ∘ᵉ inv-htpyᵉ) (is-section-eq-htpyᵉ _))

  compute-inv-eq-htpyᵉ :
    eq-htpyᵉ ∘ᵉ inv-htpyᵉ {fᵉ = fᵉ} {gᵉ} ~ᵉ invᵉ ∘ᵉ eq-htpyᵉ
  compute-inv-eq-htpyᵉ = inv-htpyᵉ compute-eq-htpy-inv-htpyᵉ
```

## See also

-ᵉ Theᵉ factᵉ thatᵉ theᵉ univalenceᵉ axiomᵉ impliesᵉ functionᵉ extensionalityᵉ isᵉ provenᵉ
  in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).ᵉ
-ᵉ Weakᵉ functionᵉ extensionalityᵉ isᵉ definedᵉ in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).ᵉ
-ᵉ Transportingᵉ alongᵉ homotopiesᵉ isᵉ definedᵉ in
  [`foundation.transport-along-homotopies`](foundation.transport-along-homotopies.md).ᵉ