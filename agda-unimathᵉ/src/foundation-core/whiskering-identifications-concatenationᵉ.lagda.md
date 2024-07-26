# Whiskering identifications with respect to concatenation

```agda
module foundation-core.whiskering-identifications-concatenationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-operationsᵉ

open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [identifications](foundation-core.identity-types.mdᵉ) `pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ
in aᵉ typeᵉ `A`.ᵉ Theᵉ whiskeringᵉ operationsᵉ areᵉ operationsᵉ thatᵉ takeᵉ
identificationsᵉ `pᵉ ＝ᵉ q`ᵉ to identificationsᵉ `rᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ ∙ᵉ q`ᵉ orᵉ to
identificationsᵉ `pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ r`.ᵉ

Theᵉ
{{#conceptᵉ "leftᵉ whiskering"ᵉ Disambiguation="identifications"ᵉ Agda=left-whisker-concatᵉ}}
operationᵉ takesᵉ anᵉ identificationᵉ `rᵉ : zᵉ ＝ᵉ x`ᵉ andᵉ anᵉ identificationᵉ `pᵉ ＝ᵉ q`ᵉ to
anᵉ identificationᵉ `rᵉ ∙ᵉ pᵉ ＝ᵉ rᵉ ∙ᵉ q`.ᵉ Similarly,ᵉ theᵉ
{{#conceptᵉ "rightᵉ whiskering"ᵉ Disambiguation="identifications"ᵉ Agda=right-whisker-concatᵉ}}
operationᵉ takesᵉ anᵉ identificationᵉ `rᵉ : yᵉ ＝ᵉ z`ᵉ andᵉ anᵉ identificationᵉ `pᵉ ＝ᵉ q`ᵉ to
anᵉ identificationᵉ `pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ r`.ᵉ

Theᵉ whiskeringᵉ operationsᵉ canᵉ beᵉ definedᵉ byᵉ theᵉ
[acionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ) ofᵉ
concatenation.ᵉ Sinceᵉ concatenationᵉ onᵉ eitherᵉ sideᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md),ᵉ itᵉ followsᵉ thatᵉ theᵉ whiskeringᵉ
operationsᵉ areᵉ equivalences.ᵉ

## Definitions

### Left whiskering of identifications

Leftᵉ whiskeringᵉ ofᵉ identificationsᵉ with respectᵉ to concatenationᵉ isᵉ anᵉ operationᵉ

```text
  (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} → qᵉ ＝ᵉ rᵉ → pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ rᵉ
```

onᵉ anyᵉ type.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-whisker-concatᵉ : left-whiskering-operationᵉ Aᵉ (_＝ᵉ_) (_∙ᵉ_) (_＝ᵉ_)
  left-whisker-concatᵉ pᵉ βᵉ = apᵉ (pᵉ ∙ᵉ_) βᵉ

  left-unwhisker-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} → pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ rᵉ → qᵉ ＝ᵉ rᵉ
  left-unwhisker-concatᵉ = is-injective-concatᵉ
```

### Right whiskering of identifications

Rightᵉ whiskeringᵉ ofᵉ identificationsᵉ with respectᵉ to concatenationᵉ isᵉ anᵉ
operationᵉ

```text
  {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ＝ᵉ qᵉ → (rᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ
```

onᵉ anyᵉ type.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  right-whisker-concatᵉ : right-whiskering-operationᵉ Aᵉ (_＝ᵉ_) (_∙ᵉ_) (_＝ᵉ_)
  right-whisker-concatᵉ αᵉ qᵉ = apᵉ (_∙ᵉ qᵉ) αᵉ

  right-unwhisker-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (rᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ → pᵉ ＝ᵉ qᵉ
  right-unwhisker-concatᵉ rᵉ = is-injective-concat'ᵉ rᵉ
```

### Double whiskering of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  {aᵉ bᵉ cᵉ dᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ sᵉ : bᵉ ＝ᵉ cᵉ} (tᵉ : rᵉ ＝ᵉ sᵉ) (qᵉ : cᵉ ＝ᵉ dᵉ)
  where

  double-whisker-concatᵉ : (pᵉ ∙ᵉ rᵉ) ∙ᵉ qᵉ ＝ᵉ (pᵉ ∙ᵉ sᵉ) ∙ᵉ qᵉ
  double-whisker-concatᵉ = right-whisker-concatᵉ (left-whisker-concatᵉ pᵉ tᵉ) qᵉ

  double-whisker-concat'ᵉ : pᵉ ∙ᵉ (rᵉ ∙ᵉ qᵉ) ＝ᵉ pᵉ ∙ᵉ (sᵉ ∙ᵉ qᵉ)
  double-whisker-concat'ᵉ = left-whisker-concatᵉ pᵉ (right-whisker-concatᵉ tᵉ qᵉ)
```

## Properties

### The unit and absorption laws for left whiskering of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-unit-law-left-whisker-concatᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    left-whisker-concatᵉ reflᵉ αᵉ ＝ᵉ αᵉ
  left-unit-law-left-whisker-concatᵉ reflᵉ = reflᵉ

  right-absorption-law-left-whisker-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    left-whisker-concatᵉ pᵉ (reflᵉ {xᵉ = qᵉ}) ＝ᵉ reflᵉ
  right-absorption-law-left-whisker-concatᵉ pᵉ qᵉ = reflᵉ
```

### The unit and absorption laws for right whiskering of identifications

Theᵉ rightᵉ unitᵉ lawᵉ forᵉ rightᵉ whiskeringᵉ ofᵉ identificationsᵉ with respectᵉ to
concatenationᵉ assertsᵉ thatᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                     right-whisker-concatᵉ αᵉ reflᵉ
           pᵉ ∙ᵉ reflᵉ ----------------------------->ᵉ p'ᵉ ∙ᵉ reflᵉ
             |                                        |
  right-unitᵉ |                                        |
             ∨ᵉ                                        ∨ᵉ
             pᵉ ------------------------------------->ᵉ p'ᵉ
```

commutesᵉ forᵉ anyᵉ `αᵉ : pᵉ ＝ᵉ p'`.ᵉ Noteᵉ thatᵉ thisᵉ lawᵉ isᵉ slightlyᵉ moreᵉ complicated,ᵉ
sinceᵉ concatenatingᵉ with `refl`ᵉ onᵉ theᵉ rightᵉ doesᵉ notᵉ computeᵉ to theᵉ identityᵉ
function.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  right-unit-law-right-whisker-concatᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    right-unitᵉ ∙ᵉ αᵉ ＝ᵉ right-whisker-concatᵉ αᵉ reflᵉ ∙ᵉ right-unitᵉ
  right-unit-law-right-whisker-concatᵉ {pᵉ = reflᵉ} reflᵉ = reflᵉ

  left-absorption-law-right-whisker-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    right-whisker-concatᵉ (reflᵉ {xᵉ = pᵉ}) qᵉ ＝ᵉ reflᵉ
  left-absorption-law-right-whisker-concatᵉ pᵉ qᵉ = reflᵉ
```

### Commutativity of left and right whiskering of identifications

Considerᵉ fourᵉ identificationsᵉ `pᵉ p'ᵉ : xᵉ ＝ᵉ y`ᵉ andᵉ `qᵉ q'ᵉ : yᵉ ＝ᵉ z`ᵉ in aᵉ typeᵉ `A`.ᵉ
Thenᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                         right-whiskerᵉ αᵉ qᵉ
                 pᵉ ∙ᵉ qᵉ --------------------->ᵉ p'ᵉ ∙ᵉ qᵉ
                   |                             |
  left-whiskerᵉ pᵉ βᵉ |                             | left-whiskerᵉ p'ᵉ βᵉ
                   ∨ᵉ                             ∨ᵉ
                 pᵉ ∙ᵉ q'ᵉ -------------------->ᵉ p'ᵉ ∙ᵉ q'ᵉ
                         right-whiskerᵉ αᵉ q'ᵉ
```

commutes.ᵉ Thereᵉ areᵉ atᵉ leastᵉ twoᵉ naturalᵉ waysᵉ in whichᵉ thisᵉ squareᵉ isᵉ seenᵉ to
commuteᵉ:

1.ᵉ Theᵉ squareᵉ commutesᵉ byᵉ naturalityᵉ ofᵉ theᵉ homotopyᵉ
   `pᵉ ↦ᵉ left-whisker-concatᵉ pᵉ β`.ᵉ
2.ᵉ Theᵉ transposedᵉ squareᵉ commutesᵉ byᵉ theᵉ naturalityᵉ ofᵉ theᵉ homotopyᵉ
   `qᵉ ↦ᵉ right-whisker-concatᵉ αᵉ q`.ᵉ

Theᵉ firstᵉ wayᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ braidingᵉ `β`ᵉ overᵉ `α`,ᵉ whileᵉ theᵉ secondᵉ canᵉ
beᵉ thoughtᵉ ofᵉ braidingᵉ `α`ᵉ underᵉ `β`.ᵉ Braidingᵉ `β`ᵉ overᵉ `α`,ᵉ thenᵉ braidingᵉ `α`ᵉ
underᵉ `β`ᵉ resultsᵉ in noᵉ braidᵉ atᵉ all.ᵉ Thus,ᵉ theseᵉ twoᵉ waysᵉ in whichᵉ theᵉ squareᵉ
commutesᵉ areᵉ inverseᵉ to eachᵉ other.ᵉ

**Note.**ᵉ Theᵉ followingᵉ statementsᵉ couldᵉ haveᵉ beenᵉ formalizedᵉ using
[commutingᵉ squaresᵉ ofᵉ identifications](foundation.commuting-squares-of-identifications.md).ᵉ
However,ᵉ in orderᵉ to avoidᵉ cyclicᵉ module dependenciesᵉ in theᵉ libraryᵉ weᵉ avoidᵉ
doingᵉ so.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} {qᵉ q'ᵉ : yᵉ ＝ᵉ zᵉ}
  where

  commutative-left-whisker-right-whisker-concatᵉ :
    (βᵉ : qᵉ ＝ᵉ q'ᵉ) (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    left-whisker-concatᵉ pᵉ βᵉ ∙ᵉ right-whisker-concatᵉ αᵉ q'ᵉ ＝ᵉ
    right-whisker-concatᵉ αᵉ qᵉ ∙ᵉ left-whisker-concatᵉ p'ᵉ βᵉ
  commutative-left-whisker-right-whisker-concatᵉ βᵉ =
    nat-htpyᵉ (λ pᵉ → left-whisker-concatᵉ pᵉ βᵉ)

  commutative-right-whisker-left-whisker-concatᵉ :
    (αᵉ : pᵉ ＝ᵉ p'ᵉ) (βᵉ : qᵉ ＝ᵉ q'ᵉ) →
    right-whisker-concatᵉ αᵉ qᵉ ∙ᵉ left-whisker-concatᵉ p'ᵉ βᵉ ＝ᵉ
    left-whisker-concatᵉ pᵉ βᵉ ∙ᵉ right-whisker-concatᵉ αᵉ q'ᵉ
  commutative-right-whisker-left-whisker-concatᵉ αᵉ =
    nat-htpyᵉ (right-whisker-concatᵉ αᵉ)

  compute-inv-commutative-right-whisker-left-whisker-concatᵉ :
    (βᵉ : qᵉ ＝ᵉ q'ᵉ) (αᵉ : pᵉ ＝ᵉ p'ᵉ) →
    ( invᵉ (commutative-right-whisker-left-whisker-concatᵉ αᵉ βᵉ)) ＝ᵉ
    ( commutative-left-whisker-right-whisker-concatᵉ βᵉ αᵉ)
  compute-inv-commutative-right-whisker-left-whisker-concatᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Swapping the order of left and right whiskering of identifications

Considerᵉ aᵉ diagramᵉ ofᵉ identificationsᵉ

```text
               rᵉ
      pᵉ      ----->ᵉ     qᵉ
  aᵉ ----->ᵉ bᵉ ----->ᵉ cᵉ ----->ᵉ
               sᵉ
```

with `tᵉ : rᵉ ＝ᵉ s`.ᵉ Thenᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                               assocᵉ pᵉ rᵉ qᵉ
                  (pᵉ ∙ᵉ rᵉ) ∙ᵉ qᵉ ------------->ᵉ pᵉ ∙ᵉ (rᵉ ∙ᵉ qᵉ)
                       |                          |
  double-whiskerᵉ pᵉ tᵉ qᵉ |                          | double-whisker'ᵉ pᵉ tᵉ qᵉ
                       ∨ᵉ                          ∨ᵉ
                  (pᵉ ∙ᵉ sᵉ) ∙ᵉ qᵉ ------------->ᵉ pᵉ ∙ᵉ (sᵉ ∙ᵉ qᵉ)
                               assocᵉ pᵉ sᵉ qᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  swap-double-whisker-concatᵉ :
    {aᵉ bᵉ cᵉ dᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ sᵉ : bᵉ ＝ᵉ cᵉ} (tᵉ : rᵉ ＝ᵉ sᵉ) (qᵉ : cᵉ ＝ᵉ dᵉ) →
    double-whisker-concatᵉ pᵉ tᵉ qᵉ ∙ᵉ assocᵉ pᵉ sᵉ qᵉ ＝ᵉ
    assocᵉ pᵉ rᵉ qᵉ ∙ᵉ double-whisker-concat'ᵉ pᵉ tᵉ qᵉ
  swap-double-whisker-concatᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```

### The action on identifications of concatenating by `refl` on the right

Considerᵉ anᵉ identificationᵉ `rᵉ : pᵉ ＝ᵉ q`ᵉ betweenᵉ twoᵉ identificationsᵉ
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ in aᵉ typeᵉ `A`.ᵉ Thenᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                      right-whiskerᵉ rᵉ reflᵉ
            pᵉ ∙ᵉ reflᵉ ---------------------->ᵉ qᵉ ∙ᵉ reflᵉ
              |                                |
   right-unitᵉ |                                | right-unitᵉ
              ∨ᵉ                                ∨ᵉ
              pᵉ ----------------------------->ᵉ qᵉ
                                rᵉ
```

commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ}
  where

  compute-refl-right-whisker-concatᵉ :
    (rᵉ : pᵉ ＝ᵉ qᵉ) →
    right-unitᵉ ∙ᵉ rᵉ ＝ᵉ right-whisker-concatᵉ rᵉ reflᵉ ∙ᵉ right-unitᵉ
  compute-refl-right-whisker-concatᵉ reflᵉ = right-unitᵉ
```

### Left whiskering of identifications distributes over concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  distributive-left-whisker-concat-concatᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ) {qᵉ rᵉ sᵉ : bᵉ ＝ᵉ cᵉ} (αᵉ : qᵉ ＝ᵉ rᵉ) (βᵉ : rᵉ ＝ᵉ sᵉ) →
    left-whisker-concatᵉ pᵉ (αᵉ ∙ᵉ βᵉ) ＝ᵉ
    left-whisker-concatᵉ pᵉ αᵉ ∙ᵉ left-whisker-concatᵉ pᵉ βᵉ
  distributive-left-whisker-concat-concatᵉ pᵉ reflᵉ βᵉ = reflᵉ
```

### Right whiskering of identifications distributes over concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  distributive-right-whisker-concat-concatᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} {pᵉ qᵉ rᵉ : aᵉ ＝ᵉ bᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ) (βᵉ : qᵉ ＝ᵉ rᵉ) (sᵉ : bᵉ ＝ᵉ cᵉ) →
    right-whisker-concatᵉ (αᵉ ∙ᵉ βᵉ) sᵉ ＝ᵉ
    right-whisker-concatᵉ αᵉ sᵉ ∙ᵉ right-whisker-concatᵉ βᵉ sᵉ
  distributive-right-whisker-concat-concatᵉ reflᵉ βᵉ sᵉ = reflᵉ
```

### Left whiskering of identifications commutes with inverses of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  compute-inv-left-whisker-concatᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ) {qᵉ rᵉ : bᵉ ＝ᵉ cᵉ} (sᵉ : qᵉ ＝ᵉ rᵉ) →
    left-whisker-concatᵉ pᵉ (invᵉ sᵉ) ＝ᵉ invᵉ (left-whisker-concatᵉ pᵉ sᵉ)
  compute-inv-left-whisker-concatᵉ pᵉ sᵉ = ap-invᵉ (concatᵉ pᵉ _) sᵉ
```

### Right whiskering of identifications commutes with inverses of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  compute-inv-right-whisker-concatᵉ :
    {aᵉ bᵉ cᵉ : Aᵉ} {pᵉ qᵉ : aᵉ ＝ᵉ bᵉ} (sᵉ : pᵉ ＝ᵉ qᵉ) (rᵉ : bᵉ ＝ᵉ cᵉ) →
    right-whisker-concatᵉ (invᵉ sᵉ) rᵉ ＝ᵉ invᵉ (right-whisker-concatᵉ sᵉ rᵉ)
  compute-inv-right-whisker-concatᵉ sᵉ rᵉ = ap-invᵉ (concat'ᵉ _ rᵉ) sᵉ
```