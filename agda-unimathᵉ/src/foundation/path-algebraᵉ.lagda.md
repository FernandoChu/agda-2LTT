# Path algebra

```agda
module foundation.path-algebraᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Asᵉ weᵉ iterateᵉ identityᵉ typeᵉ (i.e.,ᵉ considerᵉ theᵉ typeᵉ ofᵉ identificationsᵉ betweenᵉ
twoᵉ identifications),ᵉ theᵉ identityᵉ typesᵉ gainᵉ furtherᵉ structure.ᵉ

Identityᵉ typesᵉ ofᵉ identityᵉ typesᵉ areᵉ typesᵉ ofᵉ theᵉ formᵉ `pᵉ ＝ᵉ q`,ᵉ where
`pᵉ qᵉ : xᵉ ＝ᵉ y`ᵉ andᵉ `xᵉ yᵉ : A`.ᵉ Usingᵉ theᵉ homotopyᵉ interpretationᵉ ofᵉ typeᵉ theory,ᵉ
elementsᵉ ofᵉ suchᵉ aᵉ typeᵉ areᵉ oftenᵉ calledᵉ _2-pathsᵉ_ andᵉ aᵉ twiceᵉ iteratedᵉ identityᵉ
typeᵉ isᵉ oftenᵉ calledᵉ aᵉ _typeᵉ ofᵉ 2-paths_.ᵉ

Sinceᵉ 2-pathsᵉ areᵉ justᵉ identifications,ᵉ theyᵉ haveᵉ theᵉ usualᵉ operationsᵉ andᵉ
coherencesᵉ onᵉ paths/identifications.ᵉ Inᵉ theᵉ contextᵉ ofᵉ 2-paths,ᵉ thisᵉ famliarᵉ
concatenationᵉ operationᵉ isᵉ calledᵉ verticalᵉ concatenationᵉ (seeᵉ
`vertical-concat-Id²`ᵉ below).ᵉ However,ᵉ 2-pathsᵉ haveᵉ novelᵉ operationsᵉ andᵉ
coherencesᵉ derivedᵉ fromᵉ theᵉ operationsᵉ andᵉ coherencesᵉ ofᵉ theᵉ boundaryᵉ 1-pathsᵉ
(theseᵉ areᵉ `p`ᵉ andᵉ `q`ᵉ in theᵉ exampleᵉ above).ᵉ Sinceᵉ concatenationᵉ ofᵉ 1-pathsᵉ isᵉ
aᵉ functor,ᵉ itᵉ hasᵉ anᵉ inducedᵉ actionᵉ onᵉ paths.ᵉ Weᵉ callᵉ thisᵉ operationᵉ horizontalᵉ
concatenationᵉ (seeᵉ `horizontal-concat-Id²`ᵉ below).ᵉ Itᵉ comesᵉ with theᵉ standardᵉ
coherencesᵉ ofᵉ anᵉ actionᵉ onᵉ pathsᵉ function,ᵉ asᵉ wellᵉ asᵉ coherencesᵉ inducedᵉ byᵉ
coherencesᵉ onᵉ theᵉ boundaryᵉ 1-paths.ᵉ

## Properties

### The unit laws of concatenation induce homotopies

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {a0ᵉ a1ᵉ : Aᵉ}
  where

  htpy-left-unitᵉ : (λ (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) → reflᵉ {xᵉ = a0ᵉ} ∙ᵉ pᵉ) ~ᵉ idᵉ
  htpy-left-unitᵉ pᵉ = left-unitᵉ

  htpy-right-unitᵉ : (λ (pᵉ : a0ᵉ ＝ᵉ a1ᵉ) → pᵉ ∙ᵉ reflᵉ) ~ᵉ idᵉ
  htpy-right-unitᵉ pᵉ = right-unitᵉ
```

### Unit laws for `assoc`

Weᵉ giveᵉ twoᵉ treatmentsᵉ ofᵉ theᵉ unitᵉ lawsᵉ forᵉ theᵉ associator.ᵉ Oneᵉ forᵉ computingᵉ
with theᵉ associator,ᵉ andᵉ oneᵉ forᵉ coherencesᵉ betweenᵉ theᵉ unitᵉ laws.ᵉ

#### Computing `assoc` at a reflexivity

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  left-unit-law-assocᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ reflᵉ pᵉ qᵉ ＝ᵉ reflᵉ
  left-unit-law-assocᵉ pᵉ qᵉ = reflᵉ

  middle-unit-law-assocᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ pᵉ reflᵉ qᵉ ＝ᵉ right-whisker-concatᵉ right-unitᵉ qᵉ
  middle-unit-law-assocᵉ reflᵉ qᵉ = reflᵉ

  right-unit-law-assocᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ pᵉ qᵉ reflᵉ ＝ᵉ
      right-unitᵉ ∙ᵉ left-whisker-concatᵉ pᵉ (invᵉ right-unitᵉ)
  right-unit-law-assocᵉ reflᵉ reflᵉ = reflᵉ
```

#### Unit laws for `assoc` and their coherence

Weᵉ useᵉ aᵉ binaryᵉ namingᵉ schemeᵉ forᵉ theᵉ (higherᵉ) unitᵉ lawsᵉ ofᵉ theᵉ associator.ᵉ Forᵉ
eachᵉ 3-digitᵉ binaryᵉ numberᵉ exceptᵉ whenᵉ allᵉ digitsᵉ areᵉ `1`,ᵉ thereᵉ isᵉ aᵉ
correspondingᵉ unitᵉ law.ᵉ Aᵉ `0`ᵉ reflectsᵉ thatᵉ theᵉ unitᵉ ofᵉ theᵉ operatorᵉ isᵉ presentᵉ
in theᵉ correspondingᵉ position.ᵉ Moreᵉ generally,ᵉ thereᵉ isᵉ forᵉ eachᵉ `n`-digitᵉ
binaryᵉ numberᵉ (exceptᵉ allᵉ `1`sᵉ) aᵉ unitᵉ lawᵉ forᵉ theᵉ `n`-aryᵉ coherenceᵉ operator.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  unit-law-assoc-011ᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ reflᵉ pᵉ qᵉ ＝ᵉ reflᵉ
  unit-law-assoc-011ᵉ pᵉ qᵉ = reflᵉ

  unit-law-assoc-101ᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ pᵉ reflᵉ qᵉ ＝ᵉ right-whisker-concatᵉ right-unitᵉ qᵉ
  unit-law-assoc-101ᵉ reflᵉ qᵉ = reflᵉ

  unit-law-assoc-101'ᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    invᵉ (assocᵉ pᵉ reflᵉ qᵉ) ＝ᵉ right-whisker-concatᵉ (invᵉ right-unitᵉ) qᵉ
  unit-law-assoc-101'ᵉ reflᵉ qᵉ = reflᵉ

  unit-law-assoc-110ᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    assocᵉ pᵉ qᵉ reflᵉ ∙ᵉ left-whisker-concatᵉ pᵉ right-unitᵉ ＝ᵉ right-unitᵉ
  unit-law-assoc-110ᵉ reflᵉ reflᵉ = reflᵉ

  unit-law-assoc-110'ᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    invᵉ right-unitᵉ ∙ᵉ assocᵉ pᵉ qᵉ reflᵉ ＝ᵉ
    left-whisker-concatᵉ pᵉ (invᵉ right-unitᵉ)
  unit-law-assoc-110'ᵉ reflᵉ reflᵉ = reflᵉ
```

## Properties of 2-paths

### Definition of vertical and horizontal concatenation in identity types of identity types (a type of 2-paths)

```agda
vertical-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ＝ᵉ qᵉ → qᵉ ＝ᵉ rᵉ → pᵉ ＝ᵉ rᵉ
vertical-concat-Id²ᵉ αᵉ βᵉ = αᵉ ∙ᵉ βᵉ

horizontal-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ} →
  pᵉ ＝ᵉ qᵉ → uᵉ ＝ᵉ vᵉ → pᵉ ∙ᵉ uᵉ ＝ᵉ qᵉ ∙ᵉ vᵉ
horizontal-concat-Id²ᵉ αᵉ βᵉ = ap-binaryᵉ (_∙ᵉ_) αᵉ βᵉ
```

### Both horizontal and vertical concatenation of 2-paths are binary equivalences

```agda
is-binary-equiv-vertical-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} →
  is-binary-equivᵉ (vertical-concat-Id²ᵉ {lᵉ} {Aᵉ} {xᵉ} {yᵉ} {pᵉ} {qᵉ} {rᵉ})
is-binary-equiv-vertical-concat-Id²ᵉ = is-binary-equiv-concatᵉ

is-binary-equiv-horizontal-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ} →
  is-binary-equivᵉ (horizontal-concat-Id²ᵉ {lᵉ} {Aᵉ} {xᵉ} {yᵉ} {zᵉ} {pᵉ} {qᵉ} {uᵉ} {vᵉ})
is-binary-equiv-horizontal-concat-Id²ᵉ =
  is-binary-emb-is-binary-equivᵉ is-binary-equiv-concatᵉ
```

### Unit laws for horizontal and vertical concatenation of 2-paths

```agda
left-unit-law-vertical-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {βᵉ : pᵉ ＝ᵉ qᵉ} →
  vertical-concat-Id²ᵉ reflᵉ βᵉ ＝ᵉ βᵉ
left-unit-law-vertical-concat-Id²ᵉ = left-unitᵉ

right-unit-law-vertical-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ : pᵉ ＝ᵉ qᵉ} →
  vertical-concat-Id²ᵉ αᵉ reflᵉ ＝ᵉ αᵉ
right-unit-law-vertical-concat-Id²ᵉ = right-unitᵉ

compute-left-refl-horizontal-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ} (γᵉ : uᵉ ＝ᵉ vᵉ) →
  horizontal-concat-Id²ᵉ reflᵉ γᵉ ＝ᵉ left-whisker-concatᵉ pᵉ γᵉ
compute-left-refl-horizontal-concat-Id²ᵉ = left-unit-ap-binaryᵉ (_∙ᵉ_)

compute-right-refl-horizontal-concat-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ) {uᵉ : yᵉ ＝ᵉ zᵉ} →
  horizontal-concat-Id²ᵉ αᵉ reflᵉ ＝ᵉ right-whisker-concatᵉ αᵉ uᵉ
compute-right-refl-horizontal-concat-Id²ᵉ = right-unit-ap-binaryᵉ (_∙ᵉ_)
```

Horizontalᵉ concatenationᵉ satisfiesᵉ anᵉ additionalᵉ "2-dimensional"ᵉ unitᵉ lawᵉ (onᵉ
bothᵉ theᵉ leftᵉ andᵉ rightᵉ) inducedᵉ byᵉ theᵉ unitᵉ lawsᵉ onᵉ theᵉ boundaryᵉ 1-paths.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ)
  where

  nat-sq-right-unit-Id²ᵉ :
    coherence-square-identificationsᵉ
      ( horizontal-concat-Id²ᵉ αᵉ reflᵉ)
      ( right-unitᵉ)
      ( right-unitᵉ)
      ( αᵉ)
  nat-sq-right-unit-Id²ᵉ =
    ( ( horizontal-concat-Id²ᵉ reflᵉ (invᵉ (ap-idᵉ αᵉ))) ∙ᵉ
      ( nat-htpyᵉ htpy-right-unitᵉ αᵉ)) ∙ᵉ
    ( horizontal-concat-Id²ᵉ
      ( invᵉ (compute-right-refl-horizontal-concat-Id²ᵉ αᵉ))
      ( reflᵉ))

  nat-sq-left-unit-Id²ᵉ :
    coherence-square-identificationsᵉ
      ( horizontal-concat-Id²ᵉ reflᵉ αᵉ)
      ( left-unitᵉ)
      ( left-unitᵉ)
      ( αᵉ)
  nat-sq-left-unit-Id²ᵉ =
    ( ( (invᵉ (ap-idᵉ αᵉ) ∙ᵉ (nat-htpyᵉ htpy-left-unitᵉ αᵉ)) ∙ᵉ right-unitᵉ) ∙ᵉ
      ( invᵉ (compute-left-refl-horizontal-concat-Id²ᵉ αᵉ))) ∙ᵉ
    ( invᵉ right-unitᵉ)
```

### Vertical inverses distribute over horizontal concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  where

  distributive-inv-horizontal-concat-Id²ᵉ :
    (αᵉ : pᵉ ＝ᵉ qᵉ) (βᵉ : uᵉ ＝ᵉ vᵉ) →
    invᵉ (horizontal-concat-Id²ᵉ αᵉ βᵉ) ＝ᵉ horizontal-concat-Id²ᵉ (invᵉ αᵉ) (invᵉ βᵉ)
  distributive-inv-horizontal-concat-Id²ᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Definition of horizontal inverse

2-pathsᵉ haveᵉ anᵉ inducedᵉ inverseᵉ operationᵉ fromᵉ theᵉ operationᵉ onᵉ boundaryᵉ 1-pathsᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ}
  where

  horizontal-inv-Id²ᵉ : pᵉ ＝ᵉ p'ᵉ → invᵉ pᵉ ＝ᵉ invᵉ p'ᵉ
  horizontal-inv-Id²ᵉ = apᵉ invᵉ
```

Thisᵉ operationᵉ satisfiesᵉ aᵉ leftᵉ andᵉ rightᵉ idenityᵉ inducedᵉ byᵉ theᵉ inverseᵉ lawsᵉ onᵉ
1-pathsᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ p'ᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ p'ᵉ)
  where

  nat-sq-right-inv-Id²ᵉ :
    coherence-square-identificationsᵉ
      ( horizontal-concat-Id²ᵉ αᵉ (horizontal-inv-Id²ᵉ αᵉ))
      ( right-invᵉ pᵉ)
      ( right-invᵉ p'ᵉ)
      ( reflᵉ)
  nat-sq-right-inv-Id²ᵉ =
    ( ( ( horizontal-concat-Id²ᵉ reflᵉ (invᵉ (ap-constᵉ reflᵉ αᵉ))) ∙ᵉ
        ( nat-htpyᵉ right-invᵉ αᵉ)) ∙ᵉ
      ( horizontal-concat-Id²ᵉ
        ( ap-binary-comp-diagonalᵉ (_∙ᵉ_) idᵉ invᵉ αᵉ)
        ( reflᵉ))) ∙ᵉ
    ( apᵉ
      ( λ tᵉ → horizontal-concat-Id²ᵉ tᵉ (horizontal-inv-Id²ᵉ αᵉ) ∙ᵉ right-invᵉ p'ᵉ)
      ( ap-idᵉ αᵉ))

  nat-sq-left-inv-Id²ᵉ :
    coherence-square-identificationsᵉ
      ( horizontal-concat-Id²ᵉ (horizontal-inv-Id²ᵉ αᵉ) αᵉ)
      ( left-invᵉ pᵉ)
      ( left-invᵉ p'ᵉ)
      ( reflᵉ)
  nat-sq-left-inv-Id²ᵉ =
    ( ( ( horizontal-concat-Id²ᵉ reflᵉ (invᵉ (ap-constᵉ reflᵉ αᵉ))) ∙ᵉ
        ( nat-htpyᵉ left-invᵉ αᵉ)) ∙ᵉ
      ( horizontal-concat-Id²ᵉ
        ( ap-binary-comp-diagonalᵉ (_∙ᵉ_) invᵉ idᵉ αᵉ)
        ( reflᵉ))) ∙ᵉ
    ( apᵉ
      ( λ tᵉ → (horizontal-concat-Id²ᵉ (horizontal-inv-Id²ᵉ αᵉ) tᵉ) ∙ᵉ left-invᵉ p'ᵉ)
      ( ap-idᵉ αᵉ))
```

### Interchange laws for 2-paths

```agda
interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ wᵉ : yᵉ ＝ᵉ zᵉ}
  (αᵉ : pᵉ ＝ᵉ qᵉ) (βᵉ : qᵉ ＝ᵉ rᵉ) (γᵉ : uᵉ ＝ᵉ vᵉ) (δᵉ : vᵉ ＝ᵉ wᵉ) →
  ( horizontal-concat-Id²ᵉ
    ( vertical-concat-Id²ᵉ αᵉ βᵉ)
    ( vertical-concat-Id²ᵉ γᵉ δᵉ)) ＝ᵉ
  ( vertical-concat-Id²ᵉ
    ( horizontal-concat-Id²ᵉ αᵉ γᵉ)
    ( horizontal-concat-Id²ᵉ βᵉ δᵉ))
interchange-Id²ᵉ reflᵉ _ reflᵉ _ = reflᵉ

inner-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  (βᵉ : pᵉ ＝ᵉ rᵉ) (γᵉ : uᵉ ＝ᵉ vᵉ) →
  ( horizontal-concat-Id²ᵉ βᵉ γᵉ) ＝ᵉ
  ( vertical-concat-Id²ᵉ (left-whisker-concatᵉ pᵉ γᵉ) (right-whisker-concatᵉ βᵉ vᵉ))
inner-interchange-Id²ᵉ {uᵉ = reflᵉ} βᵉ reflᵉ =
  compute-right-refl-horizontal-concat-Id²ᵉ βᵉ

outer-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ wᵉ : yᵉ ＝ᵉ zᵉ}
  (αᵉ : pᵉ ＝ᵉ qᵉ) (δᵉ : uᵉ ＝ᵉ wᵉ) →
  ( horizontal-concat-Id²ᵉ αᵉ δᵉ) ＝ᵉ
  ( vertical-concat-Id²ᵉ (right-whisker-concatᵉ αᵉ uᵉ) (left-whisker-concatᵉ qᵉ δᵉ))
outer-interchange-Id²ᵉ {pᵉ = reflᵉ} reflᵉ δᵉ =
  compute-left-refl-horizontal-concat-Id²ᵉ δᵉ

unit-law-α-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ) (uᵉ : yᵉ ＝ᵉ zᵉ) →
  ( ( interchange-Id²ᵉ αᵉ reflᵉ (reflᵉ {xᵉ = uᵉ}) reflᵉ) ∙ᵉ
    ( right-unitᵉ ∙ᵉ compute-right-refl-horizontal-concat-Id²ᵉ αᵉ)) ＝ᵉ
  ( ( compute-right-refl-horizontal-concat-Id²ᵉ (αᵉ ∙ᵉ reflᵉ)) ∙ᵉ
    ( apᵉ (λ sᵉ → right-whisker-concatᵉ sᵉ uᵉ) right-unitᵉ))
unit-law-α-interchange-Id²ᵉ reflᵉ _ = reflᵉ

unit-law-β-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (βᵉ : pᵉ ＝ᵉ qᵉ) (uᵉ : yᵉ ＝ᵉ zᵉ) →
  interchange-Id²ᵉ reflᵉ βᵉ (reflᵉ {xᵉ = uᵉ}) reflᵉ ＝ᵉ reflᵉ
unit-law-β-interchange-Id²ᵉ reflᵉ _ = reflᵉ

unit-law-γ-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ} (γᵉ : uᵉ ＝ᵉ vᵉ) →
  ( ( interchange-Id²ᵉ (reflᵉ {xᵉ = pᵉ}) reflᵉ γᵉ reflᵉ) ∙ᵉ
    ( right-unitᵉ ∙ᵉ compute-left-refl-horizontal-concat-Id²ᵉ γᵉ)) ＝ᵉ
  ( ( compute-left-refl-horizontal-concat-Id²ᵉ (γᵉ ∙ᵉ reflᵉ)) ∙ᵉ
    ( apᵉ (left-whisker-concatᵉ pᵉ) right-unitᵉ))
unit-law-γ-interchange-Id²ᵉ _ reflᵉ = reflᵉ

unit-law-δ-interchange-Id²ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ} (δᵉ : uᵉ ＝ᵉ vᵉ) →
  interchange-Id²ᵉ (reflᵉ {xᵉ = pᵉ}) reflᵉ reflᵉ δᵉ ＝ᵉ reflᵉ
unit-law-δ-interchange-Id²ᵉ _ reflᵉ = reflᵉ
```

## Properties of 3-paths

3-pathsᵉ areᵉ identificationsᵉ ofᵉ 2-paths.ᵉ Inᵉ symbols,ᵉ aᵉ typeᵉ ofᵉ 3-pathsᵉ isᵉ aᵉ typeᵉ
ofᵉ theᵉ formᵉ `αᵉ ＝ᵉ β`ᵉ where `αᵉ βᵉ : pᵉ ＝ᵉ q`ᵉ andᵉ `pᵉ qᵉ : xᵉ ＝ᵉ y`.ᵉ

### Concatenation in a type of 3-paths

Likeᵉ with 2-paths,ᵉ 3-pathsᵉ haveᵉ theᵉ standardᵉ operationsᵉ onᵉ equalties,ᵉ plusᵉ theᵉ
operationsᵉ inducedᵉ byᵉ theᵉ operationsᵉ onᵉ 1-paths.ᵉ Butᵉ 3-pathsᵉ alsoᵉ haveᵉ
operationsᵉ inducedᵉ byᵉ thoseᵉ onᵉ 2-paths.ᵉ Thusᵉ thereᵉ areᵉ threeᵉ waysᵉ to concatenateᵉ
in tripleᵉ identityᵉ types.ᵉ Weᵉ nameᵉ theᵉ threeᵉ concatenationsᵉ ofᵉ tripleᵉ identityᵉ
typesᵉ x-,ᵉ y-,ᵉ andᵉ z-concatenation,ᵉ afterᵉ theᵉ standardᵉ namesᵉ forᵉ theᵉ threeᵉ axisᵉ
in 3-dimensionalᵉ space.ᵉ

Theᵉ x-concatenationᵉ operationᵉ correspondsᵉ theᵉ standardᵉ concatenationᵉ ofᵉ
equalities.ᵉ

```agda
x-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ γᵉ : pᵉ ＝ᵉ qᵉ} →
  αᵉ ＝ᵉ βᵉ → βᵉ ＝ᵉ γᵉ → αᵉ ＝ᵉ γᵉ
x-concat-Id³ᵉ σᵉ τᵉ = vertical-concat-Id²ᵉ σᵉ τᵉ
```

Theᵉ y-concatenationᵉ operationᵉ correspondsᵉ theᵉ operationᵉ inducedᵉ byᵉ theᵉ
concatenationᵉ onᵉ 1-paths.ᵉ

```agda
y-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ}
  {γᵉ δᵉ : qᵉ ＝ᵉ rᵉ} → αᵉ ＝ᵉ βᵉ → γᵉ ＝ᵉ δᵉ → (αᵉ ∙ᵉ γᵉ) ＝ᵉ (βᵉ ∙ᵉ δᵉ)
y-concat-Id³ᵉ = horizontal-concat-Id²ᵉ
```

Theᵉ z-concatenationᵉ operationᵉ correspondsᵉ theᵉ concatenationᵉ inducedᵉ byᵉ theᵉ
horizontalᵉ concatenationᵉ onᵉ 2-paths.ᵉ

```agda
z-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ δᵉ : uᵉ ＝ᵉ vᵉ} →
  αᵉ ＝ᵉ βᵉ → γᵉ ＝ᵉ δᵉ → horizontal-concat-Id²ᵉ αᵉ γᵉ ＝ᵉ horizontal-concat-Id²ᵉ βᵉ δᵉ
z-concat-Id³ᵉ σᵉ τᵉ = ap-binaryᵉ horizontal-concat-Id²ᵉ σᵉ τᵉ
```

### Unit laws for the concatenation operations on 3-paths

```agda
left-unit-law-x-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {σᵉ : αᵉ ＝ᵉ βᵉ} →
  x-concat-Id³ᵉ reflᵉ σᵉ ＝ᵉ σᵉ
left-unit-law-x-concat-Id³ᵉ = left-unit-law-vertical-concat-Id²ᵉ

right-unit-law-x-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {τᵉ : αᵉ ＝ᵉ βᵉ} →
  x-concat-Id³ᵉ τᵉ reflᵉ ＝ᵉ τᵉ
right-unit-law-x-concat-Id³ᵉ = right-unit-law-vertical-concat-Id²ᵉ

left-unit-law-y-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ δᵉ : qᵉ ＝ᵉ rᵉ}
  {τᵉ : γᵉ ＝ᵉ δᵉ} →
  y-concat-Id³ᵉ (reflᵉ {xᵉ = αᵉ}) τᵉ ＝ᵉ left-whisker-concatᵉ αᵉ τᵉ
left-unit-law-y-concat-Id³ᵉ {τᵉ = τᵉ} = compute-left-refl-horizontal-concat-Id²ᵉ τᵉ

right-unit-law-y-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ : qᵉ ＝ᵉ rᵉ}
  {σᵉ : αᵉ ＝ᵉ βᵉ} →
  y-concat-Id³ᵉ σᵉ (reflᵉ {xᵉ = γᵉ}) ＝ᵉ right-whisker-concatᵉ σᵉ γᵉ
right-unit-law-y-concat-Id³ᵉ {σᵉ = σᵉ} = compute-right-refl-horizontal-concat-Id²ᵉ σᵉ

left-unit-law-z-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ δᵉ : uᵉ ＝ᵉ vᵉ} (τᵉ : γᵉ ＝ᵉ δᵉ) →
  z-concat-Id³ᵉ (reflᵉ {xᵉ = αᵉ}) τᵉ ＝ᵉ apᵉ (horizontal-concat-Id²ᵉ αᵉ) τᵉ
left-unit-law-z-concat-Id³ᵉ {αᵉ = αᵉ} =
  left-unit-ap-binaryᵉ horizontal-concat-Id²ᵉ {αᵉ}

right-unit-law-z-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ : uᵉ ＝ᵉ vᵉ} (σᵉ : αᵉ ＝ᵉ βᵉ) →
  z-concat-Id³ᵉ σᵉ (reflᵉ {xᵉ = γᵉ}) ＝ᵉ apᵉ (λ ωᵉ → horizontal-concat-Id²ᵉ ωᵉ γᵉ) σᵉ
right-unit-law-z-concat-Id³ᵉ σᵉ =
  right-unit-ap-binaryᵉ horizontal-concat-Id²ᵉ σᵉ
```

### Interchange laws for 3-paths for the concatenation operations on 3-paths

```agda
interchange-x-y-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ γᵉ : pᵉ ＝ᵉ qᵉ}
  {δᵉ εᵉ ζᵉ : qᵉ ＝ᵉ rᵉ} (σᵉ : αᵉ ＝ᵉ βᵉ) (τᵉ : βᵉ ＝ᵉ γᵉ) (υᵉ : δᵉ ＝ᵉ εᵉ) (ϕᵉ : εᵉ ＝ᵉ ζᵉ) →
  ( y-concat-Id³ᵉ (x-concat-Id³ᵉ σᵉ τᵉ) (x-concat-Id³ᵉ υᵉ ϕᵉ)) ＝ᵉ
  ( x-concat-Id³ᵉ (y-concat-Id³ᵉ σᵉ υᵉ) (y-concat-Id³ᵉ τᵉ ϕᵉ))
interchange-x-y-concat-Id³ᵉ = interchange-Id²ᵉ

interchange-x-z-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ βᵉ γᵉ : pᵉ ＝ᵉ qᵉ} {δᵉ εᵉ ζᵉ : uᵉ ＝ᵉ vᵉ} (σᵉ : αᵉ ＝ᵉ βᵉ) (τᵉ : βᵉ ＝ᵉ γᵉ) (υᵉ : δᵉ ＝ᵉ εᵉ)
  (ϕᵉ : εᵉ ＝ᵉ ζᵉ) →
  ( z-concat-Id³ᵉ (x-concat-Id³ᵉ σᵉ τᵉ) (x-concat-Id³ᵉ υᵉ ϕᵉ)) ＝ᵉ
  ( x-concat-Id³ᵉ (z-concat-Id³ᵉ σᵉ υᵉ) (z-concat-Id³ᵉ τᵉ ϕᵉ))
interchange-x-z-concat-Id³ᵉ reflᵉ τᵉ reflᵉ ϕᵉ = reflᵉ

interchange-y-z-concat-Id³ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ wᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ δᵉ : qᵉ ＝ᵉ rᵉ} {εᵉ ζᵉ : uᵉ ＝ᵉ vᵉ} {ηᵉ θᵉ : vᵉ ＝ᵉ wᵉ}
  (σᵉ : αᵉ ＝ᵉ βᵉ) (τᵉ : γᵉ ＝ᵉ δᵉ) (υᵉ : εᵉ ＝ᵉ ζᵉ) (ϕᵉ : ηᵉ ＝ᵉ θᵉ) →
  ( ( z-concat-Id³ᵉ (y-concat-Id³ᵉ σᵉ τᵉ) (y-concat-Id³ᵉ υᵉ ϕᵉ)) ∙ᵉ
    ( interchange-Id²ᵉ βᵉ δᵉ ζᵉ θᵉ)) ＝ᵉ
  ( ( interchange-Id²ᵉ αᵉ γᵉ εᵉ ηᵉ) ∙ᵉ
    ( y-concat-Id³ᵉ (z-concat-Id³ᵉ σᵉ υᵉ) (z-concat-Id³ᵉ τᵉ ϕᵉ)))
interchange-y-z-concat-Id³ᵉ reflᵉ reflᵉ reflᵉ reflᵉ = invᵉ right-unitᵉ
```

## Properties of 4-paths

Theᵉ pattern forᵉ concatenationᵉ ofᵉ 1,ᵉ 2,ᵉ andᵉ 3-pathsᵉ continues.ᵉ Thereᵉ areᵉ fourᵉ
waysᵉ to concatenateᵉ in quadrupleᵉ identityᵉ types.ᵉ Weᵉ nameᵉ theᵉ threeᵉ nonstandardᵉ
concatenationsᵉ in quadrupleᵉ identityᵉ typesᵉ `i`-,ᵉ `j`-,ᵉ andᵉ `k`-concatenation,ᵉ
afterᵉ theᵉ standardᵉ namesᵉ forᵉ theᵉ quaternionsᵉ `i`,ᵉ `j`,ᵉ andᵉ `k`.ᵉ

### Concatenation of four paths

#### The standard concatenation

```agda
concat-Id⁴ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ}
  {rᵉ sᵉ tᵉ : αᵉ ＝ᵉ βᵉ} → rᵉ ＝ᵉ sᵉ → sᵉ ＝ᵉ tᵉ → rᵉ ＝ᵉ tᵉ
concat-Id⁴ᵉ σᵉ τᵉ = x-concat-Id³ᵉ σᵉ τᵉ
```

#### Concatenation induced by concatenation of boundary 1-paths

```agda
i-concat-Id⁴ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ γᵉ : pᵉ ＝ᵉ qᵉ} →
  {sᵉ s'ᵉ : αᵉ ＝ᵉ βᵉ} (σᵉ : sᵉ ＝ᵉ s'ᵉ) {tᵉ t'ᵉ : βᵉ ＝ᵉ γᵉ} (τᵉ : tᵉ ＝ᵉ t'ᵉ) →
  x-concat-Id³ᵉ sᵉ tᵉ ＝ᵉ x-concat-Id³ᵉ s'ᵉ t'ᵉ
i-concat-Id⁴ᵉ σᵉ τᵉ = y-concat-Id³ᵉ σᵉ τᵉ
```

#### Concatenation induced by concatenation of boundary 2-paths

```agda
j-concat-Id⁴ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ rᵉ : xᵉ ＝ᵉ yᵉ} {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ}
  {γᵉ δᵉ : qᵉ ＝ᵉ rᵉ} {sᵉ s'ᵉ : αᵉ ＝ᵉ βᵉ} (σᵉ : sᵉ ＝ᵉ s'ᵉ) {tᵉ t'ᵉ : γᵉ ＝ᵉ δᵉ} (τᵉ : tᵉ ＝ᵉ t'ᵉ) →
  y-concat-Id³ᵉ sᵉ tᵉ ＝ᵉ y-concat-Id³ᵉ s'ᵉ t'ᵉ
j-concat-Id⁴ᵉ σᵉ τᵉ = z-concat-Id³ᵉ σᵉ τᵉ
```

#### Concatenation induced by concatenation of boundary 3-paths

```agda
k-concat-Id⁴ᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} {uᵉ vᵉ : yᵉ ＝ᵉ zᵉ}
  {αᵉ βᵉ : pᵉ ＝ᵉ qᵉ} {γᵉ δᵉ : uᵉ ＝ᵉ vᵉ} {sᵉ s'ᵉ : αᵉ ＝ᵉ βᵉ} (σᵉ : sᵉ ＝ᵉ s'ᵉ) {tᵉ t'ᵉ : γᵉ ＝ᵉ δᵉ}
  (τᵉ : tᵉ ＝ᵉ t'ᵉ) → z-concat-Id³ᵉ sᵉ tᵉ ＝ᵉ z-concat-Id³ᵉ s'ᵉ t'ᵉ
k-concat-Id⁴ᵉ σᵉ τᵉ = ap-binaryᵉ (λ mᵉ nᵉ → z-concat-Id³ᵉ mᵉ nᵉ) σᵉ τᵉ
```

### Commuting cubes

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {x000ᵉ x001ᵉ x010ᵉ x100ᵉ x011ᵉ x101ᵉ x110ᵉ x111ᵉ : Aᵉ}
  where

  coherence-cube-identificationsᵉ :
    (p000̂ᵉ : x000ᵉ ＝ᵉ x001ᵉ) (p00̂0ᵉ : x000ᵉ ＝ᵉ x010ᵉ) (p0̂00ᵉ : x000ᵉ ＝ᵉ x100ᵉ)
    (p00̂1ᵉ : x001ᵉ ＝ᵉ x011ᵉ) (p0̂01ᵉ : x001ᵉ ＝ᵉ x101ᵉ) (p010̂ᵉ : x010ᵉ ＝ᵉ x011ᵉ)
    (p0̂10ᵉ : x010ᵉ ＝ᵉ x110ᵉ) (p100̂ᵉ : x100ᵉ ＝ᵉ x101ᵉ) (p10̂0ᵉ : x100ᵉ ＝ᵉ x110ᵉ)
    (p0̂11ᵉ : x011ᵉ ＝ᵉ x111ᵉ) (p10̂1ᵉ : x101ᵉ ＝ᵉ x111ᵉ) (p110̂ᵉ : x110ᵉ ＝ᵉ x111ᵉ)
    (p00̂0̂ᵉ : coherence-square-identificationsᵉ p00̂0ᵉ p000̂ᵉ p010̂ᵉ p00̂1ᵉ)
    (p0̂00̂ᵉ : coherence-square-identificationsᵉ p0̂00ᵉ p000̂ᵉ p100̂ᵉ p0̂01ᵉ)
    (p0̂0̂0ᵉ : coherence-square-identificationsᵉ p0̂00ᵉ p00̂0ᵉ p10̂0ᵉ p0̂10ᵉ)
    (p0̂0̂1ᵉ : coherence-square-identificationsᵉ p0̂01ᵉ p00̂1ᵉ p10̂1ᵉ p0̂11ᵉ)
    (p0̂10̂ᵉ : coherence-square-identificationsᵉ p0̂10ᵉ p010̂ᵉ p110̂ᵉ p0̂11ᵉ)
    (p10̂0̂ᵉ : coherence-square-identificationsᵉ p10̂0ᵉ p100̂ᵉ p110̂ᵉ p10̂1ᵉ) → UUᵉ lᵉ
  coherence-cube-identificationsᵉ
    p000̂ᵉ p00̂0ᵉ p0̂00ᵉ p00̂1ᵉ p0̂01ᵉ p010̂ᵉ p0̂10ᵉ p100̂ᵉ p10̂0ᵉ p0̂11ᵉ p10̂1ᵉ p110̂ᵉ
    p00̂0̂ᵉ p0̂00̂ᵉ p0̂0̂0ᵉ p0̂0̂1ᵉ p0̂10̂ᵉ p10̂0̂ᵉ =
    Idᵉ
      ( ( right-whisker-concatᵉ p00̂0̂ᵉ p0̂11ᵉ) ∙ᵉ
        ( ( assocᵉ p00̂0ᵉ p010̂ᵉ p0̂11ᵉ) ∙ᵉ
          ( ( left-whisker-concatᵉ p00̂0ᵉ p0̂10̂ᵉ) ∙ᵉ
            ( ( invᵉ (assocᵉ p00̂0ᵉ p0̂10ᵉ p110̂ᵉ)) ∙ᵉ
              ( ( right-whisker-concatᵉ p0̂0̂0ᵉ p110̂ᵉ) ∙ᵉ
                ( assocᵉ p0̂00ᵉ p10̂0ᵉ p110̂ᵉ))))))
      ( ( assocᵉ p000̂ᵉ p00̂1ᵉ p0̂11ᵉ) ∙ᵉ
        ( ( left-whisker-concatᵉ p000̂ᵉ p0̂0̂1ᵉ) ∙ᵉ
          ( ( invᵉ (assocᵉ p000̂ᵉ p0̂01ᵉ p10̂1ᵉ)) ∙ᵉ
            ( ( right-whisker-concatᵉ p0̂00̂ᵉ p10̂1ᵉ) ∙ᵉ
              ( ( assocᵉ p0̂00ᵉ p100̂ᵉ p10̂1ᵉ) ∙ᵉ
                ( ( left-whisker-concatᵉ p0̂00ᵉ p10̂0̂ᵉ)))))))
```