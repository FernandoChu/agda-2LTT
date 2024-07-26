# The Eckmann-Hilton argument

```agda
module synthetic-homotopy-theory.eckmann-hilton-argumentᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
open import foundation.path-algebraᵉ
open import foundation.transport-along-higher-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-concatenationᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.double-loop-spacesᵉ
open import synthetic-homotopy-theory.functoriality-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.triple-loop-spacesᵉ
```

</details>

## Idea

Thereᵉ areᵉ twoᵉ classicalᵉ statementsᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argument.ᵉ Theᵉ firstᵉ
statesᵉ thatᵉ aᵉ groupᵉ objectᵉ in theᵉ
[categoryᵉ ofᵉ groups](group-theory.category-of-groups.mdᵉ) isᵉ
[abelian](group-theory.abelian-groups.md).ᵉ Theᵉ secondᵉ statesᵉ thatᵉ `π₂(X)`ᵉ isᵉ
abelian,ᵉ forᵉ anyᵉ spaceᵉ `X`.ᵉ Theᵉ formerᵉ isᵉ anᵉ algebraicᵉ statement,ᵉ whileᵉ theᵉ
latterᵉ isᵉ aᵉ homotopyᵉ theoreticᵉ statment.ᵉ Asᵉ itᵉ turnsᵉ out,ᵉ theᵉ twoᵉ areᵉ
[equivalent](foundation.logical-equivalences.md).ᵉ Seeᵉ theᵉ followingᵉ
[Wikipediaᵉ article](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument#Two-dimensional_proof).ᵉ

Bothᵉ ofᵉ theseᵉ phrasings,ᵉ however,ᵉ areᵉ aboutᵉ [set](foundation-core.sets.mdᵉ) levelᵉ
structures.ᵉ Sinceᵉ weᵉ haveᵉ accessᵉ to untruncatedᵉ types,ᵉ itᵉ isᵉ moreᵉ naturalᵉ to
considerᵉ untruncatedᵉ analogsᵉ ofᵉ theᵉ aboveᵉ twoᵉ statements.ᵉ Thus,ᵉ weᵉ willᵉ workᵉ
with theᵉ followingᵉ statementᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argumentᵉ:

```text
  (αᵉ βᵉ : Ω²ᵉ Xᵉ) → αᵉ ∙ᵉ βᵉ = βᵉ ∙ᵉ αᵉ
```

Forᵉ fixedᵉ 2-loops,ᵉ weᵉ willᵉ callᵉ theᵉ resultingᵉ identificationᵉ "theᵉ Eckmann-Hiltonᵉ
identification".ᵉ Inᵉ thisᵉ fileᵉ weᵉ willᵉ giveᵉ twoᵉ differentᵉ constructionsᵉ ofᵉ thisᵉ
identification,ᵉ oneᵉ thatᵉ correspondsᵉ to theᵉ moreᵉ algebraicᵉ statementᵉ andᵉ oneᵉ
thatᵉ correspondsᵉ to theᵉ moreᵉ homotopyᵉ theoreticᵉ statement.ᵉ Weᵉ willᵉ callᵉ theᵉ
constructionsᵉ themselvesᵉ "theᵉ Eckmann-Hiltonᵉ argument".ᵉ

## Definitions

### Constructing the Eckmann-Hilton identification from the interchange law

Theᵉ moreᵉ algebraicᵉ argumentᵉ usesᵉ theᵉ interchangeᵉ lawᵉ
[`interchange-Ω²`](synthetic-homotopy-theory.double-loop-spaces.md).ᵉ Theᵉ
interchangeᵉ lawᵉ essentiallyᵉ expressesᵉ thatᵉ
[`horizontal-concat-Ω²`](synthetic-homotopy-theory.double-loop-spaces.mdᵉ) isᵉ aᵉ
groupᵉ homomorphismᵉ ofᵉ
[`vertical-concat-Ω²`](synthetic-homotopy-theory.double-loop-spaces.mdᵉ) in eachᵉ
variable.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ}
  where

  outer-eckmann-hilton-interchange-connection-Ω²ᵉ :
    (αᵉ δᵉ : type-Ω²ᵉ aᵉ) →
    horizontal-concat-Ω²ᵉ αᵉ δᵉ ＝ᵉ vertical-concat-Ω²ᵉ αᵉ δᵉ
  outer-eckmann-hilton-interchange-connection-Ω²ᵉ αᵉ δᵉ =
    ( z-concat-Id³ᵉ {αᵉ = αᵉ} {γᵉ = δᵉ} (invᵉ right-unitᵉ) (invᵉ left-unitᵉ)) ∙ᵉ
    ( ( interchange-Ω²ᵉ αᵉ reflᵉ reflᵉ δᵉ) ∙ᵉ
      ( y-concat-Id³ᵉ {βᵉ = αᵉ} {δᵉ = δᵉ}
        ( right-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = αᵉ})
        ( left-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = δᵉ})))

  inner-eckmann-hilton-interchange-connection-Ω²ᵉ :
    (βᵉ γᵉ : type-Ω²ᵉ aᵉ) → horizontal-concat-Ω²ᵉ βᵉ γᵉ ＝ᵉ vertical-concat-Ω²ᵉ γᵉ βᵉ
  inner-eckmann-hilton-interchange-connection-Ω²ᵉ βᵉ γᵉ =
    ( z-concat-Id³ᵉ {αᵉ = βᵉ} {βᵉ} {γᵉ} (invᵉ left-unitᵉ) (invᵉ right-unitᵉ)) ∙ᵉ
    ( ( interchange-Ω²ᵉ reflᵉ βᵉ γᵉ reflᵉ) ∙ᵉ
      ( y-concat-Id³ᵉ {βᵉ = γᵉ} {δᵉ = βᵉ}
        ( left-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = γᵉ})
        ( right-unit-law-horizontal-concat-Ω²ᵉ {αᵉ = βᵉ})))

  eckmann-hilton-interchange-Ω²ᵉ : (αᵉ βᵉ : type-Ω²ᵉ aᵉ) → αᵉ ∙ᵉ βᵉ ＝ᵉ βᵉ ∙ᵉ αᵉ
  eckmann-hilton-interchange-Ω²ᵉ αᵉ βᵉ =
    ( invᵉ (outer-eckmann-hilton-interchange-connection-Ω²ᵉ αᵉ βᵉ)) ∙ᵉ
    ( inner-eckmann-hilton-interchange-connection-Ω²ᵉ αᵉ βᵉ)

  interchange-concat-Ω²ᵉ :
    (αᵉ βᵉ γᵉ δᵉ : type-Ω²ᵉ aᵉ) → (αᵉ ∙ᵉ βᵉ) ∙ᵉ (γᵉ ∙ᵉ δᵉ) ＝ᵉ (αᵉ ∙ᵉ γᵉ) ∙ᵉ (βᵉ ∙ᵉ δᵉ)
  interchange-concat-Ω²ᵉ =
    interchange-law-commutative-and-associativeᵉ
      ( _∙ᵉ_)
      ( eckmann-hilton-interchange-Ω²ᵉ)
      ( assocᵉ)
```

### Constructing the Eckmann-Hilton identification using the naturality condition of the operation of whiskering a fixed 2-path by a 1-path

#### The motivation

Nowᵉ weᵉ giveᵉ theᵉ moreᵉ homotopyᵉ theoreticᵉ versionᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argument.ᵉ
Considerᵉ 2-loopsᵉ `αᵉ βᵉ : Ω²ᵉ X`.ᵉ Theᵉ moreᵉ homotopyᵉ theoreticᵉ Eckmann-Hiltonᵉ
argumentᵉ isᵉ oftenᵉ depictedᵉ asᵉ followsᵉ:

```text
| αᵉ |      | refl-Ω²ᵉ | αᵉ |      | βᵉ | refl-Ω²ᵉ |       | βᵉ |
-----ᵉ  ＝ᵉ  ----------------ᵉ  ＝ᵉ  ----------------ᵉ  ＝ᵉ  ----ᵉ
| βᵉ |      | βᵉ | refl-Ω²ᵉ |      | refl-Ω²ᵉ | αᵉ |       | αᵉ |
```

Theᵉ firstᵉ pictureᵉ representsᵉ theᵉ verticalᵉ concatenationᵉ ofᵉ `α`ᵉ andᵉ `β`.ᵉ Theᵉ
notationᵉ `ᵉ | γᵉ | δᵉ |`ᵉ representsᵉ theᵉ horizontalᵉ concatenationᵉ ofᵉ 2-dimensionalᵉ
identificationsᵉ `γ`ᵉ andᵉ `δ`.ᵉ Thenᵉ `|ᵉ refl-Ω²ᵉ | αᵉ |`ᵉ isᵉ justᵉ
[`left-whisker-concatᵉ refl-Ω²ᵉ α`](foundation-core.whiskering-identifications-concatenation.md).ᵉ
Theᵉ firstᵉ andᵉ lastᵉ equalityᵉ comeᵉ fromᵉ theᵉ unitᵉ lawsᵉ ofᵉ whiskering.ᵉ Andᵉ theᵉ
middleᵉ equalityᵉ canᵉ beᵉ recognizedᵉ asᵉ
[`commutative-left-whisker-right-whisker-concatᵉ αᵉ β`](foundation-core.whiskering-identifications-concatenation.md),ᵉ
whichᵉ isᵉ theᵉ naturalityᵉ conditionᵉ ofᵉ `left-whisker-concatᵉ -ᵉ α`ᵉ appliedᵉ to `β`.ᵉ

Sinceᵉ thisᵉ versionᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argumentᵉ mayᵉ seemᵉ moreᵉ complicatedᵉ thanᵉ
theᵉ algbraicᵉ version,ᵉ theᵉ readerᵉ isᵉ entitledᵉ to wonderᵉ whyᵉ weᵉ botherᵉ givingᵉ thisᵉ
secondᵉ version.ᵉ Thisᵉ versionᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argumentᵉ makesᵉ moreᵉ salientᵉ
theᵉ connectionᵉ betweenᵉ theᵉ Eckmann-Hiltonᵉ identificationᵉ andᵉ theᵉ 2-Dᵉ descentᵉ
data ofᵉ aᵉ typeᵉ family,ᵉ andᵉ playsᵉ anᵉ importantᵉ roleᵉ in theᵉ constructionᵉ ofᵉ theᵉ
Hopfᵉ fibration.ᵉ

Toᵉ seeᵉ this,ᵉ considerᵉ theᵉ familyᵉ ofᵉ basedᵉ identityᵉ typesᵉ `Idᵉ baseᵉ : Xᵉ → UU`.ᵉ Aᵉ
1-loopᵉ `l`ᵉ inducesᵉ anᵉ [automorphism](foundation.automorphisms.mdᵉ)
`trᵉ (Idᵉ baseᵉ) lᵉ : Ωᵉ Xᵉ ≃ᵉ Ωᵉ X`.ᵉ Weᵉ canᵉ computeᵉ thatᵉ

```text
  trᵉ (Idᵉ baseᵉ) lᵉ pᵉ ＝ᵉ pᵉ ∙ᵉ l.ᵉ
```

Thisᵉ isᵉ shownᵉ in
[`tr-Id-right`](foundation-core.transport-along-identifications.md).ᵉ

Upᵉ oneᵉ dimension,ᵉ aᵉ 2-loopᵉ `s`ᵉ inducesᵉ aᵉ homotopyᵉ
`tr²ᵉ (Idᵉ baseᵉ) sᵉ : idᵉ {Aᵉ = Ωᵉ Xᵉ} ~ᵉ id`.ᵉ Weᵉ canᵉ computeᵉ

```text
  tr²ᵉ (Idᵉ baseᵉ) sᵉ pᵉ ∙ᵉ tr-Id-rightᵉ reflᵉ pᵉ ＝ᵉ tr-Id-rightᵉ reflᵉ pᵉ ∙ᵉ left-whisker-concatᵉ pᵉ sᵉ
```

Thisᵉ claimᵉ isᵉ shownᵉ in
[tr²-Id-right](foundation.transport-along-higher-identifications.md).ᵉ Thus,ᵉ theᵉ
2-Dᵉ descentᵉ data ofᵉ `Idᵉ base`ᵉ isᵉ (upᵉ to equivalenceᵉ) theᵉ homotopyᵉ atᵉ theᵉ heartᵉ
ofᵉ thisᵉ versionᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ argument.ᵉ

Recallᵉ thatᵉ homotopiesᵉ ofᵉ typeᵉ `idᵉ ~ᵉ id`ᵉ automaticallyᵉ commuteᵉ with eachᵉ otherᵉ
viaᵉ [`eckmann-hilton-htpy`](foundation.homotopies.md).ᵉ Thisᵉ identificationᵉ isᵉ
constructedᵉ using theᵉ naturalityᵉ conditionᵉ ofᵉ oneᵉ ofᵉ theᵉ twoᵉ homotopiesᵉ
involved.ᵉ Whatᵉ theᵉ aboveᵉ showsᵉ isᵉ thatᵉ theᵉ Eckmann-Hiltonᵉ identificationᵉ ofᵉ
2-loopsᵉ in theᵉ baseᵉ typeᵉ `X`ᵉ isᵉ theᵉ sameᵉ asᵉ theᵉ Eckmann-Hiltonᵉ homotopyᵉ
(evaluatedᵉ atᵉ theᵉ baseᵉ pointᵉ) ofᵉ theᵉ homotopiesᵉ inducedᵉ byᵉ thoseᵉ 2-loopsᵉ in theᵉ
familyᵉ `Idᵉ base`.ᵉ

Ofᵉ courseᵉ `Idᵉ base`ᵉ isᵉ aᵉ specialᵉ typeᵉ family.ᵉ Butᵉ thisᵉ ideaᵉ generalizesᵉ
nonetheless.ᵉ Givenᵉ aᵉ typeᵉ familyᵉ `Bᵉ : Xᵉ → UU`,ᵉ anyᵉ 2-loopsᵉ `αᵉ βᵉ : Ωᵉ X`ᵉ induceᵉ
homotopiesᵉ `tr²ᵉ Bᵉ α`ᵉ andᵉ `tr²ᵉ Bᵉ β`ᵉ ofᵉ typeᵉ `idᵉ {Aᵉ = Bᵉ baseᵉ} ~ᵉ id`.ᵉ Again,ᵉ theseᵉ
homotopiesᵉ automaticallyᵉ commuteᵉ with eachᵉ otherᵉ viaᵉ

```text
  commutative-right-whisker-left-whisker-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ βᵉ)
```

whichᵉ isᵉ theᵉ naturalityᵉ conditionᵉ ofᵉ `tr²ᵉ Bᵉ α`ᵉ appliedᵉ to `tr²ᵉ Bᵉ β`.ᵉ Theᵉ
naturalityᵉ conditionᵉ thatᵉ makesᵉ `α`ᵉ andᵉ `β`ᵉ commuteᵉ in `Ω²ᵉ X`ᵉ isᵉ

```text
  commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ
```

Transportingᵉ alongᵉ thisᵉ latterᵉ identificationᵉ (i.e.,ᵉ applyingᵉ
[`tr³ᵉ B`](foundation.transport-along-higher-identifications.mdᵉ)) resultsᵉ in theᵉ
formerᵉ homotopy.ᵉ Thisᵉ isᵉ shownᵉ in
[`tr³-commutative-left-whisker-right-whisker-concat`](foundation.transport-along-identifications.md).ᵉ
Fromᵉ this,ᵉ itᵉ isᵉ easyᵉ to computeᵉ transportingᵉ alongᵉ anᵉ Eckmann-Hiltonᵉ
identificationᵉ byᵉ provingᵉ thatᵉ theᵉ additionalᵉ coherenceᵉ identificationsᵉ in theᵉ
definitionᵉ ofᵉ `eckmann-hilton-Ω²`ᵉ andᵉ `eckmann-hilton-htpy`ᵉ areᵉ compatible.ᵉ

Thisᵉ connectionᵉ hasᵉ importantᵉ consequences,ᵉ oneᵉ ofᵉ whichᵉ beingᵉ theᵉ connectionᵉ
betweenᵉ theᵉ Eckmann-Hiltonᵉ argumentᵉ andᵉ theᵉ Hopfᵉ fibration.ᵉ

#### The construction, using left whiskering

```agda
module _
  {lᵉ : Level} {Aᵉ : Pointed-Typeᵉ lᵉ}
  where

  eckmann-hilton-Ω²ᵉ :
    (αᵉ βᵉ : type-Ω²ᵉ (point-Pointed-Typeᵉ Aᵉ)) → αᵉ ∙ᵉ βᵉ ＝ᵉ βᵉ ∙ᵉ αᵉ
  eckmann-hilton-Ω²ᵉ αᵉ βᵉ =
    ( invᵉ
      ( horizontal-concat-Id²ᵉ
        ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
        ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))) ∙ᵉ
    ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ) ∙ᵉ
    ( horizontal-concat-Id²ᵉ
      ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
      ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))
```

#### Using right whiskering

Thereᵉ isᵉ anotherᵉ naturalᵉ constructionᵉ ofᵉ anᵉ Eckmann-Hiltonᵉ identificationᵉ alongᵉ
theseᵉ lines.ᵉ Ifᵉ weᵉ thinkᵉ ofᵉ theᵉ firstᵉ constructionᵉ asᵉ "rotatingᵉ clockwise",ᵉ thisᵉ
alternateᵉ versionᵉ "rotatesᵉ counter-clockwise".ᵉ Inᵉ termsᵉ ofᵉ braids,ᵉ theᵉ previousᵉ
constructionᵉ ofᵉ Eckmann-Hiltonᵉ braidsᵉ `α`ᵉ overᵉ `β`,ᵉ whileᵉ thisᵉ nextᵉ constructionᵉ
braidsᵉ `α`ᵉ underᵉ `β`.ᵉ Thisᵉ differenceᵉ showsᵉ upᵉ nicelyᵉ in theᵉ typeᵉ theory.ᵉ Theᵉ
firstᵉ versionᵉ usesᵉ theᵉ naturalityᵉ ofᵉ theᵉ operationᵉ ofᵉ whiskeringᵉ onᵉ theᵉ left,ᵉ
whileᵉ theᵉ secondᵉ versionᵉ usesᵉ theᵉ naturalityᵉ ofᵉ theᵉ operationᵉ ofᵉ whiskeringᵉ onᵉ
theᵉ right.ᵉ Basedᵉ onᵉ theᵉ intutionᵉ ofᵉ braiding,ᵉ weᵉ shouldᵉ expectᵉ theseᵉ twoᵉ versionᵉ
ofᵉ theᵉ Eckmann-Hiltonᵉ identificationᵉ to naturallyᵉ "undo"ᵉ eachᵉ other,ᵉ whichᵉ theyᵉ
do.ᵉ Thus,ᵉ weᵉ willᵉ referᵉ to thisᵉ alternateᵉ constructionᵉ ofᵉ Eckmann-Hiltonᵉ asᵉ "theᵉ
inverseᵉ Eckmann-Hiltonᵉ argument",ᵉ andᵉ theᵉ correspondingᵉ identificationᵉ "theᵉ
inverseᵉ Eckmann-Hiltonᵉ identification".ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : Pointed-Typeᵉ lᵉ}
  where

  inv-eckmann-hilton-Ω²ᵉ :
    (αᵉ βᵉ : type-Ω²ᵉ (point-Pointed-Typeᵉ Aᵉ)) → αᵉ ∙ᵉ βᵉ ＝ᵉ βᵉ ∙ᵉ αᵉ
  inv-eckmann-hilton-Ω²ᵉ αᵉ βᵉ =
    ( invᵉ
      ( horizontal-concat-Id²ᵉ
        ( right-unit-law-right-whisker-Ω²ᵉ αᵉ)
        ( left-unit-law-left-whisker-Ω²ᵉ βᵉ))) ∙ᵉ
    ( commutative-right-whisker-left-whisker-concatᵉ αᵉ βᵉ) ∙ᵉ
    ( horizontal-concat-Id²ᵉ
      ( left-unit-law-left-whisker-Ω²ᵉ βᵉ)
      ( right-unit-law-right-whisker-Ω²ᵉ αᵉ))
```

Weᵉ nowᵉ proveᵉ thatᵉ thisᵉ Eckmann-Hiltonᵉ identificationᵉ "undoes"ᵉ theᵉ previouslyᵉ
constructedᵉ Eckmann-Hiltonᵉ identification.ᵉ Ifᵉ weᵉ thinkᵉ ofᵉ braidingᵉ `α`ᵉ overᵉ `β`,ᵉ
thenᵉ braidingᵉ `β`ᵉ underᵉ `α`,ᵉ weᵉ shouldᵉ endᵉ upᵉ with theᵉ trivialᵉ braid.ᵉ Thus,ᵉ weᵉ
shouldᵉ haveᵉ

`eckmann-hilton-Ω²ᵉ αᵉ βᵉ ∙ᵉ inv-eckmann-hilton-Ω²ᵉ βᵉ αᵉ ＝ᵉ refl`ᵉ

Thisᵉ isᵉ equivalentᵉ to,ᵉ

`invᵉ inv-eckmann-hilton-Ω²ᵉ βᵉ αᵉ ＝ᵉ eckmann-hilton-Ω²ᵉ αᵉ β`ᵉ

whichᵉ isᵉ whatᵉ weᵉ prove.ᵉ

**Note.**ᵉ thatᵉ theᵉ aboveᵉ propertyᵉ isᵉ distinctᵉ fromᵉ syllepsis,ᵉ sinceᵉ itᵉ concernsᵉ
twoᵉ differentᵉ constructionᵉ ofᵉ theᵉ Eckmann-Hiltonᵉ identification.ᵉ Further,ᵉ itᵉ
appliesᵉ to allᵉ 2-loops,ᵉ notᵉ solelyᵉ 3-loops.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : Pointed-Typeᵉ lᵉ}
  where

  compute-inv-inv-eckmann-hilton-Ω²ᵉ :
    (αᵉ βᵉ : type-Ω²ᵉ (point-Pointed-Typeᵉ Aᵉ)) →
    invᵉ (inv-eckmann-hilton-Ω²ᵉ βᵉ αᵉ) ＝ᵉ eckmann-hilton-Ω²ᵉ αᵉ βᵉ
  compute-inv-inv-eckmann-hilton-Ω²ᵉ αᵉ βᵉ =
    ( distributive-inv-concatᵉ
      ( ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))) ∙ᵉ
        ( commutative-right-whisker-left-whisker-concatᵉ βᵉ αᵉ))
      ( horizontal-concat-Id²ᵉ
        ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
        ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))) ∙ᵉ
    ( left-whisker-concatᵉ
      ( invᵉ
        ( horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
      ( distributive-inv-concatᵉ
        ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
        ( commutative-right-whisker-left-whisker-concatᵉ βᵉ αᵉ))) ∙ᵉ
    ( left-whisker-concatᵉ
      ( invᵉ
        ( horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
      ( horizontal-concat-Id²ᵉ
        ( compute-inv-commutative-right-whisker-left-whisker-concatᵉ αᵉ βᵉ)
        ( inv-invᵉ
          ( horizontal-concat-Id²ᵉ
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))))) ∙ᵉ
    ( invᵉ
      ( assocᵉ
        ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
        ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ)
        ( horizontal-concat-Id²ᵉ
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))))
```

## Properties

### Obtaining a 3-loop from a 2-loop using `eckmann-hilton-Ω²`

Givenᵉ aᵉ 2-loopᵉ `sᵉ : Ω²ᵉ A`,ᵉ weᵉ canᵉ obtainᵉ anᵉ identificationᵉ
`eckmann-hilton-Ω²ᵉ sᵉ sᵉ : sᵉ ∙ᵉ sᵉ ＝ᵉ sᵉ ∙ᵉ s`.ᵉ Theᵉ typeᵉ ofᵉ thisᵉ identificationᵉ isᵉ
equivalentᵉ to theᵉ typeᵉ ofᵉ 3-loops,ᵉ viaᵉ theᵉ equivalenceᵉ
[`pointed-equiv-2-loop-pointed-identityᵉ (Ωᵉ (Aᵉ ,ᵉ aᵉ)) (sᵉ ∙ᵉ s)`](synthetic-homotopy-theory.double-loop-spaces.md).ᵉ

3-loopsᵉ obtainedᵉ in thisᵉ wayᵉ areᵉ atᵉ theᵉ heartᵉ ofᵉ theᵉ Hopfᵉ fibration.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (sᵉ : type-Ω²ᵉ aᵉ)
  where

  3-loop-eckmann-hilton-Ω²ᵉ : type-Ω³ᵉ aᵉ
  3-loop-eckmann-hilton-Ω²ᵉ =
    map-pointed-equivᵉ
      ( pointed-equiv-2-loop-pointed-identityᵉ (Ωᵉ (Aᵉ ,ᵉ aᵉ)) (sᵉ ∙ᵉ sᵉ))
      ( eckmann-hilton-Ω²ᵉ sᵉ sᵉ)

  inv-3-loop-eckmann-hilton-Ω²ᵉ : type-Ω³ᵉ aᵉ
  inv-3-loop-eckmann-hilton-Ω²ᵉ =
    map-pointed-equivᵉ
      ( pointed-equiv-2-loop-pointed-identityᵉ (Ωᵉ (Aᵉ ,ᵉ aᵉ)) (sᵉ ∙ᵉ sᵉ))
      ( inv-eckmann-hilton-Ω²ᵉ sᵉ sᵉ)
```

### The above two 3-loops are inverses

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ : Aᵉ} (sᵉ : type-Ω²ᵉ aᵉ)
  where

  compute-inv-inv-3-loop-eckmann-hilton-Ω²ᵉ :
    invᵉ (inv-3-loop-eckmann-hilton-Ω²ᵉ sᵉ) ＝ᵉ 3-loop-eckmann-hilton-Ω²ᵉ sᵉ
  compute-inv-inv-3-loop-eckmann-hilton-Ω²ᵉ =
    ( invᵉ
      ( preserves-inv-map-Ωᵉ
        ( pointed-map-pointed-equivᵉ
          ( pointed-equiv-loop-pointed-identityᵉ (Ωᵉ (Aᵉ ,ᵉ aᵉ)) (sᵉ ∙ᵉ sᵉ)))
        (inv-eckmann-hilton-Ω²ᵉ sᵉ sᵉ))) ∙ᵉ
    ( apᵉ
      ( map-Ωᵉ
        ( pointed-map-pointed-equivᵉ
          ( pointed-equiv-loop-pointed-identityᵉ (Ωᵉ (Aᵉ ,ᵉ aᵉ)) (sᵉ ∙ᵉ sᵉ))))
      ( compute-inv-inv-eckmann-hilton-Ω²ᵉ sᵉ sᵉ))
```

### Computing transport along `eckmann-hilton-Ω²`

Thisᵉ coherenceᵉ relatesᵉ theᵉ threeᵉ dimensionalᵉ transportᵉ
[`tr³`](foundation.transport-along-higher-identifications.mdᵉ) alongᵉ anᵉ
Eckmann-Hiltonᵉ identificationᵉ
[`eckmann-hilton-Ω²ᵉ αᵉ β`](synthetic-homotopy-theory.eckmann-hilton-argument.mdᵉ)
to theᵉ Eckmann-Hiltonᵉ argumentᵉ forᵉ homotopiesᵉ
[`eckmann-hilton-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ β)`](foundation.homotopy-algebra.md).ᵉ

Thisᵉ takesᵉ theᵉ formᵉ ofᵉ aᵉ commutativeᵉ squareᵉ ofᵉ homotopiesᵉ

```text
                   tr²-concatᵉ αᵉ βᵉ
  tr²ᵉ Bᵉ (αᵉ ∙ᵉ βᵉ) ------------------->ᵉ tr²ᵉ Bᵉ αᵉ ∙hᵉ tr²ᵉ Bᵉ βᵉ
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       |                                    |
       ∨ᵉ                                    ∨ᵉ
  tr²ᵉ Bᵉ (βᵉ ∙ᵉ αᵉ) ------------------->ᵉ tr²ᵉ Bᵉ βᵉ ∙hᵉ tr²ᵉ Bᵉ α,ᵉ
                   tr²-concatᵉ βᵉ αᵉ
```

where theᵉ leftᵉ legᵉ isᵉ `tr³ᵉ Bᵉ (eckmann-hilton-Ω²ᵉ αᵉ β)`ᵉ andᵉ theᵉ rightᵉ legᵉ isᵉ
`eckmann-hilton-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ β)`.ᵉ

Weᵉ constructᵉ aᵉ fillerᵉ forᵉ thisᵉ squareᵉ byᵉ firstᵉ distributingᵉ `tr³`ᵉ acrossᵉ theᵉ
concatenatedᵉ pathsᵉ usedᵉ in `eckmann-hilton-Ω²`,ᵉ thenᵉ splittingᵉ theᵉ resultantᵉ
squareᵉ intoᵉ threeᵉ verticalᵉ squares,ᵉ constructingᵉ fillersᵉ forᵉ each,ᵉ thenᵉ pastingᵉ
themᵉ together.ᵉ Theᵉ fillerᵉ ofᵉ theᵉ middleᵉ squareᵉ isᵉ

```text
  tr³-commutative-left-whisker-right-whisker-concat-Ω²ᵉ αᵉ βᵉ
```

Theᵉ fillersᵉ forᵉ theᵉ topᵉ andᵉ bottomᵉ squaresᵉ areᵉ constructedᵉ below.ᵉ Theyᵉ relateᵉ
theᵉ unitᵉ lawsᵉ forᵉ whiskeringᵉ identificationsᵉ usedᵉ in `eckmann-hilton-Ω²`ᵉ andᵉ theᵉ
unitᵉ lawsᵉ forᵉ whiskeringᵉ homotopiesᵉ usedᵉ in `eckmann-hilton-htpy`.ᵉ

#### Distributing `tr³` across `eckmann-hilton-Ω²`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {aᵉ : Aᵉ}
  {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (αᵉ βᵉ : type-Ω²ᵉ aᵉ)
  where

  tr³-eckmann-hilton-distributedᵉ :
    tr²ᵉ Bᵉ (αᵉ ∙ᵉ βᵉ) ~ᵉ tr²ᵉ Bᵉ (βᵉ ∙ᵉ αᵉ)
  tr³-eckmann-hilton-distributedᵉ =
    ( tr³ᵉ
      ( Bᵉ)
      ( invᵉ
        ( horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))) ∙hᵉ
    ( tr³ᵉ
      ( Bᵉ)
      ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ)) ∙hᵉ
    ( tr³ᵉ
      ( Bᵉ)
      ( horizontal-concat-Id²ᵉ
        ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
        ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))

  tr³-concat-eckmann-hiltonᵉ :
    ( tr³ᵉ Bᵉ (eckmann-hilton-Ω²ᵉ αᵉ βᵉ)) ~ᵉ
    ( tr³-eckmann-hilton-distributedᵉ)
  tr³-concat-eckmann-hiltonᵉ =
    ( tr³-concatᵉ
      ( ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))) ∙ᵉ
        ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
      ( horizontal-concat-Id²ᵉ
        ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
        ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))) ∙hᵉ
    ( right-whisker-concat-htpyᵉ
      ( tr³-concatᵉ
        ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
        ( commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
      ( tr³ᵉ
        ( Bᵉ)
        ( horizontal-concat-Id²ᵉ
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))))
```

#### The filler of the top square

```agda
  tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ :
    coherence-square-homotopiesᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
      ( left-whisker-concat-htpyᵉ
        ( tr²ᵉ Bᵉ αᵉ)
        ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
      ( tr²-concatᵉ αᵉ βᵉ)
  tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ =
    concat-bottom-homotopy-coherence-square-homotopiesᵉ
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
      ( left-whisker-concat-htpyᵉ
        ( tr²ᵉ Bᵉ αᵉ)
        ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
      ( tr²-concatᵉ αᵉ βᵉ ∙hᵉ refl-htpyᵉ)
      ( right-unit-htpyᵉ)
      ( horizontal-pasting-coherence-square-homotopiesᵉ
        ( tr²-concatᵉ
          ( left-whisker-concatᵉ reflᵉ αᵉ)
          ( right-whisker-concatᵉ βᵉ reflᵉ))
        ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
        ( tr³ᵉ
          ( Bᵉ)
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
        ( horizontal-concat-htpy²ᵉ
          ( tr³ᵉ
            ( Bᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))
          ( tr³ᵉ
            ( Bᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
        ( left-whisker-concat-htpyᵉ
          ( tr²ᵉ Bᵉ αᵉ)
          ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
        ( tr²-concatᵉ αᵉ βᵉ)
        ( refl-htpyᵉ)
        ( tr³-horizontal-concatᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))
        ( inv-concat-right-homotopy-coherence-square-homotopiesᵉ
          ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
          ( horizontal-concat-htpy²ᵉ
            ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-Ω²ᵉ αᵉ))
            ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
          ( left-whisker-concat-htpyᵉ
            ( tr²ᵉ Bᵉ αᵉ)
            ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
          ( refl-htpyᵉ)
          ( inv-htpyᵉ
            ( compute-left-refl-htpy-horizontal-concat-htpy²ᵉ
              ( tr²ᵉ Bᵉ αᵉ)
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
          ( ( right-unit-htpyᵉ) ∙hᵉ
            ( z-concat-htpy³ᵉ
              ( inv-htpyᵉ right-unit-htpyᵉ)
              ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
                ( left-whisker-concat-htpyᵉ
                  ( tr³ᵉ
                    ( Bᵉ)
                    ( invᵉ
                      ( right-unit-law-right-whisker-concatᵉ βᵉ ∙ᵉ right-unitᵉ)))
                  ( inv-htpyᵉ
                    ( left-inv-htpyᵉ
                      ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))) ∙hᵉ
                ( inv-htpyᵉ
                  ( assoc-htpyᵉ
                    ( tr³ᵉ
                      ( Bᵉ)
                      ( invᵉ
                        ( ( right-unit-law-right-whisker-concatᵉ βᵉ) ∙ᵉ
                          ( right-unitᵉ))))
                    ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
                    ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))))) ∙hᵉ
            ( interchange-htpy²ᵉ
              ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ αᵉ))
              ( refl-htpyᵉ)
              ( ( tr³ᵉ
                  ( Bᵉ)
                  ( invᵉ
                    ( ( right-unit-law-right-whisker-concatᵉ βᵉ) ∙ᵉ
                      ( right-unitᵉ)))) ∙hᵉ
                ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))))

  tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ :
    coherence-square-homotopiesᵉ
      ( tr²-concatᵉ αᵉ βᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))))
      ( inv-htpyᵉ
        ( left-whisker-concat-htpyᵉ
          ( tr²ᵉ Bᵉ αᵉ)
          ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
  tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ =
    inv-concat-left-homotopy-coherence-square-homotopiesᵉ
      ( tr²-concatᵉ αᵉ βᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( invᵉ
          ( horizontal-concat-Id²ᵉ
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))))
      ( inv-htpyᵉ
        ( left-whisker-concat-htpyᵉ
          ( tr²ᵉ Bᵉ αᵉ)
          ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
      ( tr⁴ᵉ
        ( Bᵉ)
        ( distributive-inv-horizontal-concat-Id²ᵉ
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
      ( concat-left-homotopy-coherence-square-homotopiesᵉ
        ( tr²-concatᵉ αᵉ βᵉ)
        ( inv-htpyᵉ
          ( tr³ᵉ
            ( Bᵉ)
            ( horizontal-concat-Id²ᵉ
              ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
              ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))))
        ( inv-htpyᵉ
          ( left-whisker-concat-htpyᵉ
            ( tr²ᵉ Bᵉ αᵉ)
            ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
        ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
        ( ( inv-htpyᵉ
            ( tr³-invᵉ
              ( horizontal-concat-Id²ᵉ
                ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
                ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))) ∙hᵉ
          ( tr⁴ᵉ
            ( Bᵉ)
            ( distributive-inv-horizontal-concat-Id²ᵉ
              ( left-unit-law-left-whisker-concatᵉ αᵉ)
              ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))))
        ( vertical-inv-coherence-square-homotopiesᵉ
          ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
          ( tr³ᵉ
            ( Bᵉ)
            ( horizontal-concat-Id²ᵉ
              ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
              ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)))
          ( left-whisker-concat-htpyᵉ
            ( tr²ᵉ Bᵉ αᵉ)
            ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
          ( tr²-concatᵉ αᵉ βᵉ)
          ( tr³-horizontal-concat-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ)))
```

#### The filler of the bottom square

```agda
  tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω²ᵉ :
    coherence-square-homotopiesᵉ
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( horizontal-concat-Id²ᵉ
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
      ( right-whisker-concat-htpyᵉ
        ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
        ( tr²ᵉ Bᵉ αᵉ))
      ( tr²-concatᵉ βᵉ αᵉ)
  tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω²ᵉ =
    concat-bottom-homotopy-coherence-square-homotopiesᵉ
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
      ( tr³ᵉ
        ( Bᵉ)
        ( horizontal-concat-Id²ᵉ
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
      ( right-whisker-concat-htpyᵉ
        ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
        ( tr²ᵉ Bᵉ αᵉ))
      ( tr²-concatᵉ βᵉ αᵉ ∙hᵉ refl-htpyᵉ)
      ( right-unit-htpyᵉ)
      ( horizontal-pasting-coherence-square-homotopiesᵉ
        ( tr²-concatᵉ
          ( right-whisker-concatᵉ βᵉ reflᵉ)
          ( left-whisker-concatᵉ reflᵉ αᵉ))
        ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
        ( tr³ᵉ
          ( Bᵉ)
          ( horizontal-concat-Id²ᵉ
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
        ( horizontal-concat-htpy²ᵉ
          ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ))
          ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
        ( right-whisker-concat-htpyᵉ
          ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
          ( tr²ᵉ Bᵉ αᵉ))
        ( tr²-concatᵉ βᵉ αᵉ)
        ( refl-htpyᵉ)
        ( tr³-horizontal-concatᵉ
          ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
          ( left-unit-law-left-whisker-Ω²ᵉ αᵉ))
        ( inv-concat-right-homotopy-coherence-square-homotopiesᵉ
          ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
          ( horizontal-concat-htpy²ᵉ
            ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ))
            ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
          ( right-whisker-concat-htpyᵉ
            ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
            ( tr²ᵉ Bᵉ αᵉ))
          ( refl-htpyᵉ)
          ( inv-htpyᵉ
            ( compute-right-refl-htpy-horizontal-concat-htpy²ᵉ
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
              ( tr²ᵉ Bᵉ αᵉ)))
          ( ( right-unit-htpyᵉ
              { Hᵉ =
                ( horizontal-concat-htpy²ᵉ
                  ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ))
                  ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-Ω²ᵉ αᵉ)))}) ∙hᵉ
            ( z-concat-htpy³ᵉ
              ( ( inv-htpyᵉ right-unit-htpyᵉ) ∙hᵉ
                ( left-whisker-concat-htpyᵉ
                  ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ))
                  ( inv-htpyᵉ
                    ( left-inv-htpyᵉ
                      ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))) ∙hᵉ
                ( inv-htpyᵉ
                  ( assoc-htpyᵉ
                    ( tr³ᵉ Bᵉ (right-unit-law-right-whisker-Ω²ᵉ βᵉ))
                    ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))
                    ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))))
              ( inv-htpyᵉ right-unit-htpyᵉ)) ∙hᵉ
            ( interchange-htpy²ᵉ
              ( ( tr³ᵉ
                  ( Bᵉ)
                  ( invᵉ
                    ( ( right-unit-law-right-whisker-concatᵉ βᵉ) ∙ᵉ
                      ( right-unitᵉ)))) ∙hᵉ
                ( inv-htpyᵉ (left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))
              ( tr³ᵉ Bᵉ (left-unit-law-left-whisker-concatᵉ αᵉ))
              ( refl-htpyᵉ)))))
```

#### The computation

```agda
  tr³-eckmann-hiltonᵉ :
    coherence-square-homotopiesᵉ
      ( tr²-concatᵉ αᵉ βᵉ)
      ( tr³ᵉ Bᵉ (eckmann-hilton-Ω²ᵉ αᵉ βᵉ))
      ( eckmann-hilton-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ βᵉ))
      ( tr²-concatᵉ βᵉ αᵉ)
  tr³-eckmann-hiltonᵉ =
    inv-concat-left-homotopy-coherence-square-homotopiesᵉ
      ( tr²-concatᵉ αᵉ βᵉ)
      ( tr³ᵉ Bᵉ (eckmann-hilton-Ω²ᵉ αᵉ βᵉ))
      ( eckmann-hilton-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ βᵉ))
      ( tr²-concatᵉ βᵉ αᵉ)
      ( tr³-concat-eckmann-hiltonᵉ)
      ( vertical-pasting-coherence-square-homotopiesᵉ
        ( tr²-concatᵉ αᵉ βᵉ)
        ( tr³ᵉ Bᵉ
          ( invᵉ
            ( horizontal-concat-Id²ᵉ
              ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
              ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))) ∙hᵉ
        ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ)))
        ( ( inv-htpyᵉ
            ( left-whisker-concat-htpyᵉ
              ( tr²ᵉ Bᵉ αᵉ)
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)))) ∙hᵉ
          ( commutative-right-whisker-left-whisker-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ βᵉ)))
        ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
        ( tr³ᵉ Bᵉ
          ( horizontal-concat-Id²ᵉ
            ( right-unit-law-right-whisker-Ω²ᵉ βᵉ)
            ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)))
        ( right-whisker-concat-htpyᵉ
          ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ)) (tr²ᵉ Bᵉ αᵉ))
        ( tr²-concatᵉ βᵉ αᵉ)
        ( vertical-pasting-coherence-square-homotopiesᵉ
          ( tr²-concatᵉ αᵉ βᵉ)
          ( tr³ᵉ
            ( Bᵉ)
            ( invᵉ
              ( horizontal-concat-Id²ᵉ
                ( left-unit-law-left-whisker-Ω²ᵉ αᵉ)
                ( right-unit-law-right-whisker-Ω²ᵉ βᵉ))))
          ( inv-htpyᵉ
            ( left-whisker-concat-htpyᵉ
              ( tr²ᵉ Bᵉ αᵉ)
              ( left-unit-law-left-whisker-compᵉ (tr²ᵉ Bᵉ βᵉ))))
          ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω²ᵉ αᵉ βᵉ)
          ( tr³ᵉ Bᵉ (commutative-left-whisker-right-whisker-concatᵉ αᵉ βᵉ))
          ( commutative-right-whisker-left-whisker-htpyᵉ (tr²ᵉ Bᵉ αᵉ) (tr²ᵉ Bᵉ βᵉ))
          ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω²ᵉ βᵉ αᵉ)
          ( tr³-horizontal-concat-inv-left-unit-law-left-whisker-right-unit-law-right-whisker-Ω²ᵉ)
          ( tr³-commutative-left-whisker-right-whisker-concat-Ω²ᵉ αᵉ βᵉ))
        ( tr³-horizontal-concat-right-unit-law-right-whisker-left-unit-law-left-whisker-Ω²ᵉ))
```

## External links

-ᵉ [Theᵉ Eckmann-Hiltonᵉ argument](https://1lab.dev/Algebra.Magma.Unital.EckmannHilton.htmlᵉ)
  atᵉ 1lab.ᵉ
-ᵉ [Eckmann-Hiltonᵉ argument](https://ncatlab.org/nlab/show/Eckmann-Hilton+argumentᵉ)
  atᵉ $n$Lab.ᵉ
-ᵉ [Eckmann-Hiltonᵉ argument](https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argumentᵉ)
  atᵉ Wikipedia.ᵉ
-ᵉ [Eckmann-Hiltonᵉ andᵉ theᵉ Hopfᵉ Fibration](https://www.youtube.com/watch?v=hU4_dVpmkKMᵉ)