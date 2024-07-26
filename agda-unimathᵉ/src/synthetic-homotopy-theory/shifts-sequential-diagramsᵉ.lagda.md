# Shifts of sequential diagrams

```agda
module synthetic-homotopy-theory.shifts-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-concatenationᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.functoriality-sequential-colimitsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "shift"ᵉ Disambiguation="sequentialᵉ diagram"ᵉ Agda=shift-sequential-diagramᵉ}}
ofᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) isᵉ aᵉ
sequentialᵉ diagramᵉ consistingᵉ ofᵉ theᵉ typesᵉ andᵉ mapsᵉ shiftedᵉ byᵉ one.ᵉ Itᵉ isᵉ alsoᵉ
denotedᵉ `A[1]`.ᵉ Thisᵉ shiftingᵉ canᵉ beᵉ iteratedᵉ forᵉ anyᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `k`;ᵉ thenᵉ theᵉ
resultingᵉ sequentialᵉ diagramᵉ isᵉ denotedᵉ `A[k]`.ᵉ

Similarly,ᵉ aᵉ
{{#conceptᵉ "shift"ᵉ Disambiguation="morphismᵉ ofᵉ sequentialᵉ diagrams"ᵉ Agda=shift-hom-sequential-diagramᵉ}}
ofᵉ aᵉ
[morphismᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ)
isᵉ aᵉ morphismᵉ fromᵉ theᵉ shiftedᵉ domainᵉ intoᵉ theᵉ shiftedᵉ codomain.ᵉ Inᵉ symbols,ᵉ
givenᵉ aᵉ morphismᵉ `fᵉ : Aᵉ → B`,ᵉ weᵉ haveᵉ `f[kᵉ] : A[kᵉ] → B[k]`.ᵉ

Weᵉ alsoᵉ defineᵉ shiftsᵉ ofᵉ
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ) andᵉ
[homotopiesᵉ ofᵉ cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md),ᵉ
whichᵉ canᵉ additionallyᵉ beᵉ unshifted.ᵉ

Importantlyᵉ theᵉ typeᵉ ofᵉ coconesᵉ underᵉ aᵉ sequentialᵉ diagramᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ coconesᵉ underᵉ itsᵉ
shift,ᵉ whichᵉ impliesᵉ thatᵉ theᵉ
[sequentialᵉ colimit](synthetic-homotopy-theory.sequential-colimits.mdᵉ) ofᵉ aᵉ
shiftedᵉ sequentialᵉ diagramᵉ isᵉ equivalentᵉ to theᵉ colimitᵉ ofᵉ theᵉ originalᵉ diagram.ᵉ

## Definitions

_Implementationᵉ noteᵉ_: theᵉ constructionsᵉ areᵉ definedᵉ byᵉ firstᵉ definingᵉ aᵉ shiftᵉ
byᵉ one,ᵉ andᵉ thenᵉ recursivelyᵉ shiftingᵉ byᵉ oneᵉ accordingᵉ to theᵉ argument.ᵉ Anᵉ
alternativeᵉ wouldᵉ beᵉ to shiftᵉ allᵉ data using
[addition](elementary-number-theory.addition-natural-numbers.mdᵉ) onᵉ theᵉ naturalᵉ
numbers.ᵉ

However,ᵉ additionᵉ computesᵉ onlyᵉ onᵉ oneᵉ side,ᵉ soᵉ weᵉ haveᵉ aᵉ choiceᵉ to makeᵉ: givenᵉ
aᵉ shiftᵉ `k`,ᵉ do weᵉ defineᵉ theᵉ `n`-thᵉ levelᵉ ofᵉ theᵉ shiftedᵉ structureᵉ to beᵉ theᵉ
`n+k`-thᵉ orᵉ `k+n`-thᵉ levelᵉ ofᵉ theᵉ original?ᵉ

Theᵉ formerᵉ runsᵉ intoᵉ issuesᵉ alreadyᵉ whenᵉ definingᵉ theᵉ shiftedᵉ sequence,ᵉ sinceᵉ
`aₙ₊ₖᵉ : Aₙ₊ₖᵉ → A₍ₙ₊₁₎₊ₖ`,ᵉ butᵉ weᵉ needᵉ aᵉ mapᵉ ofᵉ typeᵉ `Aₙ₊ₖᵉ → A₍ₙ₊ₖ₎₊₁`,ᵉ whichᵉ
forcesᵉ usᵉ to introduceᵉ aᵉ
[transport](foundation-core.transport-along-identifications.md).ᵉ

Onᵉ theᵉ otherᵉ hand,ᵉ theᵉ latterᵉ requiresᵉ transportᵉ whenᵉ provingᵉ anythingᵉ byᵉ
inductionᵉ onᵉ `k`ᵉ andᵉ doesn'tᵉ satisfyᵉ theᵉ judgmentalᵉ equalityᵉ `A[0ᵉ] ≐ᵉ A`,ᵉ becauseᵉ
`A₍ₖ₊₁₎₊ₙ`ᵉ isᵉ notᵉ `A₍ₖ₊ₙ₎₊₁`ᵉ andᵉ `A₀₊ₙ`ᵉ isᵉ notᵉ `Aₙ`,ᵉ andᵉ itᵉ requiresᵉ moreᵉ
infrastructureᵉ forᵉ workingᵉ with horizontalᵉ compositionsᵉ in sequentialᵉ colimitᵉ to
beᵉ formalizedᵉ in termsᵉ ofᵉ addition.ᵉ

Toᵉ contrast,ᵉ definingᵉ theᵉ operationsᵉ byᵉ inductionᵉ doesᵉ satisfyᵉ `A[0ᵉ] ≐ᵉ A`,ᵉ itᵉ
computesᵉ whenᵉ provingᵉ propertiesᵉ byᵉ induction,ᵉ whichᵉ isᵉ theᵉ expectedᵉ primaryᵉ
use-case,ᵉ andᵉ noᵉ furtherᵉ infrastructureᵉ isᵉ necessary.ᵉ

### Shifts of sequential diagrams

Givenᵉ aᵉ sequentialᵉ diagramᵉ `A`ᵉ

```text
     a₀ᵉ      a₁ᵉ      a₂ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ ,ᵉ
```

weᵉ canᵉ forgetᵉ theᵉ firstᵉ typeᵉ andᵉ mapᵉ to getᵉ theᵉ diagramᵉ

```text
     a₁ᵉ      a₂ᵉ
 A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ ,ᵉ
```

whichᵉ weᵉ callᵉ `A[1]`.ᵉ Inductively,ᵉ weᵉ defineᵉ `A[kᵉ +ᵉ 1ᵉ] ≐ᵉ A[k][1]`.ᵉ

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  shift-once-sequential-diagramᵉ : sequential-diagramᵉ l1ᵉ
  pr1ᵉ shift-once-sequential-diagramᵉ nᵉ = family-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)
  pr2ᵉ shift-once-sequential-diagramᵉ nᵉ = map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)

module _
  {l1ᵉ : Level}
  where

  shift-sequential-diagramᵉ : ℕᵉ → sequential-diagramᵉ l1ᵉ → sequential-diagramᵉ l1ᵉ
  shift-sequential-diagramᵉ zero-ℕᵉ Aᵉ = Aᵉ
  shift-sequential-diagramᵉ (succ-ℕᵉ kᵉ) Aᵉ =
    shift-once-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ)
```

### Shifts of morphisms of sequential diagrams

Givenᵉ aᵉ morphismᵉ ofᵉ sequentialᵉ diagramsᵉ `fᵉ : Aᵉ → B`ᵉ

```text
        a₀ᵉ      a₁ᵉ
    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
    |       |       |
 f₀ᵉ |       | f₁ᵉ    | f₂ᵉ
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ ,ᵉ
        b₀ᵉ      b₁ᵉ
```

weᵉ canᵉ dropᵉ theᵉ firstᵉ squareᵉ to getᵉ theᵉ morphismᵉ

```text
        a₁ᵉ
    A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
    |       |
 f₁ᵉ |       | f₂ᵉ
    ∨ᵉ       ∨ᵉ
    B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ ,ᵉ
        b₁ᵉ
```

whichᵉ weᵉ callᵉ `f[1ᵉ] : A[1ᵉ] → B[1]`.ᵉ Inductively,ᵉ weᵉ defineᵉ `f[kᵉ +ᵉ 1ᵉ] ≐ᵉ f[k][1]`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  (fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  shift-once-hom-sequential-diagramᵉ :
    hom-sequential-diagramᵉ
      ( shift-once-sequential-diagramᵉ Aᵉ)
      ( shift-once-sequential-diagramᵉ Bᵉ)
  pr1ᵉ shift-once-hom-sequential-diagramᵉ nᵉ =
    map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ)
  pr2ᵉ shift-once-hom-sequential-diagramᵉ nᵉ =
    naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  shift-hom-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    hom-sequential-diagramᵉ Aᵉ Bᵉ →
    hom-sequential-diagramᵉ
      ( shift-sequential-diagramᵉ kᵉ Aᵉ)
      ( shift-sequential-diagramᵉ kᵉ Bᵉ)
  shift-hom-sequential-diagramᵉ zero-ℕᵉ fᵉ = fᵉ
  shift-hom-sequential-diagramᵉ (succ-ℕᵉ kᵉ) fᵉ =
    shift-once-hom-sequential-diagramᵉ
      ( shift-sequential-diagramᵉ kᵉ Bᵉ)
      ( shift-hom-sequential-diagramᵉ kᵉ fᵉ)
```

### Shifts of cocones under sequential diagrams

Givenᵉ aᵉ coconeᵉ `c`ᵉ

```text
      a₀ᵉ      a₁ᵉ
  A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
   \ᵉ      |      /ᵉ
    \ᵉ     |     /ᵉ
  i₀ᵉ \ᵉ    | i₁ᵉ /ᵉ i₂ᵉ
      \ᵉ   |   /ᵉ
       ∨ᵉ  ∨ᵉ  ∨ᵉ
          Xᵉ
```

underᵉ `A`,ᵉ weᵉ mayᵉ forgetᵉ theᵉ firstᵉ inclusionᵉ andᵉ homotopyᵉ to getᵉ theᵉ coconeᵉ

```text
         a₁ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |      /ᵉ
     |     /ᵉ
  i₁ᵉ |    /ᵉ i₂ᵉ
     |   /ᵉ
     ∨ᵉ  ∨ᵉ
     Xᵉ
```

underᵉ `A[1]`.ᵉ Weᵉ denoteᵉ thisᵉ coconeᵉ `c[1]`.ᵉ Inductively,ᵉ weᵉ defineᵉ
`c[kᵉ +ᵉ 1ᵉ] ≐ᵉ c[k][1]`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  shift-once-cocone-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) Xᵉ
  pr1ᵉ shift-once-cocone-sequential-diagramᵉ nᵉ =
    map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ)
  pr2ᵉ shift-once-cocone-sequential-diagramᵉ nᵉ =
    coherence-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  shift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    cocone-sequential-diagramᵉ Aᵉ Xᵉ →
    cocone-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) Xᵉ
  shift-cocone-sequential-diagramᵉ zero-ℕᵉ cᵉ =
    cᵉ
  shift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) cᵉ =
    shift-once-cocone-sequential-diagramᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ)
```

### Unshifts of cocones under sequential diagrams

Conversely,ᵉ givenᵉ aᵉ coconeᵉ `c`ᵉ

```text
         a₁ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |      /ᵉ
     |     /ᵉ
  i₁ᵉ |    /ᵉ i₂ᵉ
     |   /ᵉ
     ∨ᵉ  ∨ᵉ
     Xᵉ
```

underᵉ `A[1]`,ᵉ weᵉ mayᵉ prependᵉ aᵉ mapᵉ

```text
           a₀ᵉ      a₁ᵉ
       A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
        \ᵉ      |      /ᵉ
         \ᵉ     |     /ᵉ
  i₁ᵉ ∘ᵉ a₀ᵉ \ᵉ    | i₁ᵉ /ᵉ i₂ᵉ
           \ᵉ   |   /ᵉ
            ∨ᵉ  ∨ᵉ  ∨ᵉ
               Xᵉ
```

whichᵉ commutesᵉ byᵉ reflexivity,ᵉ givingᵉ usᵉ aᵉ coconeᵉ underᵉ `A`,ᵉ whichᵉ weᵉ callᵉ
`c[-1]`.ᵉ

Noticeᵉ thatᵉ byᵉ restrictingᵉ theᵉ typeᵉ ofᵉ `c`ᵉ to beᵉ theᵉ coconesᵉ underᵉ anᵉ alreadyᵉ
shiftedᵉ diagram,ᵉ weᵉ ensureᵉ thatᵉ unshiftingᵉ cannotᵉ getᵉ outᵉ ofᵉ boundsᵉ ofᵉ theᵉ
originalᵉ diagram.ᵉ

Inductively,ᵉ weᵉ defineᵉ `c[-(kᵉ +ᵉ 1ᵉ)] ≐ᵉ c[-1][-k]`.ᵉ Oneᵉ mightᵉ expectᵉ thatᵉ
followingᵉ theᵉ pattern ofᵉ shifts,ᵉ thisᵉ shouldᵉ beᵉ `c[-k][-1]`,ᵉ butᵉ recallᵉ thatᵉ weᵉ
onlyᵉ knowᵉ howᵉ to unshiftᵉ aᵉ coconeᵉ underᵉ `A[n]`ᵉ byᵉ `n`;ᵉ sinceᵉ thisᵉ `c`ᵉ isᵉ underᵉ
`A[k][1]`,ᵉ weᵉ firstᵉ needᵉ to unshiftᵉ byᵉ 1 to getᵉ `c[-1]`ᵉ underᵉ `A[k]`,ᵉ andᵉ onlyᵉ
thenᵉ weᵉ canᵉ unshiftᵉ byᵉ `k`ᵉ to getᵉ `c[-1][-k]`ᵉ underᵉ `A`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) Xᵉ)
  where

  unshift-once-cocone-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ Aᵉ Xᵉ
  pr1ᵉ unshift-once-cocone-sequential-diagramᵉ zero-ℕᵉ =
    map-cocone-sequential-diagramᵉ cᵉ zero-ℕᵉ ∘ᵉ map-sequential-diagramᵉ Aᵉ zero-ℕᵉ
  pr1ᵉ unshift-once-cocone-sequential-diagramᵉ (succ-ℕᵉ nᵉ) =
    map-cocone-sequential-diagramᵉ cᵉ nᵉ
  pr2ᵉ unshift-once-cocone-sequential-diagramᵉ zero-ℕᵉ =
    refl-htpyᵉ
  pr2ᵉ unshift-once-cocone-sequential-diagramᵉ (succ-ℕᵉ nᵉ) =
    coherence-cocone-sequential-diagramᵉ cᵉ nᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  {Xᵉ : UUᵉ l2ᵉ}
  where

  unshift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    cocone-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) Xᵉ →
    cocone-sequential-diagramᵉ Aᵉ Xᵉ
  unshift-cocone-sequential-diagramᵉ zero-ℕᵉ cᵉ =
    cᵉ
  unshift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) cᵉ =
    unshift-cocone-sequential-diagramᵉ kᵉ
      ( unshift-once-cocone-sequential-diagramᵉ
        ( shift-sequential-diagramᵉ kᵉ Aᵉ)
        ( cᵉ))
```

### Shifts of homotopies of cocones under sequential diagrams

Givenᵉ coconesᵉ `c`ᵉ andᵉ `c'`ᵉ underᵉ `A`ᵉ

```text
     a₀ᵉ      a₁ᵉ                   a₀ᵉ      a₁ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
  \ᵉ      |      /ᵉ              \ᵉ      |      /ᵉ
   \ᵉ     | i₁ᵉ  /ᵉ                \ᵉ     | i'₁ᵉ /ᵉ
 i₀ᵉ \ᵉ    |    /ᵉ i₂ᵉ     ~ᵉ     i'₀ᵉ \ᵉ    |    /ᵉ i'₂ᵉ
     \ᵉ   |   /ᵉ                    \ᵉ   |   /ᵉ
      ∨ᵉ  ∨ᵉ  ∨ᵉ                      ∨ᵉ  ∨ᵉ  ∨ᵉ
         Xᵉ                            Xᵉ
```

andᵉ aᵉ homotopyᵉ `Hᵉ : cᵉ ~ᵉ c'`ᵉ betweenᵉ them,ᵉ weᵉ canᵉ againᵉ forgetᵉ theᵉ firstᵉ homotopyᵉ
ofᵉ mapsᵉ andᵉ coherenceᵉ to getᵉ theᵉ homotopyᵉ `H[1ᵉ] : c[1ᵉ] ~ᵉ c'[1]`.ᵉ Inductively,ᵉ weᵉ
defineᵉ `H[kᵉ +ᵉ 1ᵉ] ≐ᵉ H[k][1]`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Hᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ)
  where

  shift-once-htpy-cocone-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( shift-once-cocone-sequential-diagramᵉ cᵉ)
      ( shift-once-cocone-sequential-diagramᵉ c'ᵉ)
  pr1ᵉ shift-once-htpy-cocone-sequential-diagramᵉ nᵉ =
    htpy-htpy-cocone-sequential-diagramᵉ Hᵉ (succ-ℕᵉ nᵉ)
  pr2ᵉ shift-once-htpy-cocone-sequential-diagramᵉ nᵉ =
    coherence-htpy-htpy-cocone-sequential-diagramᵉ
      ( Hᵉ)
      ( succ-ℕᵉ nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  where

  shift-htpy-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ →
    htpy-cocone-sequential-diagramᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ)
      ( shift-cocone-sequential-diagramᵉ kᵉ c'ᵉ)
  shift-htpy-cocone-sequential-diagramᵉ zero-ℕᵉ Hᵉ =
    Hᵉ
  shift-htpy-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) Hᵉ =
    shift-once-htpy-cocone-sequential-diagramᵉ
      ( shift-htpy-cocone-sequential-diagramᵉ kᵉ Hᵉ)
```

### Unshifts of homotopies of cocones under sequential diagrams

Similarlyᵉ to unshiftingᵉ cocones,ᵉ weᵉ canᵉ recoverᵉ theᵉ firstᵉ homotopyᵉ andᵉ coherenceᵉ
to unshiftᵉ aᵉ homotopyᵉ ofᵉ cocones.ᵉ Givenᵉ twoᵉ coconesᵉ `c`,ᵉ `c'`ᵉ underᵉ `A[1]`ᵉ

```text
         a₁ᵉ                     a₁ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ      A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |      /ᵉ               |      /ᵉ
     |     /ᵉ                |     /ᵉ
  i₁ᵉ |    /ᵉ i₂ᵉ     ~ᵉ    i'₁ᵉ |    /ᵉ i'₂ᵉ
     |   /ᵉ                  |   /ᵉ
     ∨ᵉ  ∨ᵉ                   ∨ᵉ  ∨ᵉ
     Xᵉ                      Xᵉ
```

andᵉ aᵉ homotopyᵉ `Hᵉ : cᵉ ~ᵉ c'`,ᵉ weᵉ needᵉ to showᵉ thatᵉ `i₁ᵉ ∘ᵉ a₀ᵉ ~ᵉ i'₁ᵉ ∘ᵉ a₀`.ᵉ Thisᵉ canᵉ
beᵉ obtainedᵉ byᵉ whiskeringᵉ `H₀ᵉ ·rᵉ a₀`,ᵉ whichᵉ makesᵉ theᵉ coherenceᵉ trivial.ᵉ

Inductively,ᵉ weᵉ defineᵉ `H[-(kᵉ +ᵉ 1ᵉ)] ≐ᵉ H[-1][-k]`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) Xᵉ}
  (Hᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ)
  where

  unshift-once-htpy-cocone-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( unshift-once-cocone-sequential-diagramᵉ Aᵉ cᵉ)
      ( unshift-once-cocone-sequential-diagramᵉ Aᵉ c'ᵉ)
  pr1ᵉ unshift-once-htpy-cocone-sequential-diagramᵉ zero-ℕᵉ =
    ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ zero-ℕᵉ) ·rᵉ
    ( map-sequential-diagramᵉ Aᵉ zero-ℕᵉ)
  pr1ᵉ unshift-once-htpy-cocone-sequential-diagramᵉ (succ-ℕᵉ nᵉ) =
    htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ
  pr2ᵉ unshift-once-htpy-cocone-sequential-diagramᵉ zero-ℕᵉ =
    inv-htpy-right-unit-htpyᵉ
  pr2ᵉ unshift-once-htpy-cocone-sequential-diagramᵉ (succ-ℕᵉ nᵉ) =
    coherence-htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  where

  unshift-htpy-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    {cᵉ c'ᵉ : cocone-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) Xᵉ} →
    htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ →
    htpy-cocone-sequential-diagramᵉ
      ( unshift-cocone-sequential-diagramᵉ Aᵉ kᵉ cᵉ)
      ( unshift-cocone-sequential-diagramᵉ Aᵉ kᵉ c'ᵉ)
  unshift-htpy-cocone-sequential-diagramᵉ zero-ℕᵉ Hᵉ =
    Hᵉ
  unshift-htpy-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) Hᵉ =
    unshift-htpy-cocone-sequential-diagramᵉ kᵉ
      (unshift-once-htpy-cocone-sequential-diagramᵉ Hᵉ)
```

### Morphisms from sequential diagrams into their shifts

Theᵉ morphismᵉ isᵉ obtainedᵉ byᵉ observingᵉ thatᵉ theᵉ squaresᵉ in theᵉ diagramᵉ

```text
        a₀ᵉ      a₁ᵉ
    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
    |       |       |
 a₀ᵉ |       | a₁ᵉ    | a₂ᵉ
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ A₃ᵉ --->ᵉ ⋯ᵉ
        a₁ᵉ      a₂ᵉ
```

commuteᵉ byᵉ reflexivity.ᵉ

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  hom-shift-once-sequential-diagramᵉ :
    hom-sequential-diagramᵉ
      ( Aᵉ)
      ( shift-once-sequential-diagramᵉ Aᵉ)
  pr1ᵉ hom-shift-once-sequential-diagramᵉ = map-sequential-diagramᵉ Aᵉ
  pr2ᵉ hom-shift-once-sequential-diagramᵉ nᵉ = refl-htpyᵉ

module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  hom-shift-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    hom-sequential-diagramᵉ
      ( Aᵉ)
      ( shift-sequential-diagramᵉ kᵉ Aᵉ)
  hom-shift-sequential-diagramᵉ zero-ℕᵉ = id-hom-sequential-diagramᵉ Aᵉ
  hom-shift-sequential-diagramᵉ (succ-ℕᵉ kᵉ) =
    comp-hom-sequential-diagramᵉ
      ( Aᵉ)
      ( shift-sequential-diagramᵉ kᵉ Aᵉ)
      ( shift-sequential-diagramᵉ (succ-ℕᵉ kᵉ) Aᵉ)
      ( hom-shift-once-sequential-diagramᵉ
        ( shift-sequential-diagramᵉ kᵉ Aᵉ))
      ( hom-shift-sequential-diagramᵉ kᵉ)
```

## Properties

### The type of cocones under a sequential diagram is equivalent to the type of cocones under its shift

Thisᵉ isᵉ shownᵉ byᵉ provingᵉ thatᵉ shiftingᵉ andᵉ unshiftingᵉ ofᵉ coconesᵉ areᵉ mutuallyᵉ
inverseᵉ operations.ᵉ

Toᵉ showᵉ thatᵉ `shiftᵉ ∘ᵉ unshiftᵉ ~ᵉ id`ᵉ isᵉ trivial,ᵉ sinceᵉ theᵉ firstᵉ stepᵉ synthesizesᵉ
someᵉ data forᵉ theᵉ firstᵉ level,ᵉ whichᵉ theᵉ secondᵉ stepᵉ promptlyᵉ forgets.ᵉ

Inᵉ theᵉ inductive step,ᵉ weᵉ needᵉ to showᵉ `c[-(kᵉ +ᵉ 1)][kᵉ +ᵉ 1ᵉ] ~ᵉ c`.ᵉ Theᵉ left-handᵉ
sideᵉ computesᵉ to `c[-1][-k][k][1]`,ᵉ whichᵉ isᵉ homotopicᵉ to `c[-1][1]`ᵉ byᵉ shiftingᵉ
theᵉ homotopyᵉ givenᵉ byᵉ theᵉ inductive hypothesis,ᵉ andᵉ thatᵉ computesᵉ to `c`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  htpy-is-section-unshift-once-cocone-sequential-diagramᵉ :
    (cᵉ : cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) Xᵉ) →
    htpy-cocone-sequential-diagramᵉ
      ( shift-once-cocone-sequential-diagramᵉ
        ( unshift-once-cocone-sequential-diagramᵉ Aᵉ cᵉ))
      ( cᵉ)
  htpy-is-section-unshift-once-cocone-sequential-diagramᵉ cᵉ =
    refl-htpy-cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) cᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  htpy-is-section-unshift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    (cᵉ : cocone-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) Xᵉ) →
    htpy-cocone-sequential-diagramᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ
        ( unshift-cocone-sequential-diagramᵉ Aᵉ kᵉ cᵉ))
      ( cᵉ)
  htpy-is-section-unshift-cocone-sequential-diagramᵉ zero-ℕᵉ cᵉ =
    refl-htpy-cocone-sequential-diagramᵉ Aᵉ cᵉ
  htpy-is-section-unshift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) cᵉ =
    shift-once-htpy-cocone-sequential-diagramᵉ
      ( htpy-is-section-unshift-cocone-sequential-diagramᵉ kᵉ
        ( unshift-once-cocone-sequential-diagramᵉ
          ( shift-sequential-diagramᵉ kᵉ Aᵉ)
          ( cᵉ)))

  is-section-unshift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    is-sectionᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ)
      ( unshift-cocone-sequential-diagramᵉ Aᵉ {Xᵉ} kᵉ)
  is-section-unshift-cocone-sequential-diagramᵉ kᵉ cᵉ =
    eq-htpy-cocone-sequential-diagramᵉ
      ( shift-sequential-diagramᵉ kᵉ Aᵉ)
      ( _)
      ( _)
      ( htpy-is-section-unshift-cocone-sequential-diagramᵉ kᵉ cᵉ)
```

Forᵉ theᵉ otherᵉ direction,ᵉ weᵉ needᵉ to showᵉ thatᵉ theᵉ synthesizedᵉ data,ᵉ namelyᵉ theᵉ
mapᵉ `i₁ᵉ ∘ᵉ a₀ᵉ : A₀ᵉ → X`ᵉ andᵉ theᵉ reflexiveᵉ homotopy,ᵉ isᵉ consistentᵉ with theᵉ
originalᵉ data `i₀ᵉ : A₀ᵉ → X`ᵉ andᵉ theᵉ homotopyᵉ `H₀ᵉ : i₀ᵉ ~ᵉ i₁ᵉ ∘ᵉ a₀`.ᵉ Itᵉ isᵉ moreᵉ
convenientᵉ to showᵉ theᵉ inverseᵉ homotopyᵉ `idᵉ ~ᵉ unshiftᵉ ∘ᵉ shift`,ᵉ becauseᵉ `H₀`ᵉ
givesᵉ usᵉ exactlyᵉ theᵉ rightᵉ homotopyᵉ forᵉ theᵉ firstᵉ level,ᵉ soᵉ theᵉ restᵉ ofᵉ theᵉ
coherencesᵉ areᵉ alsoᵉ trivial.ᵉ

Inᵉ theᵉ inductive step,ᵉ weᵉ needᵉ to showᵉ
`cᵉ ~ᵉ c[kᵉ +ᵉ 1][-(kᵉ +ᵉ 1ᵉ)] ≐ᵉ c[k][1][-1][-k]`.ᵉ Thisᵉ followsᵉ fromᵉ theᵉ inductive
hypothesis,ᵉ whichᵉ statesᵉ thatᵉ `cᵉ ~ᵉ c[k][-k]`,ᵉ andᵉ whichᵉ weᵉ composeᵉ with theᵉ
homotopyᵉ `c[kᵉ] ~ᵉ c[k][1][-1]`ᵉ unshiftedᵉ byᵉ `k`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ :
    (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) →
    htpy-cocone-sequential-diagramᵉ
      ( cᵉ)
      ( unshift-once-cocone-sequential-diagramᵉ Aᵉ
        ( shift-once-cocone-sequential-diagramᵉ cᵉ))
  pr1ᵉ (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ cᵉ)
    zero-ℕᵉ =
    coherence-cocone-sequential-diagramᵉ cᵉ zero-ℕᵉ
  pr1ᵉ (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ cᵉ)
    (succ-ℕᵉ nᵉ) =
    refl-htpyᵉ
  pr2ᵉ (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ cᵉ)
    zero-ℕᵉ =
    refl-htpyᵉ
  pr2ᵉ (inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ cᵉ)
    (succ-ℕᵉ nᵉ) =
    right-unit-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  inv-htpy-is-retraction-unshift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) →
    htpy-cocone-sequential-diagramᵉ
      ( cᵉ)
      ( unshift-cocone-sequential-diagramᵉ Aᵉ kᵉ
        ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ))
  inv-htpy-is-retraction-unshift-cocone-sequential-diagramᵉ zero-ℕᵉ cᵉ =
    refl-htpy-cocone-sequential-diagramᵉ Aᵉ cᵉ
  inv-htpy-is-retraction-unshift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) cᵉ =
    concat-htpy-cocone-sequential-diagramᵉ
      ( inv-htpy-is-retraction-unshift-cocone-sequential-diagramᵉ kᵉ cᵉ)
      ( unshift-htpy-cocone-sequential-diagramᵉ kᵉ
        ( inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ
          ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ)))

  is-retraction-unshift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    is-retractionᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ)
      ( unshift-cocone-sequential-diagramᵉ Aᵉ {Xᵉ} kᵉ)
  is-retraction-unshift-cocone-sequential-diagramᵉ kᵉ cᵉ =
    invᵉ
      ( eq-htpy-cocone-sequential-diagramᵉ Aᵉ _ _
        ( inv-htpy-is-retraction-unshift-cocone-sequential-diagramᵉ kᵉ cᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  where

  is-equiv-shift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    is-equivᵉ (shift-cocone-sequential-diagramᵉ {Xᵉ = Xᵉ} kᵉ)
  is-equiv-shift-cocone-sequential-diagramᵉ kᵉ =
    is-equiv-is-invertibleᵉ
      ( unshift-cocone-sequential-diagramᵉ Aᵉ kᵉ)
      ( is-section-unshift-cocone-sequential-diagramᵉ kᵉ)
      ( is-retraction-unshift-cocone-sequential-diagramᵉ kᵉ)

  equiv-shift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    cocone-sequential-diagramᵉ Aᵉ Xᵉ ≃ᵉ
    cocone-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) Xᵉ
  pr1ᵉ (equiv-shift-cocone-sequential-diagramᵉ kᵉ) =
    shift-cocone-sequential-diagramᵉ kᵉ
  pr2ᵉ (equiv-shift-cocone-sequential-diagramᵉ kᵉ) =
    is-equiv-shift-cocone-sequential-diagramᵉ kᵉ
```

### The sequential colimit of a sequential diagram is also the sequential colimit of its shift

Givenᵉ aᵉ sequentialᵉ colimitᵉ

```text
     a₀ᵉ      a₁ᵉ      a₂ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ -->ᵉ X,ᵉ
```

thereᵉ isᵉ aᵉ commutingᵉ triangleᵉ

```text
              cocone-mapᵉ
      Xᵉ → Yᵉ ------------>ᵉ coconeᵉ Aᵉ Yᵉ
            \ᵉ           /ᵉ
  cocone-mapᵉ  \ᵉ       /ᵉ
                ∨ᵉ   ∨ᵉ
             coconeᵉ A[1ᵉ] Y.ᵉ
```

Inductively,ᵉ weᵉ composeᵉ thisᵉ triangleᵉ in theᵉ followingᵉ wayᵉ

```text
              cocone-mapᵉ
      Xᵉ → Yᵉ ------------>ᵉ coconeᵉ Aᵉ Yᵉ
            \⟍ᵉ             |
             \ᵉ ⟍ᵉ           |
              \ᵉ  ⟍ᵉ         |
               \ᵉ   ⟍ᵉ       ∨ᵉ
                \ᵉ    >ᵉ coconeᵉ A[kᵉ] Yᵉ
     cocone-mapᵉ  \ᵉ       /ᵉ
                  \ᵉ     /ᵉ
                   \ᵉ   /ᵉ
                    ∨ᵉ ∨ᵉ
             coconeᵉ A[kᵉ +ᵉ 1ᵉ] Y,ᵉ
```

where theᵉ topᵉ triangleᵉ isᵉ theᵉ inductive hypothesis,ᵉ andᵉ theᵉ bottomᵉ triangleᵉ isᵉ
theᵉ stepᵉ instantiatedᵉ atᵉ `A[k]`.ᵉ

Thisᵉ givesᵉ usᵉ theᵉ commutingᵉ triangleᵉ

```text
              cocone-mapᵉ
      Xᵉ → Yᵉ ------------>ᵉ coconeᵉ Aᵉ Yᵉ
            \ᵉ     ≃ᵉ     /ᵉ
  cocone-mapᵉ  \ᵉ       /ᵉ ≃ᵉ
                ∨ᵉ   ∨ᵉ
             coconeᵉ A[kᵉ] Y,ᵉ
```

where theᵉ topᵉ mapᵉ isᵉ anᵉ equivalenceᵉ byᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ coconeᵉ onᵉ
`X`,ᵉ andᵉ theᵉ rightᵉ mapᵉ isᵉ anᵉ equivalenceᵉ byᵉ aᵉ theoremᵉ shownᵉ above,ᵉ whichᵉ impliesᵉ
thatᵉ theᵉ leftᵉ mapᵉ isᵉ anᵉ equivalence,ᵉ whichᵉ exactlyᵉ saysᵉ thatᵉ `X`ᵉ isᵉ theᵉ
sequentialᵉ colimitᵉ ofᵉ `A[k]`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  triangle-cocone-map-shift-once-cocone-sequential-diagramᵉ :
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( cocone-map-sequential-diagramᵉ
        ( shift-once-cocone-sequential-diagramᵉ cᵉ)
        { Yᵉ = Yᵉ})
      ( shift-once-cocone-sequential-diagramᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
  triangle-cocone-map-shift-once-cocone-sequential-diagramᵉ Yᵉ = refl-htpyᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  triangle-cocone-map-shift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( cocone-map-sequential-diagramᵉ
        ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ))
      ( shift-cocone-sequential-diagramᵉ kᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
  triangle-cocone-map-shift-cocone-sequential-diagramᵉ zero-ℕᵉ Yᵉ =
    refl-htpyᵉ
  triangle-cocone-map-shift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) Yᵉ =
    ( triangle-cocone-map-shift-once-cocone-sequential-diagramᵉ
      ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ)
      ( Yᵉ)) ∙hᵉ
    ( ( shift-once-cocone-sequential-diagramᵉ) ·lᵉ
      ( triangle-cocone-map-shift-cocone-sequential-diagramᵉ kᵉ Yᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  where

  up-shift-cocone-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    universal-property-sequential-colimitᵉ cᵉ →
    universal-property-sequential-colimitᵉ (shift-cocone-sequential-diagramᵉ kᵉ cᵉ)
  up-shift-cocone-sequential-diagramᵉ kᵉ up-cᵉ Yᵉ =
    is-equiv-left-map-triangleᵉ
      ( cocone-map-sequential-diagramᵉ
        ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ))
      ( shift-cocone-sequential-diagramᵉ kᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( triangle-cocone-map-shift-cocone-sequential-diagramᵉ cᵉ kᵉ Yᵉ)
      ( up-cᵉ Yᵉ)
      ( is-equiv-shift-cocone-sequential-diagramᵉ kᵉ)
```

Weᵉ instantiateᵉ thisᵉ theoremᵉ forᵉ theᵉ standardᵉ sequentialᵉ colimits,ᵉ givingᵉ usᵉ
`A[k]∞ᵉ ≃ᵉ A∞`.ᵉ

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  compute-sequential-colimit-shift-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    standard-sequential-colimitᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ) ≃ᵉ
    standard-sequential-colimitᵉ Aᵉ
  pr1ᵉ (compute-sequential-colimit-shift-sequential-diagramᵉ kᵉ) =
    cogap-standard-sequential-colimitᵉ
      ( shift-cocone-sequential-diagramᵉ
        ( kᵉ)
        ( cocone-standard-sequential-colimitᵉ Aᵉ))
  pr2ᵉ (compute-sequential-colimit-shift-sequential-diagramᵉ kᵉ) =
    is-sequential-colimit-universal-propertyᵉ _
      ( up-shift-cocone-sequential-diagramᵉ kᵉ up-standard-sequential-colimitᵉ)
```

### Unshifting cocones under sequential diagrams is homotopic to precomposing them with shift inclusion morphisms

Givenᵉ aᵉ coconeᵉ `c`ᵉ

```text
         a₁ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |      /ᵉ
     |     /ᵉ
  i₁ᵉ |    /ᵉ i₂ᵉ
     |   /ᵉ
     ∨ᵉ  ∨ᵉ
     Xᵉ
```

underᵉ `A[1]`,ᵉ weᵉ haveᵉ twoᵉ wayᵉ ofᵉ turningᵉ itᵉ intoᵉ aᵉ coconeᵉ underᵉ `A`ᵉ ---ᵉ weᵉ canᵉ
unshiftᵉ it,ᵉ whichᵉ givesᵉ theᵉ coconeᵉ

```text
           a₀ᵉ      a₁ᵉ
       A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
        \ᵉ      |      /ᵉ
         \ᵉ     |     /ᵉ
  i₁ᵉ ∘ᵉ a₀ᵉ \ᵉ    | i₁ᵉ /ᵉ i₂ᵉ
           \ᵉ   |   /ᵉ
            ∨ᵉ  ∨ᵉ  ∨ᵉ
               Xᵉ ,ᵉ
```

orᵉ weᵉ canᵉ prependᵉ theᵉ inclusionᵉ morphismᵉ
`hom-shift-sequential-diagramᵉ : Aᵉ → A[1]`ᵉ to getᵉ

```text
         a₀ᵉ
     A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ ⋯ᵉ
     |       |
  a₀ᵉ |       | a₁ᵉ
     ∨ᵉ   a₁ᵉ  ∨ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |      /ᵉ
     |     /ᵉ
  i₁ᵉ |    /ᵉ i₂ᵉ
     |   /ᵉ
     ∨ᵉ  ∨ᵉ
     Xᵉ .ᵉ
```

Weᵉ showᵉ thatᵉ theseᵉ twoᵉ coconesᵉ areᵉ homotopic.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cocone-sequential-diagramᵉ (shift-once-sequential-diagramᵉ Aᵉ) Xᵉ)
  where

  htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( unshift-once-cocone-sequential-diagramᵉ Aᵉ cᵉ)
      ( map-cocone-hom-sequential-diagramᵉ
        ( hom-shift-once-sequential-diagramᵉ Aᵉ)
        ( cᵉ))
  pr1ᵉ htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ
    zero-ℕᵉ = refl-htpyᵉ
  pr1ᵉ htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ
    (succ-ℕᵉ nᵉ) = coherence-cocone-sequential-diagramᵉ cᵉ nᵉ
  pr2ᵉ htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ
    zero-ℕᵉ = inv-htpy-right-unit-htpyᵉ
  pr2ᵉ htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ
    (succ-ℕᵉ nᵉ) =
    left-whisker-concat-htpyᵉ
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( inv-htpy-right-unit-htpyᵉ)
```

Asᵉ aᵉ corollary,ᵉ takingᵉ aᵉ coconeᵉ `c`ᵉ underᵉ `A`,ᵉ shiftingᵉ itᵉ andᵉ prependingᵉ theᵉ
shiftᵉ inclusionᵉ morphismᵉ resultsᵉ in aᵉ coconeᵉ homotopicᵉ to `c`,ᵉ i.e.,ᵉ

```text
         a₀ᵉ      a₁ᵉ
     A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     |       |       |                     a₀ᵉ      a₁ᵉ
  a₀ᵉ |       | a₁ᵉ    | a₂ᵉ              A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
     ∨ᵉ   a₁ᵉ  ∨ᵉ   a₂ᵉ  ∨ᵉ                  \ᵉ      |      /ᵉ
     A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ A₃ᵉ --->ᵉ ⋯ᵉ    ~ᵉ      \ᵉ     | i₁ᵉ  /ᵉ
      \ᵉ      |      /ᵉ                  i₀ᵉ \ᵉ    |    /ᵉ i₂ᵉ
       \ᵉ     |     /ᵉ                       \ᵉ   |   /ᵉ
     i₁ᵉ \ᵉ    | i₂ᵉ /ᵉ i₃ᵉ                      ∨ᵉ  ∨ᵉ  ∨ᵉ
         \ᵉ   |   /ᵉ                             Xᵉ .ᵉ
          ∨ᵉ  ∨ᵉ  ∨ᵉ
             Xᵉ
```

**Proof:**ᵉ Weᵉ firstᵉ useᵉ theᵉ aboveᵉ lemma,ᵉ whichᵉ saysᵉ thatᵉ theᵉ leftᵉ coconeᵉ isᵉ
homotopicᵉ to `c[1][-1]`,ᵉ andᵉ thenᵉ weᵉ useᵉ theᵉ factᵉ thatᵉ unshiftingᵉ isᵉ aᵉ
retraction.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  inv-compute-map-cocone-hom-shift-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( cᵉ)
      ( map-cocone-hom-sequential-diagramᵉ
        ( hom-shift-once-sequential-diagramᵉ Aᵉ)
        ( shift-once-cocone-sequential-diagramᵉ cᵉ))
  inv-compute-map-cocone-hom-shift-sequential-diagramᵉ =
    concat-htpy-cocone-sequential-diagramᵉ
      ( inv-htpy-is-retraction-unshift-once-cocone-sequential-diagramᵉ cᵉ)
      ( htpy-cocone-unshift-cocone-map-cocone-hom-shift-sequential-diagramᵉ
        ( shift-once-cocone-sequential-diagramᵉ cᵉ))

  compute-map-cocone-hom-shift-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( map-cocone-hom-sequential-diagramᵉ
        ( hom-shift-once-sequential-diagramᵉ Aᵉ)
        ( shift-once-cocone-sequential-diagramᵉ cᵉ))
      ( cᵉ)
  compute-map-cocone-hom-shift-sequential-diagramᵉ =
    inv-htpy-cocone-sequential-diagramᵉ
      ( inv-compute-map-cocone-hom-shift-sequential-diagramᵉ)
```

### Inclusion morphisms of shifting sequential diagrams induce the identity map on sequential colimits

Givenᵉ aᵉ sequentialᵉ diagramᵉ `(A,ᵉ a)`ᵉ with aᵉ colimitᵉ `X`,ᵉ thenᵉ weᵉ knowᵉ thatᵉ forᵉ
everyᵉ naturalᵉ numberᵉ `k`ᵉ

-ᵉ `X`ᵉ isᵉ alsoᵉ aᵉ sequentialᵉ colimitᵉ ofᵉ `A[k]`ᵉ andᵉ
-ᵉ thereᵉ isᵉ aᵉ morphismᵉ `Aᵉ → A[k]`,ᵉ inducingᵉ aᵉ mapᵉ betweenᵉ colimits.ᵉ

Togetherᵉ theyᵉ giveᵉ aᵉ mapᵉ `Xᵉ → X`,ᵉ whichᵉ weᵉ showᵉ hereᵉ to beᵉ theᵉ identityᵉ map.ᵉ

**Proof:**ᵉ Byᵉ inductionᵉ onᵉ `k`;ᵉ forᵉ theᵉ baseᵉ case,ᵉ observeᵉ thatᵉ `Aᵉ → A[0]`ᵉ isᵉ
theᵉ identityᵉ morphism,ᵉ whichᵉ getsᵉ sentᵉ to theᵉ identityᵉ mapᵉ byᵉ functorialityᵉ ofᵉ
sequentialᵉ colimits.ᵉ

Forᵉ theᵉ inductive case,ᵉ observeᵉ thatᵉ theᵉ inclusionᵉ morphismᵉ `Aᵉ → A[kᵉ +ᵉ 1]`ᵉ isᵉ
definedᵉ asᵉ theᵉ compositionᵉ `Aᵉ → A[kᵉ] → A[kᵉ +ᵉ 1]`,ᵉ soᵉ byᵉ functorialityᵉ theᵉ
inducedᵉ mapᵉ isᵉ theᵉ compositionᵉ ofᵉ theᵉ mapsᵉ inducedᵉ byᵉ `Aᵉ → A[k]`ᵉ andᵉ
`A[kᵉ] → A[kᵉ +ᵉ 1]`.ᵉ Theᵉ firstᵉ inducedᵉ mapᵉ isᵉ theᵉ identityᵉ mapᵉ byᵉ theᵉ inductive
hypothesis.ᵉ Theᵉ secondᵉ inducedᵉ mapᵉ isᵉ definedᵉ to beᵉ theᵉ mapᵉ obtainedᵉ byᵉ theᵉ
universalᵉ propertyᵉ ofᵉ `X`ᵉ asᵉ aᵉ colimitᵉ ofᵉ `A[k]`ᵉ fromᵉ theᵉ coconeᵉ `c[kᵉ +ᵉ 1]`ᵉ
precomposedᵉ byᵉ theᵉ inclusionᵉ `A[kᵉ] → A[kᵉ +ᵉ 1]`.ᵉ Weᵉ haveᵉ seenᵉ aboveᵉ thatᵉ thisᵉ
precompositionᵉ resultsᵉ in aᵉ coconeᵉ homotopicᵉ to `c[k]`,ᵉ soᵉ theᵉ mapᵉ inducedᵉ byᵉ
`A[kᵉ] → A[kᵉ +ᵉ 1]`ᵉ isᵉ homotopicᵉ to theᵉ oneᵉ inducedᵉ byᵉ `c[k]`.ᵉ Butᵉ `c[k]`ᵉ isᵉ theᵉ
coconeᵉ ofᵉ theᵉ sequentialᵉ colimitᵉ ofᵉ `A[k]`,ᵉ soᵉ itᵉ alsoᵉ inducesᵉ theᵉ identityᵉ map.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  compute-map-colimit-hom-shift-once-sequential-diagramᵉ :
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( shift-once-cocone-sequential-diagramᵉ cᵉ)
      ( hom-shift-once-sequential-diagramᵉ Aᵉ) ~ᵉ
    idᵉ
  compute-map-colimit-hom-shift-once-sequential-diagramᵉ =
    ( htpy-map-universal-property-htpy-cocone-sequential-diagramᵉ
      ( up-cᵉ)
      ( compute-map-cocone-hom-shift-sequential-diagramᵉ cᵉ)) ∙hᵉ
    ( compute-map-universal-property-sequential-colimit-idᵉ up-cᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  compute-map-colimit-hom-shift-sequential-diagramᵉ :
    (kᵉ : ℕᵉ) →
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( shift-cocone-sequential-diagramᵉ kᵉ cᵉ)
      ( hom-shift-sequential-diagramᵉ Aᵉ kᵉ) ~ᵉ
    idᵉ
  compute-map-colimit-hom-shift-sequential-diagramᵉ zero-ℕᵉ =
    preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ
  compute-map-colimit-hom-shift-sequential-diagramᵉ (succ-ℕᵉ kᵉ) =
    ( preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( up-shift-cocone-sequential-diagramᵉ kᵉ up-cᵉ)
      ( shift-cocone-sequential-diagramᵉ (succ-ℕᵉ kᵉ) cᵉ)
      ( hom-shift-once-sequential-diagramᵉ (shift-sequential-diagramᵉ kᵉ Aᵉ))
      ( hom-shift-sequential-diagramᵉ Aᵉ kᵉ)) ∙hᵉ
    ( horizontal-concat-htpyᵉ
      ( compute-map-colimit-hom-shift-once-sequential-diagramᵉ
        ( up-shift-cocone-sequential-diagramᵉ kᵉ up-cᵉ))
      ( compute-map-colimit-hom-shift-sequential-diagramᵉ kᵉ))
```