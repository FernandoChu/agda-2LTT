# Zigzags between sequential diagrams

```agda
module synthetic-homotopy-theory.zigzags-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.retractionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.functoriality-sequential-colimitsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.shifts-sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "zigzag"ᵉ Disambiguation="sequentialᵉ diagrams"ᵉ Agda=zigzag-sequential-diagramᵉ}}
betweenᵉ [sequentialᵉ diagrams](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`ᵉ andᵉ `(B,ᵉ b)`ᵉ isᵉ aᵉ pairᵉ ofᵉ familiesᵉ ofᵉ mapsᵉ

```text
  fₙᵉ : Aₙᵉ → Bₙᵉ
  gₙᵉ : Bₙᵉ → Aₙ₊₁ᵉ
```

andᵉ [coherences](foundation-core.commuting-triangles-of-maps.mdᵉ) betweenᵉ them,ᵉ
suchᵉ thatᵉ theyᵉ fitᵉ in theᵉ followingᵉ diagramᵉ:

```text
       a₀ᵉ        a₁ᵉ
  A₀ᵉ ----->ᵉ A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ ⋯ᵉ
   \ᵉ       ∧ᵉ \ᵉ       ∧ᵉ
    \ᵉ     /ᵉ   \ᵉ f₁ᵉ  /ᵉ
  f₀ᵉ \ᵉ   /ᵉ g₀ᵉ  \ᵉ   /ᵉ g₁ᵉ
      ∨ᵉ /ᵉ       ∨ᵉ /ᵉ
      B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ ⋯ᵉ .ᵉ
           b₀ᵉ
```

Givenᵉ [colimits](synthetic-homotopy-theory.sequential-colimits.mdᵉ) `X`ᵉ ofᵉ `A`ᵉ
andᵉ `Y`ᵉ ofᵉ `B`,ᵉ theᵉ zigzagᵉ inducesᵉ mapsᵉ `f∞ᵉ : Xᵉ → Y`ᵉ andᵉ `g∞ᵉ : Yᵉ → X`,ᵉ whichᵉ weᵉ
showᵉ to beᵉ mutuallyᵉ inverseᵉ [equivalences](foundation-core.equivalences.md).ᵉ

## Definitions

### A zigzag between sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  module _
    (fᵉ :
      (nᵉ : ℕᵉ) →
      family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ)
    (gᵉ :
      (nᵉ : ℕᵉ) →
      family-sequential-diagramᵉ Bᵉ nᵉ → family-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ))
    where

    coherence-upper-triangle-zigzag-sequential-diagramᵉ : UUᵉ l1ᵉ
    coherence-upper-triangle-zigzag-sequential-diagramᵉ =
      (nᵉ : ℕᵉ) →
      coherence-triangle-mapsᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ)
        ( gᵉ nᵉ)
        ( fᵉ nᵉ)

    coherence-lower-triangle-zigzag-sequential-diagramᵉ : UUᵉ l2ᵉ
    coherence-lower-triangle-zigzag-sequential-diagramᵉ =
      (nᵉ : ℕᵉ) →
      coherence-triangle-mapsᵉ
        ( map-sequential-diagramᵉ Bᵉ nᵉ)
        ( fᵉ (succ-ℕᵉ nᵉ))
        ( gᵉ nᵉ)

  zigzag-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  zigzag-sequential-diagramᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) →
        family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ)
      ( λ fᵉ →
        Σᵉ ( (nᵉ : ℕᵉ) →
            family-sequential-diagramᵉ Bᵉ nᵉ →
            family-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ))
          ( λ gᵉ →
            coherence-upper-triangle-zigzag-sequential-diagramᵉ fᵉ gᵉ ×ᵉ
            coherence-lower-triangle-zigzag-sequential-diagramᵉ fᵉ gᵉ))
```

### Components of a zigzag of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-zigzag-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ
  map-zigzag-sequential-diagramᵉ = pr1ᵉ zᵉ

  inv-map-zigzag-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Bᵉ nᵉ → family-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)
  inv-map-zigzag-sequential-diagramᵉ = pr1ᵉ (pr2ᵉ zᵉ)

  upper-triangle-zigzag-sequential-diagramᵉ :
    coherence-upper-triangle-zigzag-sequential-diagramᵉ Aᵉ Bᵉ
      ( map-zigzag-sequential-diagramᵉ)
      ( inv-map-zigzag-sequential-diagramᵉ)
  upper-triangle-zigzag-sequential-diagramᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ zᵉ))

  lower-triangle-zigzag-sequential-diagramᵉ :
    coherence-lower-triangle-zigzag-sequential-diagramᵉ Aᵉ Bᵉ
      ( map-zigzag-sequential-diagramᵉ)
      ( inv-map-zigzag-sequential-diagramᵉ)
  lower-triangle-zigzag-sequential-diagramᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ zᵉ))
```

### Half-shifts of zigzags of sequential diagrams

Weᵉ canᵉ forgetᵉ theᵉ firstᵉ triangleᵉ ofᵉ aᵉ zigzagᵉ betweenᵉ `(A,ᵉ a)`ᵉ andᵉ `(B,ᵉ b)`ᵉ to
getᵉ aᵉ zigzagᵉ betweenᵉ `(B,ᵉ b)`ᵉ andᵉ theᵉ
[shift](synthetic-homotopy-theory.shifts-sequential-diagrams.mdᵉ) `(A[1],ᵉ a[1])`ᵉ

```text
       b₀ᵉ        b₁ᵉ
  B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ B₂ᵉ ----->ᵉ ⋯ᵉ
   \ᵉ       ∧ᵉ \ᵉ       ∧ᵉ
    \ᵉ     /ᵉ   \ᵉ g₁ᵉ  /ᵉ
  g₀ᵉ \ᵉ   /ᵉ f₁ᵉ  \ᵉ   /ᵉ f₂ᵉ
      ∨ᵉ /ᵉ       ∨ᵉ /ᵉ
      A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ ⋯ᵉ .ᵉ
           a₁ᵉ
```

Weᵉ callᵉ thisᵉ aᵉ _half-shiftᵉ_ ofᵉ theᵉ originalᵉ zigzag,ᵉ andᵉ itᵉ providesᵉ aᵉ symmetryᵉ
betweenᵉ theᵉ downward-goingᵉ `f`ᵉ mapsᵉ andᵉ upward-goingᵉ `g`ᵉ maps.ᵉ Weᵉ exploitᵉ thisᵉ
symmetryᵉ in theᵉ proceedingᵉ constructionsᵉ byᵉ formulatingᵉ theᵉ definitionsᵉ andᵉ
lemmasᵉ forᵉ theᵉ downwardsᵉ directions,ᵉ andᵉ thenᵉ applyingᵉ themᵉ to theᵉ half-shiftᵉ ofᵉ
aᵉ zigzagᵉ to getᵉ theᵉ constructionsᵉ forᵉ theᵉ upwardᵉ direction.ᵉ

Repeatingᵉ aᵉ half-shiftᵉ twiceᵉ getsᵉ usᵉ aᵉ shiftᵉ ofᵉ aᵉ zigzag.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  half-shift-zigzag-sequential-diagramᵉ :
    zigzag-sequential-diagramᵉ Bᵉ (shift-once-sequential-diagramᵉ Aᵉ)
  pr1ᵉ half-shift-zigzag-sequential-diagramᵉ =
    inv-map-zigzag-sequential-diagramᵉ zᵉ
  pr1ᵉ (pr2ᵉ half-shift-zigzag-sequential-diagramᵉ) nᵉ =
    map-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ half-shift-zigzag-sequential-diagramᵉ)) =
    lower-triangle-zigzag-sequential-diagramᵉ zᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ half-shift-zigzag-sequential-diagramᵉ)) nᵉ =
    upper-triangle-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  shift-zigzag-sequential-diagramᵉ :
    zigzag-sequential-diagramᵉ
      ( shift-once-sequential-diagramᵉ Aᵉ)
      ( shift-once-sequential-diagramᵉ Bᵉ)
  shift-zigzag-sequential-diagramᵉ =
    half-shift-zigzag-sequential-diagramᵉ
      ( half-shift-zigzag-sequential-diagramᵉ zᵉ)
```

### Morphisms of sequential diagrams induced by zigzags of sequential diagrams

Weᵉ canᵉ realignᵉ aᵉ zigzagᵉ

```text
       a₀ᵉ        a₁ᵉ
  A₀ᵉ ----->ᵉ A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ ⋯ᵉ
   \ᵉ       ∧ᵉ \ᵉ       ∧ᵉ
    \ᵉ     /ᵉ   \ᵉ f₁ᵉ  /ᵉ
  f₀ᵉ \ᵉ   /ᵉ g₀ᵉ  \ᵉ   /ᵉ g₁ᵉ
      ∨ᵉ /ᵉ       ∨ᵉ /ᵉ
      B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ ⋯ᵉ
           b₀ᵉ
```

intoᵉ aᵉ [morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ)
`fᵉ : Aᵉ → B`ᵉ

```text
          a₀ᵉ        a₁ᵉ
     A₀ᵉ ----->ᵉ A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ ⋯ᵉ
     |        ∧|ᵉ        ∧|ᵉ
  f₀ᵉ |   g₀ᵉ /ᵉ  | f₁ᵉ   /ᵉ  | f₂ᵉ
     |    /ᵉ    |    /ᵉ g₁ᵉ |
     ∨ᵉ  /ᵉ      ∨ᵉ  /ᵉ      ∨ᵉ
     B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ B₂ᵉ ----->ᵉ ⋯ᵉ .ᵉ
          b₀ᵉ        b₁ᵉ
```

Similarly,ᵉ weᵉ canᵉ realignᵉ theᵉ half-shiftᵉ ofᵉ aᵉ zigzagᵉ to getᵉ theᵉ morphismᵉ
`gᵉ : Bᵉ → A[1]`ᵉ:

```text
          b₀ᵉ        b₁ᵉ
     B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ B₂ᵉ ----->ᵉ ⋯ᵉ
     |        ∧|ᵉ        ∧|ᵉ
  g₀ᵉ |   f₁ᵉ /ᵉ  | g₁ᵉ   /ᵉ  | g₂ᵉ
     |    /ᵉ    |    /ᵉ f₂ᵉ |
     ∨ᵉ  /ᵉ      ∨ᵉ  /ᵉ      ∨ᵉ
     A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ A₃ᵉ ----->ᵉ ⋯ᵉ ,ᵉ
          a₁ᵉ        a₂ᵉ
```

whichᵉ shouldᵉ beᵉ thoughtᵉ ofᵉ asᵉ anᵉ inverseᵉ ofᵉ `f`ᵉ ---ᵉ andᵉ weᵉ showᵉ thatᵉ itᵉ indeedᵉ
inducesᵉ anᵉ inverseᵉ in theᵉ colimitᵉ furtherᵉ down.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  hom-diagram-zigzag-sequential-diagramᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ
  pr1ᵉ hom-diagram-zigzag-sequential-diagramᵉ =
    map-zigzag-sequential-diagramᵉ zᵉ
  pr2ᵉ hom-diagram-zigzag-sequential-diagramᵉ nᵉ =
    horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-zigzag-sequential-diagramᵉ zᵉ nᵉ)
      ( map-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( inv-htpyᵉ (upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ))
      ( lower-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  inv-hom-diagram-zigzag-sequential-diagramᵉ :
    hom-sequential-diagramᵉ Bᵉ (shift-once-sequential-diagramᵉ Aᵉ)
  inv-hom-diagram-zigzag-sequential-diagramᵉ =
    hom-diagram-zigzag-sequential-diagramᵉ
      ( half-shift-zigzag-sequential-diagramᵉ zᵉ)
```

### Zigzags of sequential diagrams unfold to the shifting morphism of sequential diagrams

Afterᵉ composingᵉ theᵉ morphismsᵉ inducedᵉ byᵉ aᵉ zigzag,ᵉ weᵉ getᵉ aᵉ morphismᵉ
`gᵉ ∘ᵉ fᵉ : Aᵉ → A[1]`ᵉ

```text
          a₀ᵉ        a₁ᵉ
     A₀ᵉ ----->ᵉ A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ ⋯ᵉ
     |        ∧|ᵉ        ∧|ᵉ
  f₀ᵉ |   g₀ᵉ /ᵉ  | f₁ᵉ   /ᵉ  | f₂ᵉ
     |    /ᵉ    |    /ᵉ g₁ᵉ |
     ∨ᵉ  /ᵉ b₀ᵉ   ∨ᵉ  /ᵉ b₁ᵉ   ∨ᵉ
     B₀ᵉ ----->ᵉ B₁ᵉ ----->ᵉ B₂ᵉ ----->ᵉ ⋯ᵉ
     |        ∧|ᵉ        ∧|ᵉ
  g₀ᵉ |   f₁ᵉ /ᵉ  | g₁ᵉ   /ᵉ  | g₂ᵉ
     |    /ᵉ    |    /ᵉ f₂ᵉ |
     ∨ᵉ  /ᵉ      ∨ᵉ  /ᵉ      ∨ᵉ
     A₁ᵉ ----->ᵉ A₂ᵉ ----->ᵉ A₃ᵉ ----->ᵉ ⋯ᵉ .ᵉ
          a₁ᵉ        a₂ᵉ
```

Weᵉ showᵉ thatᵉ thereᵉ isᵉ aᵉ
[homotopy](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ) betweenᵉ
thisᵉ morphismᵉ andᵉ theᵉ
[shiftᵉ inclusionᵉ morphism](synthetic-homotopy-theory.shifts-sequential-diagrams.mdᵉ)
`aᵉ : Aᵉ → A[1]`ᵉ

```text
        a₀ᵉ      a₁ᵉ
    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ
    |       |       |
 a₀ᵉ |       | a₁ᵉ    | a₂ᵉ
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ A₃ᵉ --->ᵉ ⋯ᵉ .ᵉ
        a₁ᵉ      a₂ᵉ
```

**Proof:**ᵉ Component-wiseᵉ theᵉ homotopiesᵉ `aₙᵉ ~ᵉ gₙᵉ ∘ᵉ fₙ`ᵉ areᵉ givenᵉ byᵉ theᵉ upperᵉ
trianglesᵉ in theᵉ zigzag.ᵉ Theᵉ coherenceᵉ ofᵉ aᵉ homotopyᵉ requiresᵉ usᵉ to showᵉ thatᵉ
theᵉ compositionsᵉ

```text
      aₙᵉ
  Aₙᵉ ---->ᵉ Aₙ₊₁ᵉ
            | \ᵉ fₙ₊₁ᵉ
            |   ∨ᵉ
       aₙ₊₁ᵉ |    Bₙ₊₁ᵉ
            |   /ᵉ
            ∨ᵉ ∨ᵉ gₙ₊₁ᵉ
           Aₙ₊₂ᵉ
```

andᵉ

```text
               aₙᵉ
          Aₙᵉ ----->ᵉ Aₙ₊₁ᵉ
        /ᵉ  |        ∧|ᵉ
      /ᵉ fₙᵉ |   gₙᵉ /ᵉ  | fₙ₊₁ᵉ
     |     |    /ᵉ    |
     |     ∨ᵉ  /ᵉ      ∨ᵉ
  aₙᵉ |    Bₙᵉ ----->ᵉ Bₙ₊₁ᵉ
     |     |        ∧|ᵉ
     |  gₙᵉ | fₙ₊₁ᵉ /ᵉ  | gₙ₊₁ᵉ
       \ᵉ   |    /ᵉ    |
         ∨ᵉ ∨ᵉ  /ᵉ      ∨ᵉ
          Aₙ₊₁ᵉ --->ᵉ Aₙ₊₂ᵉ
               aₙ₊₁ᵉ
```

areᵉ homotopic.ᵉ Sinceᵉ theᵉ skewedᵉ squareᵉ

```text
         gₙᵉ
    Bₙᵉ ----->ᵉ Aₙ₊₁ᵉ
     |         |
  gₙᵉ |         | fₙ₊₁ᵉ
     ∨ᵉ         ∨ᵉ
    Aₙ₊₁ᵉ --->ᵉ Bₙ₊₁ᵉ
         fₙ₊₁ᵉ
```

in theᵉ middleᵉ isᵉ composedᵉ ofᵉ inverseᵉ triangles,ᵉ itᵉ isᵉ homotopicᵉ to theᵉ
reflexivityᵉ homotopy,ᵉ whichᵉ makesᵉ theᵉ secondᵉ diagramᵉ collapseᵉ to

```text
           aₙᵉ
        --------ᵉ
      /ᵉ          \ᵉ
    /ᵉ              ∨ᵉ
  Aₙᵉ ---->ᵉ Bₙᵉ ---->ᵉ Aₙ₊₁ᵉ
    \ᵉ fₙᵉ       gₙᵉ  ∧ᵉ |   \ᵉ fₙ₊₁ᵉ
      \ᵉ          /ᵉ   |     ∨ᵉ
        --------ᵉ     | aₙ₊₁ᵉ Bₙ₊₁ᵉ
           aₙᵉ        |     /ᵉ
                     ∨ᵉ   ∨ᵉ gₙ₊₁ᵉ
                    Aₙ₊₂ᵉ ,ᵉ
```

where theᵉ globeᵉ isᵉ againᵉ composedᵉ ofᵉ inverseᵉ triangles,ᵉ soᵉ theᵉ diagramᵉ collapsesᵉ
to

```text
      aₙᵉ
  Aₙᵉ ---->ᵉ Aₙ₊₁ᵉ
            | \ᵉ fₙ₊₁ᵉ
            |   ∨ᵉ
       aₙ₊₁ᵉ |    Bₙ₊₁ᵉ
            |   /ᵉ
            ∨ᵉ ∨ᵉ gₙ₊₁ᵉ
           Aₙ₊₂ᵉ ,ᵉ
```

whichᵉ isᵉ whatᵉ weᵉ neededᵉ to show.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  htpy-hom-shift-hom-zigzag-sequential-diagramᵉ :
    htpy-hom-sequential-diagramᵉ
      ( shift-once-sequential-diagramᵉ Aᵉ)
      ( hom-shift-once-sequential-diagramᵉ Aᵉ)
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ
        ( shift-once-sequential-diagramᵉ Aᵉ)
        ( inv-hom-diagram-zigzag-sequential-diagramᵉ zᵉ)
        ( hom-diagram-zigzag-sequential-diagramᵉ zᵉ))
  pr1ᵉ htpy-hom-shift-hom-zigzag-sequential-diagramᵉ =
    upper-triangle-zigzag-sequential-diagramᵉ zᵉ
  pr2ᵉ htpy-hom-shift-hom-zigzag-sequential-diagramᵉ nᵉ =
    inv-concat-right-homotopy-coherence-square-homotopiesᵉ
      ( ( map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)) ·lᵉ
        ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ))
      ( refl-htpyᵉ)
      ( naturality-comp-hom-sequential-diagramᵉ Aᵉ Bᵉ
        ( shift-once-sequential-diagramᵉ Aᵉ)
        ( inv-hom-diagram-zigzag-sequential-diagramᵉ zᵉ)
        ( hom-diagram-zigzag-sequential-diagramᵉ zᵉ)
        ( nᵉ))
      ( ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( pasting-coherence-squares-collapse-trianglesᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ)
        ( map-zigzag-sequential-diagramᵉ zᵉ nᵉ)
        ( map-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ))
        ( map-sequential-diagramᵉ Bᵉ nᵉ)
        ( inv-map-zigzag-sequential-diagramᵉ zᵉ nᵉ)
        ( inv-map-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ))
        ( map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ))
        ( inv-htpyᵉ (upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ))
        ( lower-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ)
        ( inv-htpyᵉ (lower-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ))
        ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ))
        ( left-inv-htpyᵉ (lower-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ)))
      ( right-whisker-concat-coherence-square-homotopiesᵉ
        ( ( map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)) ·lᵉ
          ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ))
        ( refl-htpyᵉ)
        ( ( map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)) ·lᵉ
          ( inv-htpyᵉ (upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ)))
        ( refl-htpyᵉ)
        ( inv-htpyᵉ
          ( right-inv-htpy-left-whiskerᵉ
            ( map-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ))
            ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ nᵉ)))
        ( ( upper-triangle-zigzag-sequential-diagramᵉ zᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
          ( map-sequential-diagramᵉ Aᵉ nᵉ)))
```

## Properties

### Zigzags of sequential diagrams induce equivalences of sequential colimits

Byᵉ
[functoriality](synthetic-homotopy-theory.functoriality-sequential-colimits.mdᵉ)
ofᵉ sequentialᵉ colimits,ᵉ theᵉ morphismᵉ `fᵉ : Aᵉ → B`ᵉ inducedᵉ byᵉ aᵉ zigzagᵉ thenᵉ
inducesᵉ aᵉ mapᵉ ofᵉ colimitsᵉ `A∞ᵉ → B∞`.ᵉ Weᵉ showᵉ thatᵉ thisᵉ inducedᵉ mapᵉ isᵉ anᵉ
equivalence.ᵉ

**Proof:**ᵉ Givenᵉ aᵉ colimitᵉ `X`ᵉ ofᵉ `(A,ᵉ a)`ᵉ andᵉ aᵉ colimitᵉ `Y`ᵉ ofᵉ `(B,ᵉ b)`,ᵉ weᵉ getᵉ
aᵉ mapᵉ `f∞ᵉ : Xᵉ → Y`.ᵉ Sinceᵉ `X`ᵉ isᵉ alsoᵉ aᵉ colimitᵉ ofᵉ `(A[1],ᵉ a[1])`,ᵉ theᵉ morphismᵉ
`gᵉ : Bᵉ → A[1]`ᵉ inducesᵉ aᵉ mapᵉ `g∞ᵉ : Yᵉ → X`.ᵉ Composingᵉ theᵉ two,ᵉ weᵉ getᵉ
`g∞ᵉ ∘ᵉ f∞ᵉ : Xᵉ → X`.ᵉ Byᵉ functoriality,ᵉ thisᵉ mapᵉ isᵉ homotopicᵉ to `(gᵉ ∘ᵉ f)∞`,ᵉ andᵉ
takingᵉ aᵉ colimitᵉ preservesᵉ homotopies,ᵉ soᵉ `gᵉ ∘ᵉ fᵉ ~ᵉ a`ᵉ impliesᵉ `(gᵉ ∘ᵉ f)∞ᵉ ~ᵉ a∞`.ᵉ
Inᵉ
[`shifts-sequential-diagrams`](synthetic-homotopy-theory.shifts-sequential-diagrams.mdᵉ)
weᵉ showᵉ thatᵉ `a∞ᵉ ~ᵉ id`,ᵉ soᵉ weᵉ getᵉ aᵉ commutingᵉ triangleᵉ

```text
        idᵉ
     Xᵉ --->ᵉ Xᵉ
     |     ∧ᵉ
  f∞ᵉ |   /ᵉ g∞ᵉ
     ∨ᵉ /ᵉ
     Yᵉ .ᵉ
```

Applyingᵉ thisᵉ constructionᵉ to theᵉ half-shiftᵉ ofᵉ theᵉ zigzag,ᵉ weᵉ getᵉ aᵉ commutingᵉ
triangleᵉ

```text
        idᵉ
     Yᵉ --->ᵉ Yᵉ
     |     ∧ᵉ
  g∞ᵉ |   /ᵉ f[1]∞ᵉ
     ∨ᵉ /ᵉ
     Xᵉ .ᵉ
```

Theseᵉ trianglesᵉ composeᵉ to theᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
         idᵉ
     Xᵉ ----->ᵉ Xᵉ
     |       ∧|ᵉ
  f∞ᵉ |  g∞ᵉ /ᵉ  | f[1]∞ᵉ
     |   /ᵉ    |
     ∨ᵉ /ᵉ      ∨ᵉ
     Yᵉ ----->ᵉ Yᵉ .ᵉ
         idᵉ
```

Sinceᵉ theᵉ horizontalᵉ mapsᵉ areᵉ identities,ᵉ weᵉ getᵉ thatᵉ `g∞`ᵉ isᵉ byᵉ definitionᵉ anᵉ
equivalence,ᵉ becauseᵉ weᵉ justᵉ presentedᵉ itsᵉ sectionᵉ `f∞`ᵉ andᵉ itsᵉ retractionᵉ
`f[1]∞`.ᵉ Sinceᵉ `f∞`ᵉ isᵉ aᵉ sectionᵉ ofᵉ anᵉ equivalence,ᵉ itᵉ isᵉ itselfᵉ anᵉ equivalence.ᵉ

Additionallyᵉ weᵉ getᵉ theᵉ judgmentalᵉ equalitiesᵉ `f∞⁻¹ᵉ ≐ᵉ g∞`ᵉ andᵉ `g∞⁻¹ᵉ ≐ᵉ f∞`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  {Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  {Yᵉ : UUᵉ l4ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  (up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-colimit-zigzag-sequential-diagramᵉ : Xᵉ → Yᵉ
  map-colimit-zigzag-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( c'ᵉ)
      ( hom-diagram-zigzag-sequential-diagramᵉ zᵉ)

  inv-map-colimit-zigzag-sequential-diagramᵉ : Yᵉ → Xᵉ
  inv-map-colimit-zigzag-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-c'ᵉ)
      ( shift-once-cocone-sequential-diagramᵉ cᵉ)
      ( inv-hom-diagram-zigzag-sequential-diagramᵉ zᵉ)

  upper-triangle-colimit-zigzag-sequential-diagramᵉ :
    coherence-triangle-mapsᵉ
      ( idᵉ)
      ( inv-map-colimit-zigzag-sequential-diagramᵉ)
      ( map-colimit-zigzag-sequential-diagramᵉ)
  upper-triangle-colimit-zigzag-sequential-diagramᵉ =
    ( inv-htpyᵉ (compute-map-colimit-hom-shift-once-sequential-diagramᵉ up-cᵉ)) ∙hᵉ
    ( htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ up-cᵉ
      ( shift-once-cocone-sequential-diagramᵉ cᵉ)
      ( htpy-hom-shift-hom-zigzag-sequential-diagramᵉ zᵉ)) ∙hᵉ
    ( preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( up-c'ᵉ)
      ( shift-once-cocone-sequential-diagramᵉ cᵉ)
      ( inv-hom-diagram-zigzag-sequential-diagramᵉ zᵉ)
      ( hom-diagram-zigzag-sequential-diagramᵉ zᵉ))

  is-retraction-inv-map-colimit-zigzag-sequential-diagramᵉ :
    is-retractionᵉ
      ( map-colimit-zigzag-sequential-diagramᵉ)
      ( inv-map-colimit-zigzag-sequential-diagramᵉ)
  is-retraction-inv-map-colimit-zigzag-sequential-diagramᵉ =
    inv-htpyᵉ upper-triangle-colimit-zigzag-sequential-diagramᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  {Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  {Yᵉ : UUᵉ l4ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  (up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  (zᵉ : zigzag-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  lower-triangle-colimit-zigzag-sequential-diagramᵉ :
    coherence-triangle-mapsᵉ
      ( idᵉ)
      ( map-colimit-zigzag-sequential-diagramᵉ
        ( up-shift-cocone-sequential-diagramᵉ 1 up-cᵉ)
        ( up-shift-cocone-sequential-diagramᵉ 1 up-c'ᵉ)
        ( shift-zigzag-sequential-diagramᵉ zᵉ))
      ( map-colimit-zigzag-sequential-diagramᵉ up-c'ᵉ
        ( up-shift-cocone-sequential-diagramᵉ 1 up-cᵉ)
        ( half-shift-zigzag-sequential-diagramᵉ zᵉ))
  lower-triangle-colimit-zigzag-sequential-diagramᵉ =
    upper-triangle-colimit-zigzag-sequential-diagramᵉ
      ( up-c'ᵉ)
      ( up-shift-cocone-sequential-diagramᵉ 1 up-cᵉ)
      ( half-shift-zigzag-sequential-diagramᵉ zᵉ)

  is-equiv-inv-map-colimit-zigzag-sequential-diagramᵉ :
    is-equivᵉ (inv-map-colimit-zigzag-sequential-diagramᵉ up-cᵉ up-c'ᵉ zᵉ)
  pr1ᵉ is-equiv-inv-map-colimit-zigzag-sequential-diagramᵉ =
    ( map-colimit-zigzag-sequential-diagramᵉ up-cᵉ up-c'ᵉ zᵉ) ,ᵉ
    ( is-retraction-inv-map-colimit-zigzag-sequential-diagramᵉ up-cᵉ up-c'ᵉ zᵉ)
  pr2ᵉ is-equiv-inv-map-colimit-zigzag-sequential-diagramᵉ =
    ( map-colimit-zigzag-sequential-diagramᵉ
      ( up-shift-cocone-sequential-diagramᵉ 1 up-cᵉ)
      ( up-shift-cocone-sequential-diagramᵉ 1 up-c'ᵉ)
      ( shift-zigzag-sequential-diagramᵉ zᵉ)) ,ᵉ
    ( is-retraction-inv-map-colimit-zigzag-sequential-diagramᵉ
      ( up-c'ᵉ)
      ( up-shift-cocone-sequential-diagramᵉ 1 up-cᵉ)
      ( half-shift-zigzag-sequential-diagramᵉ zᵉ))

  inv-equiv-colimit-zigzag-sequential-diagramᵉ : Yᵉ ≃ᵉ Xᵉ
  pr1ᵉ inv-equiv-colimit-zigzag-sequential-diagramᵉ =
    inv-map-colimit-zigzag-sequential-diagramᵉ up-cᵉ up-c'ᵉ zᵉ
  pr2ᵉ inv-equiv-colimit-zigzag-sequential-diagramᵉ =
    is-equiv-inv-map-colimit-zigzag-sequential-diagramᵉ

  equiv-colimit-zigzag-sequential-diagramᵉ : Xᵉ ≃ᵉ Yᵉ
  pr1ᵉ equiv-colimit-zigzag-sequential-diagramᵉ =
    map-colimit-zigzag-sequential-diagramᵉ up-cᵉ up-c'ᵉ zᵉ
  pr2ᵉ equiv-colimit-zigzag-sequential-diagramᵉ =
    is-equiv-map-inv-equivᵉ inv-equiv-colimit-zigzag-sequential-diagramᵉ
```