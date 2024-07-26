# Precomposition of lifts of families of elements by maps

```agda
module orthogonal-factorization-systems.precomposition-lifts-families-of-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ familyᵉ `Bᵉ : Aᵉ → 𝓤`ᵉ andᵉ aᵉ mapᵉ `aᵉ : Iᵉ → A`.ᵉ Then,ᵉ givenᵉ aᵉ mapᵉ
`fᵉ : Jᵉ → I`,ᵉ weᵉ mayᵉ pullᵉ backᵉ aᵉ
[lift](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ) ofᵉ `a`ᵉ to
aᵉ liftᵉ ofᵉ `aᵉ ∘ᵉ f`.ᵉ

Inᵉ otherᵉ words,ᵉ givenᵉ aᵉ diagramᵉ

```text
                Σᵉ (xᵉ : Aᵉ) (Bᵉ xᵉ)
                      |
                      | pr1ᵉ
                      |
                      ∨ᵉ
  Jᵉ ------>ᵉ Iᵉ ------>ᵉ Aᵉ         ,ᵉ
       fᵉ         aᵉ
```

weᵉ getᵉ aᵉ mapᵉ ofᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ

```text
  ((iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ)) → ((jᵉ : Jᵉ) → Bᵉ (aᵉ (fᵉ jᵉ))) .ᵉ
```

Thisᵉ mapᵉ ofᵉ liftsᵉ inducesᵉ aᵉ mapᵉ fromᵉ liftedᵉ familiesᵉ ofᵉ elementsᵉ indexedᵉ byᵉ `I`ᵉ
to liftedᵉ familiesᵉ ofᵉ elementsᵉ indexedᵉ byᵉ `J`.ᵉ

## Definitions

### Precomposition of lifts of families of elements by functions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) {Jᵉ : UUᵉ l4ᵉ}
  (fᵉ : Jᵉ → Iᵉ)
  where

  precomp-lift-family-of-elementsᵉ :
    (aᵉ : Iᵉ → Aᵉ) →
    lift-family-of-elementsᵉ Bᵉ aᵉ → lift-family-of-elementsᵉ Bᵉ (aᵉ ∘ᵉ fᵉ)
  precomp-lift-family-of-elementsᵉ aᵉ bᵉ iᵉ = bᵉ (fᵉ iᵉ)
```

### Precomposition in lifted families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) {Jᵉ : UUᵉ l4ᵉ}
  (fᵉ : Jᵉ → Iᵉ)
  where

  precomp-lifted-family-of-elementsᵉ :
    lifted-family-of-elementsᵉ Iᵉ Bᵉ → lifted-family-of-elementsᵉ Jᵉ Bᵉ
  precomp-lifted-family-of-elementsᵉ =
    map-Σᵉ
      ( lift-family-of-elementsᵉ Bᵉ)
      ( precompᵉ fᵉ Aᵉ)
      ( precomp-lift-family-of-elementsᵉ Bᵉ fᵉ)
```

## Properties

### Homotopies between maps induce commuting triangles of precompositions of lifts of families of elements

Considerᵉ twoᵉ mapsᵉ `f,ᵉ gᵉ : Jᵉ → I`ᵉ andᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ betweenᵉ them.ᵉ Theᵉ
precompositionᵉ functionsᵉ theyᵉ induceᵉ onᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ haveᵉ
differentᵉ codomains,ᵉ namelyᵉ `lift-family-of-elementsᵉ Bᵉ (aᵉ ∘ᵉ f)`ᵉ andᵉ
`lift-family-of-elementsᵉ Bᵉ (aᵉ ∘ᵉ g)`,ᵉ butᵉ theyᵉ fitᵉ intoᵉ aᵉ
[commutingᵉ triangle](foundation.commuting-triangles-of-maps.mdᵉ) with
[transport](foundation.transport-along-identifications.mdᵉ) in theᵉ typeᵉ ofᵉ liftsᵉ:

```text
                              precomp-liftᵉ Bᵉ fᵉ aᵉ
  lift-family-of-elementsᵉ Bᵉ aᵉ ------------------>ᵉ lift-family-of-elementsᵉ Bᵉ (aᵉ ∘ᵉ fᵉ)
                      \ᵉ                                /ᵉ
                         \ᵉ                          /ᵉ
                            \ᵉ                    /ᵉ
           precomp-liftᵉ Bᵉ gᵉ aᵉ  \ᵉ              /ᵉ trᵉ (lift-family-of-elementsᵉ Bᵉ) (htpy-precompᵉ Hᵉ Aᵉ aᵉ)
                                  \ᵉ        /ᵉ
                                     ∨ᵉ  ∨ᵉ
                       lift-family-of-elementsᵉ Bᵉ (aᵉ ∘ᵉ gᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) (aᵉ : Iᵉ → Aᵉ)
  {Jᵉ : UUᵉ l4ᵉ} {fᵉ : Jᵉ → Iᵉ}
  where

  statement-triangle-precomp-lift-family-of-elements-htpyᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  statement-triangle-precomp-lift-family-of-elements-htpyᵉ {gᵉ} Hᵉ =
    coherence-triangle-maps'ᵉ
      ( precomp-lift-family-of-elementsᵉ Bᵉ gᵉ aᵉ)
      ( trᵉ (lift-family-of-elementsᵉ Bᵉ) (htpy-precompᵉ Hᵉ Aᵉ aᵉ))
      ( precomp-lift-family-of-elementsᵉ Bᵉ fᵉ aᵉ)

  triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ :
    statement-triangle-precomp-lift-family-of-elements-htpyᵉ refl-htpyᵉ
  triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ bᵉ =
    tr-lift-family-of-elements-precompᵉ Bᵉ aᵉ refl-htpyᵉ (bᵉ ∘ᵉ fᵉ)

  abstract
    triangle-precomp-lift-family-of-elements-htpyᵉ :
      {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
      statement-triangle-precomp-lift-family-of-elements-htpyᵉ Hᵉ
    triangle-precomp-lift-family-of-elements-htpyᵉ =
      ind-htpyᵉ fᵉ
        ( λ gᵉ → statement-triangle-precomp-lift-family-of-elements-htpyᵉ)
        ( triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ)

    compute-triangle-precomp-lift-family-of-elements-htpyᵉ :
      triangle-precomp-lift-family-of-elements-htpyᵉ refl-htpyᵉ ＝ᵉ
      triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ
    compute-triangle-precomp-lift-family-of-elements-htpyᵉ =
      compute-ind-htpyᵉ fᵉ
        ( λ gᵉ → statement-triangle-precomp-lift-family-of-elements-htpyᵉ)
        ( triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ)
```

### `triangle-precomp-lift-family-of-elements-htpy` factors through transport along a homotopy in the famiy `B ∘ a`

Insteadᵉ ofᵉ definingᵉ theᵉ homotopyᵉ `triangle-precomp-lift-family-of-elements-htpy`ᵉ
byᵉ homotopyᵉ induction,ᵉ weᵉ couldᵉ haveᵉ definedᵉ itᵉ manuallyᵉ using theᵉ
characterizationᵉ ofᵉ transportᵉ in theᵉ typeᵉ ofᵉ liftsᵉ ofᵉ aᵉ familyᵉ ofᵉ elements.ᵉ

Weᵉ showᵉ thatᵉ theseᵉ twoᵉ definitionsᵉ areᵉ homotopic.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) (aᵉ : Iᵉ → Aᵉ)
  {Jᵉ : UUᵉ l4ᵉ} {fᵉ : Jᵉ → Iᵉ}
  where

  statement-coherence-triangle-precomp-lift-family-of-elementsᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  statement-coherence-triangle-precomp-lift-family-of-elementsᵉ Hᵉ =
    ( triangle-precomp-lift-family-of-elements-htpyᵉ Bᵉ aᵉ Hᵉ) ~ᵉ
    ( ( ( tr-lift-family-of-elements-precompᵉ Bᵉ aᵉ Hᵉ) ·rᵉ
        ( precomp-lift-family-of-elementsᵉ Bᵉ fᵉ aᵉ)) ∙hᵉ
      ( λ bᵉ → eq-htpyᵉ (λ jᵉ → apdᵉ bᵉ (Hᵉ jᵉ))))

  coherence-triangle-precomp-lift-family-of-elements-refl-htpyᵉ :
    statement-coherence-triangle-precomp-lift-family-of-elementsᵉ
      ( refl-htpyᵉ)
  coherence-triangle-precomp-lift-family-of-elements-refl-htpyᵉ bᵉ =
    ( htpy-eqᵉ (compute-triangle-precomp-lift-family-of-elements-htpyᵉ Bᵉ aᵉ) bᵉ) ∙ᵉ
    ( invᵉ right-unitᵉ) ∙ᵉ
    ( left-whisker-concatᵉ
      ( triangle-precomp-lift-family-of-elements-htpy-refl-htpyᵉ Bᵉ aᵉ bᵉ)
      ( invᵉ (eq-htpy-refl-htpyᵉ (bᵉ ∘ᵉ fᵉ))))

  abstract
    coherence-triangle-precomp-lift-family-of-elementsᵉ :
      {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
      statement-coherence-triangle-precomp-lift-family-of-elementsᵉ Hᵉ
    coherence-triangle-precomp-lift-family-of-elementsᵉ =
      ind-htpyᵉ fᵉ
        ( λ gᵉ →
          statement-coherence-triangle-precomp-lift-family-of-elementsᵉ)
        ( coherence-triangle-precomp-lift-family-of-elements-refl-htpyᵉ)

    compute-coherence-triangle-precomp-lift-family-of-elementsᵉ :
      coherence-triangle-precomp-lift-family-of-elementsᵉ refl-htpyᵉ ＝ᵉ
      coherence-triangle-precomp-lift-family-of-elements-refl-htpyᵉ
    compute-coherence-triangle-precomp-lift-family-of-elementsᵉ =
      compute-ind-htpyᵉ fᵉ
        ( λ gᵉ →
          statement-coherence-triangle-precomp-lift-family-of-elementsᵉ)
        ( coherence-triangle-precomp-lift-family-of-elements-refl-htpyᵉ)
```

### `precomp-lifted-family-of-elements` is homotopic to the precomposition map on functions up to equivalence

Weᵉ haveᵉ aᵉ [commutingᵉ square](foundation.commuting-squares-of-maps.mdᵉ) likeᵉ thisᵉ:

```text
                                     precomp-lifted-familyᵉ fᵉ
  Σᵉ (aᵉ : Iᵉ → Aᵉ) ((iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ)) ------------------------>ᵉ Σᵉ (aᵉ : Jᵉ → Aᵉ) ((jᵉ : Jᵉ) → Bᵉ (aᵉ jᵉ))
                  |                                                           |
                  |                                                           |
                  | map-inv-distributive-Π-Σᵉ    ⇗ᵉ    map-inv-distributive-Π-Σᵉ |
                  |                                                           |
                  ∨ᵉ                                                           ∨ᵉ
              Iᵉ → Σᵉ Aᵉ Bᵉ ------------------------------------------------>ᵉ Jᵉ → Σᵉ Aᵉ Bᵉ ,ᵉ
                                               -ᵉ ∘ᵉ fᵉ
```

whichᵉ showsᵉ thatᵉ `precomp-lifted-family-of-elementsᵉ f`ᵉ isᵉ aᵉ goodᵉ choiceᵉ forᵉ aᵉ
precompositionᵉ mapᵉ in theᵉ typeᵉ ofᵉ liftedᵉ familiesᵉ ofᵉ elements,ᵉ sinceᵉ it'sᵉ
homotopicᵉ to theᵉ regularᵉ precompositionᵉ mapᵉ upᵉ to equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) {Jᵉ : UUᵉ l4ᵉ}
  (fᵉ : Jᵉ → Iᵉ)
  where

  coherence-square-precomp-map-inv-distributive-Π-Σᵉ :
    coherence-square-mapsᵉ
      ( precomp-lifted-family-of-elementsᵉ Bᵉ fᵉ)
      ( map-inv-distributive-Π-Σᵉ)
      ( map-inv-distributive-Π-Σᵉ)
      ( precompᵉ fᵉ (Σᵉ Aᵉ Bᵉ))
  coherence-square-precomp-map-inv-distributive-Π-Σᵉ = refl-htpyᵉ
```

### Precomposition of lifted families of elements preserves homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) {Jᵉ : UUᵉ l4ᵉ}
  {fᵉ : Jᵉ → Iᵉ}
  where

  htpy-precomp-lifted-family-of-elementsᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
    ( precomp-lifted-family-of-elementsᵉ Bᵉ fᵉ) ~ᵉ
    ( precomp-lifted-family-of-elementsᵉ Bᵉ gᵉ)
  htpy-precomp-lifted-family-of-elementsᵉ Hᵉ =
    htpy-map-Σᵉ
      ( lift-family-of-elementsᵉ Bᵉ)
      ( htpy-precompᵉ Hᵉ Aᵉ)
      ( precomp-lift-family-of-elementsᵉ Bᵉ fᵉ)
      ( λ aᵉ → triangle-precomp-lift-family-of-elements-htpyᵉ Bᵉ aᵉ Hᵉ)

  abstract
    compute-htpy-precomp-lifted-family-of-elementsᵉ :
      htpy-precomp-lifted-family-of-elementsᵉ refl-htpyᵉ ~ᵉ
      refl-htpyᵉ
    compute-htpy-precomp-lifted-family-of-elementsᵉ =
      htpy-htpy-map-Σ-refl-htpyᵉ
        ( lift-family-of-elementsᵉ Bᵉ)
        ( compute-htpy-precomp-refl-htpyᵉ fᵉ Aᵉ)
        ( λ aᵉ →
          ( htpy-eqᵉ
            ( compute-triangle-precomp-lift-family-of-elements-htpyᵉ Bᵉ aᵉ)) ∙hᵉ
          ( λ bᵉ →
            htpy-eqᵉ (compute-tr-lift-family-of-elements-precompᵉ Bᵉ aᵉ) (bᵉ ∘ᵉ fᵉ)))
```

### `coherence-square-precomp-map-inv-distributive-Π-Σ` commutes with induced homotopies between precompositions maps

Diagrammatically,ᵉ weᵉ haveᵉ twoᵉ waysᵉ ofᵉ composingᵉ homotopiesᵉ to connectᵉ `-ᵉ ∘ᵉ f`ᵉ
andᵉ `precomp-lifted-family-of-elementsᵉ g`.ᵉ Oneᵉ factorsᵉ throughᵉ
`precomp-lifted-family-of-elementsᵉ f`ᵉ:

```text
                                     precomp-lifted-familyᵉ gᵉ
                               -----------------------------------ᵉ
                             /ᵉ                                     \ᵉ
                           /ᵉ     ⇗ᵉ htpy-precomp-lifted-familyᵉ Hᵉ      \ᵉ
                         /ᵉ                                             ∨ᵉ
  Σᵉ (aᵉ : Iᵉ → Aᵉ) ((iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ)) ------------------------>ᵉ Σᵉ (aᵉ : Jᵉ → Aᵉ) ((jᵉ : Jᵉ) → Bᵉ (aᵉ jᵉ))
                  |                  precomp-lifted-familyᵉ fᵉ                  |
                  |                                                           |
                  |                             ⇗ᵉ                             |
                  | map-inv-distributive-Π-Σᵉ         map-inv-distributive-Π-Σᵉ |
                  ∨ᵉ                                                           ∨ᵉ
              Iᵉ → Σᵉ Aᵉ Bᵉ ------------------------------------------------>ᵉ Jᵉ → Σᵉ Aᵉ Bᵉ ,ᵉ
                                              -ᵉ ∘ᵉ fᵉ
```

whileᵉ theᵉ otherᵉ factorsᵉ throughᵉ `-ᵉ ∘ᵉ g`ᵉ:

```text
                                     precomp-lifted-familyᵉ gᵉ
  Σᵉ (aᵉ : Iᵉ → Aᵉ) ((iᵉ : Iᵉ) → Bᵉ (aᵉ iᵉ)) ------------------------>ᵉ Σᵉ (aᵉ : Jᵉ → Aᵉ) ((jᵉ : Jᵉ) → Bᵉ (aᵉ jᵉ))
                  |                                                           |
                  |                                                           |
                  | map-inv-distributive-Π-Σᵉ    ⇗ᵉ    map-inv-distributive-Π-Σᵉ |
                  |                                                           |
                  ∨ᵉ                           -ᵉ ∘ᵉ gᵉ                           ∨ᵉ
              Iᵉ → Σᵉ Aᵉ Bᵉ ------------------------------------------------>ᵉ Jᵉ → Σᵉ Aᵉ Bᵉ .ᵉ
                        \ᵉ                                               >ᵉ
                          \ᵉ             ⇗ᵉ  htpy-precompᵉ Hᵉ             /ᵉ
                            \ᵉ                                       /ᵉ
                              -------------------------------------ᵉ
                                              -ᵉ ∘ᵉ fᵉ
```

Weᵉ showᵉ thatᵉ theseᵉ homotopiesᵉ areᵉ themselvesᵉ homotopic,ᵉ fillingᵉ theᵉ cylinder.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ) {Jᵉ : UUᵉ l4ᵉ}
  {fᵉ : Jᵉ → Iᵉ}
  where

  statement-coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  statement-coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ
    {gᵉ} Hᵉ =
    coherence-square-homotopiesᵉ
      ( htpy-precompᵉ Hᵉ (Σᵉ Aᵉ Bᵉ) ·rᵉ map-inv-distributive-Π-Σᵉ)
      ( coherence-square-precomp-map-inv-distributive-Π-Σᵉ Bᵉ fᵉ)
      ( coherence-square-precomp-map-inv-distributive-Π-Σᵉ Bᵉ gᵉ)
      ( ( map-inv-distributive-Π-Σᵉ) ·lᵉ
        ( htpy-precomp-lifted-family-of-elementsᵉ Bᵉ Hᵉ))

  coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σ-refl-htpyᵉ :
    statement-coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ
      ( refl-htpyᵉ)
  coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σ-refl-htpyᵉ =
    ( left-whisker-comp²ᵉ
      ( map-inv-distributive-Π-Σᵉ)
      ( compute-htpy-precomp-lifted-family-of-elementsᵉ Bᵉ)) ∙hᵉ
    ( inv-htpyᵉ
      ( λ hᵉ →
        compute-htpy-precomp-refl-htpyᵉ fᵉ
          ( Σᵉ Aᵉ Bᵉ)
          ( map-inv-distributive-Π-Σᵉ hᵉ))) ∙hᵉ
    ( inv-htpy-right-unit-htpyᵉ)

  coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ :
    {gᵉ : Jᵉ → Iᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
    statement-coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ
      ( Hᵉ)
  coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ =
    ind-htpyᵉ fᵉ
      ( λ gᵉ →
        statement-coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ)
      ( coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σ-refl-htpyᵉ)
```