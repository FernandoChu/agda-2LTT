# The dependent pullback property of pushouts

```agda
module synthetic-homotopy-theory.dependent-pullback-property-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.constant-type-familiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-sums-pullbacksᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
open import orthogonal-factorization-systems.precomposition-lifts-families-of-elementsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pullback-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ pullbackᵉ property**ᵉ ofᵉ
[pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) assertsᵉ thatᵉ theᵉ typeᵉ ofᵉ
sectionsᵉ ofᵉ aᵉ typeᵉ familyᵉ overᵉ aᵉ pushoutᵉ canᵉ beᵉ expressedᵉ asᵉ aᵉ
[pullback](foundation.pullbacks.md).ᵉ

Theᵉ factᵉ thatᵉ theᵉ dependentᵉ pullbackᵉ propertyᵉ ofᵉ pushoutsᵉ isᵉ
[logicallyᵉ equivalent](foundation.logical-equivalences.mdᵉ) to theᵉ
[dependentᵉ universalᵉ property](synthetic-homotopy-theory.dependent-universal-property-pushouts.mdᵉ)
ofᵉ pushoutsᵉ isᵉ shownᵉ in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).ᵉ

## Definition

```agda
cone-dependent-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
  let iᵉ = pr1ᵉ cᵉ
      jᵉ = pr1ᵉ (pr2ᵉ cᵉ)
      Hᵉ = pr2ᵉ (pr2ᵉ cᵉ)
  in
  coneᵉ
    ( λ (hᵉ : (aᵉ : Aᵉ) → Pᵉ (iᵉ aᵉ)) → λ (sᵉ : Sᵉ) → trᵉ Pᵉ (Hᵉ sᵉ) (hᵉ (fᵉ sᵉ)))
    ( λ (hᵉ : (bᵉ : Bᵉ) → Pᵉ (jᵉ bᵉ)) → λ sᵉ → hᵉ (gᵉ sᵉ))
    ( (xᵉ : Xᵉ) → Pᵉ xᵉ)
pr1ᵉ (cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) Pᵉ) hᵉ aᵉ =
  hᵉ (iᵉ aᵉ)
pr1ᵉ (pr2ᵉ (cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) Pᵉ)) hᵉ bᵉ =
  hᵉ (jᵉ bᵉ)
pr2ᵉ (pr2ᵉ (cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) Pᵉ)) hᵉ =
  eq-htpyᵉ (λ sᵉ → apdᵉ hᵉ (Hᵉ sᵉ))

dependent-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  UUωᵉ
dependent-pullback-property-pushoutᵉ {Sᵉ = Sᵉ} {Aᵉ} {Bᵉ} fᵉ gᵉ {Xᵉ} (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) =
  {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
  is-pullbackᵉ
    ( λ (hᵉ : (aᵉ : Aᵉ) → Pᵉ (iᵉ aᵉ)) → λ sᵉ → trᵉ Pᵉ (Hᵉ sᵉ) (hᵉ (fᵉ sᵉ)))
    ( λ (hᵉ : (bᵉ : Bᵉ) → Pᵉ (jᵉ bᵉ)) → λ sᵉ → hᵉ (gᵉ sᵉ))
    ( cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) Pᵉ)
```

## Properties

### The dependent pullback property is logically equivalent to the pullback property

Considerᵉ aᵉ [cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ)

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ  .ᵉ
        iᵉ
```

Theᵉ nondependentᵉ pullbackᵉ propertyᵉ followsᵉ fromᵉ theᵉ dependentᵉ oneᵉ byᵉ applyingᵉ
theᵉ dependentᵉ pullbackᵉ propertyᵉ to theᵉ constantᵉ typeᵉ familyᵉ `λᵉ _ → Y`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  pullback-property-dependent-pullback-property-pushoutᵉ :
    dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ →
    pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
  pullback-property-dependent-pullback-property-pushoutᵉ dpp-cᵉ Yᵉ =
    is-pullback-htpyᵉ
      ( λ hᵉ →
        eq-htpyᵉ
          ( λ sᵉ →
            invᵉ
              ( tr-constant-type-familyᵉ
                ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
                ( hᵉ (fᵉ sᵉ)))))
      ( refl-htpyᵉ)
      ( cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ (λ _ → Yᵉ))
      ( ( refl-htpyᵉ) ,ᵉ
        ( refl-htpyᵉ) ,ᵉ
        ( λ hᵉ →
          ( right-unitᵉ) ∙ᵉ
          ( apᵉ
            ( eq-htpyᵉ)
            ( eq-htpyᵉ
              ( λ sᵉ →
                left-transpose-eq-concatᵉ _ _ _
                  ( invᵉ
                    ( apd-constant-type-familyᵉ hᵉ
                      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ))))) ∙ᵉ
          ( eq-htpy-concat-htpyᵉ _ _))))
      ( dpp-cᵉ (λ _ → Yᵉ))
```

Inᵉ theᵉ converseᵉ direction,ᵉ weᵉ useᵉ theᵉ factᵉ thatᵉ byᵉ theᵉ
[typeᵉ theoreticᵉ principleᵉ ofᵉ choice](foundation.type-theoretic-principle-of-choice.md),ᵉ
dependentᵉ functionsᵉ distributeᵉ overᵉ Σ-types.ᵉ That,ᵉ andᵉ aᵉ handfulᵉ ofᵉ technicalᵉ
lemmasᵉ aboutᵉ [transport](foundation.transport-along-identifications.mdᵉ) in
[precomposedᵉ typeᵉ families](foundation.precomposition-type-families.mdᵉ) andᵉ
[precomposition](orthogonal-factorization-systems.precomposition-lifts-families-of-elements.mdᵉ)
in
[liftsᵉ ofᵉ familiesᵉ ofᵉ elements](orthogonal-factorization-systems.lifts-families-of-elements.md),ᵉ
allowᵉ usᵉ to constructᵉ theᵉ followingᵉ
[commutingᵉ cube](foundation.commuting-cubes-of-maps.mdᵉ):

```text
                                Σᵉ (hᵉ : Xᵉ → Xᵉ) ((xᵉ : Xᵉ) → Pᵉ (hᵉ xᵉ))
                                       /ᵉ        |        \ᵉ
                                     /ᵉ          |          \ᵉ
                                   /ᵉ            |            \ᵉ
                                 /ᵉ              |              \ᵉ
                               /ᵉ                |                \ᵉ
                             /ᵉ                  |                  \ᵉ
                           /ᵉ                    |                    \ᵉ
                         ∨ᵉ                      ∨ᵉ                      ∨ᵉ
  Σᵉ (hᵉ : Aᵉ → Xᵉ) ((aᵉ : Aᵉ) → Pᵉ (hᵉ aᵉ))    Xᵉ → Σᵉ (xᵉ : Xᵉ) (Pᵉ xᵉ)    Σᵉ (hᵉ : Bᵉ → Xᵉ) ((bᵉ : Bᵉ) → Pᵉ (hᵉ bᵉ))
                         |\ᵉ             /ᵉ               \ᵉ             /|ᵉ
                         |  \ᵉ         /ᵉ                   \ᵉ         /ᵉ  |
                         |    \ᵉ     /ᵉ                       \ᵉ     /ᵉ    |
                         |      \ᵉ /ᵉ                           \ᵉ /ᵉ      |
                         |      /ᵉ \ᵉ                           /ᵉ \ᵉ      |
                         |    /ᵉ     \ᵉ                       /ᵉ     \ᵉ    |
                         |  /ᵉ         \ᵉ                   /ᵉ         \ᵉ  |
                         ∨∨ᵉ             ∨ᵉ               ∨ᵉ             ∨∨ᵉ
         Aᵉ → Σᵉ (xᵉ : Xᵉ) (Pᵉ xᵉ)    Σᵉ (hᵉ : Sᵉ → Xᵉ) ((sᵉ : Sᵉ) → Pᵉ (hᵉ sᵉ))    Bᵉ → Σᵉ (xᵉ : Xᵉ) (Pᵉ xᵉ)
                           \ᵉ                    |                    /ᵉ
                             \ᵉ                  |                  /ᵉ
                               \ᵉ                |                /ᵉ
                                 \ᵉ              |              /ᵉ
                                   \ᵉ            |            /ᵉ
                                     \ᵉ          |          /ᵉ
                                       \ᵉ        |        /ᵉ
                                         ∨ᵉ      ∨ᵉ      ∨ᵉ
                                       Sᵉ → Σᵉ (xᵉ : Xᵉ) (Pᵉ xᵉ) .ᵉ
```

Theᵉ bottomᵉ squareᵉ isᵉ theᵉ inducedᵉ precompositionᵉ squareᵉ forᵉ ourᵉ fixedᵉ cocone,ᵉ soᵉ
byᵉ theᵉ assumedᵉ pullbackᵉ property,ᵉ instantiatedᵉ atᵉ theᵉ typeᵉ `Σᵉ (xᵉ : Xᵉ) (Pᵉ x)`,ᵉ
it'sᵉ aᵉ pullback.ᵉ Theᵉ topᵉ squareᵉ isᵉ constructedᵉ byᵉ precompositionᵉ ofᵉ mapsᵉ onᵉ theᵉ
firstᵉ component,ᵉ andᵉ byᵉ precompositionᵉ ofᵉ liftsᵉ ofᵉ familiesᵉ ofᵉ elementsᵉ onᵉ theᵉ
secondᵉ component.ᵉ Sinceᵉ verticalᵉ mapsᵉ areᵉ equivalences,ᵉ byᵉ theᵉ principleᵉ ofᵉ
choice,ᵉ andᵉ theᵉ bottomᵉ squareᵉ isᵉ aᵉ pullback,ᵉ weᵉ concludeᵉ thatᵉ theᵉ topᵉ squareᵉ isᵉ
aᵉ pullback.ᵉ

Observeᵉ thatᵉ restrictingᵉ theᵉ topᵉ squareᵉ to itsᵉ firstᵉ component,ᵉ weᵉ againᵉ getᵉ theᵉ
inducedᵉ precompositionᵉ square,ᵉ thisᵉ timeᵉ instantiatedᵉ atᵉ `X`,ᵉ soᵉ thatᵉ isᵉ alsoᵉ aᵉ
pullback.ᵉ Henceᵉ theᵉ topᵉ squareᵉ isᵉ aᵉ pullbackᵉ ofᵉ totalᵉ spacesᵉ overᵉ aᵉ pullbackᵉ
square,ᵉ whichᵉ impliesᵉ thatᵉ weᵉ getᵉ aᵉ familyᵉ ofᵉ pullbackᵉ squaresᵉ ofᵉ theᵉ fibers,ᵉ
i.e.ᵉ forᵉ everyᵉ `hᵉ : Xᵉ → X`ᵉ weᵉ haveᵉ aᵉ pullbackᵉ

```text
    (xᵉ : Xᵉ) → Pᵉ (hᵉ xᵉ) --------->ᵉ (bᵉ : Bᵉ) → Pᵉ (hᵉ (jᵉ bᵉ))
            | ⌟ᵉ                           |
            |                             |
            |                             |
            |                             |
            ∨ᵉ                             ∨ᵉ
  (aᵉ : Aᵉ) → Pᵉ (hᵉ (iᵉ aᵉ)) ----->ᵉ (sᵉ : Sᵉ) → Pᵉ (hᵉ (jᵉ (gᵉ sᵉ))) ,ᵉ
```

andᵉ instantiatingᵉ forᵉ `idᵉ : Xᵉ → X`ᵉ givesᵉ usᵉ exactlyᵉ aᵉ proofᵉ ofᵉ theᵉ dependentᵉ
pullbackᵉ property.ᵉ

```agda
  cone-family-dependent-pullback-propertyᵉ :
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
    cone-familyᵉ
      ( lift-family-of-elementsᵉ Pᵉ)
      ( precomp-lift-family-of-elementsᵉ Pᵉ fᵉ)
      ( precomp-lift-family-of-elementsᵉ Pᵉ gᵉ)
      ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Xᵉ)
      ( lift-family-of-elementsᵉ Pᵉ)
  pr1ᵉ (cone-family-dependent-pullback-propertyᵉ Pᵉ γᵉ) hᵉ =
    hᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ
  pr1ᵉ (pr2ᵉ (cone-family-dependent-pullback-propertyᵉ Pᵉ γᵉ)) hᵉ =
    hᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ
  pr2ᵉ (pr2ᵉ (cone-family-dependent-pullback-propertyᵉ Pᵉ γᵉ)) =
    triangle-precomp-lift-family-of-elements-htpyᵉ Pᵉ γᵉ
      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)

  is-pullback-cone-family-dependent-pullback-familyᵉ :
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
    pullback-property-pushoutᵉ fᵉ gᵉ cᵉ →
    (γᵉ : Xᵉ → Xᵉ) →
    is-pullbackᵉ
      ( ( trᵉ
          ( lift-family-of-elementsᵉ Pᵉ)
          ( htpy-precompᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ) Xᵉ γᵉ)) ∘ᵉ
        ( precomp-lift-family-of-elementsᵉ Pᵉ fᵉ
          ( γᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)))
      ( precomp-lift-family-of-elementsᵉ Pᵉ gᵉ
        ( γᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
      ( cone-family-dependent-pullback-propertyᵉ Pᵉ γᵉ)
  is-pullback-cone-family-dependent-pullback-familyᵉ Pᵉ pp-cᵉ =
    is-pullback-family-is-pullback-totᵉ
      ( lift-family-of-elementsᵉ Pᵉ)
      ( precomp-lift-family-of-elementsᵉ Pᵉ fᵉ)
      ( precomp-lift-family-of-elementsᵉ Pᵉ gᵉ)
      ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Xᵉ)
      ( cone-family-dependent-pullback-propertyᵉ Pᵉ)
      ( pp-cᵉ Xᵉ)
      ( is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
        ( precompᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) (Σᵉ Xᵉ Pᵉ))
        ( precompᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) (Σᵉ Xᵉ Pᵉ))
        ( precompᵉ fᵉ (Σᵉ Xᵉ Pᵉ))
        ( precompᵉ gᵉ (Σᵉ Xᵉ Pᵉ))
        ( precomp-lifted-family-of-elementsᵉ Pᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
        ( precomp-lifted-family-of-elementsᵉ Pᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
        ( precomp-lifted-family-of-elementsᵉ Pᵉ fᵉ)
        ( precomp-lifted-family-of-elementsᵉ Pᵉ gᵉ)
        ( map-inv-distributive-Π-Σᵉ)
        ( map-inv-distributive-Π-Σᵉ)
        ( map-inv-distributive-Π-Σᵉ)
        ( map-inv-distributive-Π-Σᵉ)
        ( htpy-precomp-lifted-family-of-elementsᵉ Pᵉ
          ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)
        ( htpy-precompᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ) (Σᵉ Xᵉ Pᵉ))
        ( coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σᵉ
          ( Pᵉ)
          ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ))
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( is-equiv-map-inv-distributive-Π-Σᵉ)
        ( pp-cᵉ (Σᵉ Xᵉ Pᵉ)))

  dependent-pullback-property-pullback-property-pushoutᵉ :
    pullback-property-pushoutᵉ fᵉ gᵉ cᵉ →
    dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
  dependent-pullback-property-pullback-property-pushoutᵉ pp-cᵉ Pᵉ =
    is-pullback-htpy'ᵉ
      ( ( tr-lift-family-of-elements-precompᵉ Pᵉ idᵉ
          ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)) ·rᵉ
        ( precomp-lift-family-of-elementsᵉ Pᵉ fᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)))
      ( refl-htpyᵉ)
      ( cone-family-dependent-pullback-propertyᵉ Pᵉ idᵉ)
      { c'ᵉ = cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ}
      ( ( refl-htpyᵉ) ,ᵉ
        ( refl-htpyᵉ) ,ᵉ
        ( ( right-unit-htpyᵉ) ∙hᵉ
          ( coherence-triangle-precomp-lift-family-of-elementsᵉ Pᵉ idᵉ
            ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ))))
      ( is-pullback-cone-family-dependent-pullback-familyᵉ Pᵉ pp-cᵉ idᵉ)
```