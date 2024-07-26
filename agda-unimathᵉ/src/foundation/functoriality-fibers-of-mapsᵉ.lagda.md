# Functoriality of fibers of maps

```agda
module foundation.functoriality-fibers-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Anyᵉ [morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ fromᵉ `f`ᵉ
to `g`ᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

inducesᵉ aᵉ morphismᵉ ofᵉ arrowsᵉ betweenᵉ theᵉ
[fiberᵉ inclusions](foundation-core.fibers-of-maps.mdᵉ) ofᵉ `f`ᵉ andᵉ `g`,ᵉ i.e.,ᵉ aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
  fiberᵉ fᵉ bᵉ ----->ᵉ fiberᵉ gᵉ (jᵉ bᵉ)
      |                  |
      |                  |
      ∨ᵉ                  ∨ᵉ
      Aᵉ --------------->ᵉ X.ᵉ
```

Thisᵉ operationᵉ fromᵉ morphismsᵉ ofᵉ arrowsᵉ fromᵉ `f`ᵉ to `g`ᵉ to morphismsᵉ ofᵉ arrowsᵉ
betweenᵉ theirᵉ fiberᵉ inclusionsᵉ isᵉ theᵉ **functorialᵉ actionᵉ ofᵉ fibers**.ᵉ Theᵉ
functorialᵉ actionᵉ obeysᵉ theᵉ functorᵉ laws,ᵉ i.e.,ᵉ itᵉ preservesᵉ identityᵉ morphismsᵉ
andᵉ composition.ᵉ

## Definitions

### Any commuting square induces a family of maps between the fibers of the vertical maps

Ourᵉ definitionᵉ ofᵉ `map-domain-hom-arrow-fiber`ᵉ isᵉ givenᵉ in suchᵉ aᵉ wayᵉ thatᵉ itᵉ
alwaysᵉ computesᵉ nicely.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ) (bᵉ : Bᵉ)
  where

  map-domain-hom-arrow-fiberᵉ :
    fiberᵉ fᵉ bᵉ → fiberᵉ gᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ)
  map-domain-hom-arrow-fiberᵉ =
    map-Σᵉ _
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( λ aᵉ pᵉ →
        invᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) ∙ᵉ apᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) pᵉ)

  map-fiberᵉ :
    fiberᵉ fᵉ bᵉ → fiberᵉ gᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ)
  map-fiberᵉ = map-domain-hom-arrow-fiberᵉ

  map-codomain-hom-arrow-fiberᵉ : Aᵉ → Xᵉ
  map-codomain-hom-arrow-fiberᵉ = map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ

  coh-hom-arrow-fiberᵉ :
    coherence-square-mapsᵉ
      ( map-domain-hom-arrow-fiberᵉ)
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ gᵉ)
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  coh-hom-arrow-fiberᵉ = refl-htpyᵉ

  hom-arrow-fiberᵉ :
    hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ {bᵉ})
      ( inclusion-fiberᵉ gᵉ {map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ})
  pr1ᵉ hom-arrow-fiberᵉ = map-domain-hom-arrow-fiberᵉ
  pr1ᵉ (pr2ᵉ hom-arrow-fiberᵉ) = map-codomain-hom-arrow-fiberᵉ
  pr2ᵉ (pr2ᵉ hom-arrow-fiberᵉ) = coh-hom-arrow-fiberᵉ
```

### Any cone induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) (aᵉ : Aᵉ)
  where

  map-fiber-vertical-map-coneᵉ :
    fiberᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) aᵉ → fiberᵉ gᵉ (fᵉ aᵉ)
  map-fiber-vertical-map-coneᵉ =
    map-domain-hom-arrow-fiberᵉ
      ( vertical-map-coneᵉ fᵉ gᵉ cᵉ)
      ( gᵉ)
      ( hom-arrow-coneᵉ fᵉ gᵉ cᵉ)
      ( aᵉ)
```

### For any `f : A → B` and any identification `p : b ＝ b'` in `B`, we obtain a morphism of arrows between the fiber inclusion at `b` to the fiber inclusion at `b'`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  tr-hom-arrow-inclusion-fiberᵉ :
    {bᵉ b'ᵉ : Bᵉ} (pᵉ : bᵉ ＝ᵉ b'ᵉ) →
    hom-arrowᵉ (inclusion-fiberᵉ fᵉ {bᵉ}) (inclusion-fiberᵉ fᵉ {b'ᵉ})
  pr1ᵉ (tr-hom-arrow-inclusion-fiberᵉ pᵉ) = totᵉ (λ aᵉ → concat'ᵉ (fᵉ aᵉ) pᵉ)
  pr1ᵉ (pr2ᵉ (tr-hom-arrow-inclusion-fiberᵉ pᵉ)) = idᵉ
  pr2ᵉ (pr2ᵉ (tr-hom-arrow-inclusion-fiberᵉ pᵉ)) = refl-htpyᵉ
```

## Properties

### The functorial action of `fiber` preserves the identity function

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (bᵉ : Bᵉ)
  where

  preserves-id-map-fiberᵉ :
    map-domain-hom-arrow-fiberᵉ fᵉ fᵉ id-hom-arrowᵉ bᵉ ~ᵉ idᵉ
  preserves-id-map-fiberᵉ (aᵉ ,ᵉ reflᵉ) = reflᵉ

  coh-preserves-id-hom-arrow-fiberᵉ :
    coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( coh-hom-arrow-fiberᵉ fᵉ fᵉ id-hom-arrowᵉ bᵉ)
      ( inclusion-fiberᵉ fᵉ ·lᵉ preserves-id-map-fiberᵉ)
  coh-preserves-id-hom-arrow-fiberᵉ (aᵉ ,ᵉ reflᵉ) = reflᵉ

  preserves-id-hom-arrow-fiberᵉ :
    htpy-hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ fᵉ)
      ( hom-arrow-fiberᵉ fᵉ fᵉ id-hom-arrowᵉ bᵉ)
      ( id-hom-arrowᵉ)
  pr1ᵉ preserves-id-hom-arrow-fiberᵉ = preserves-id-map-fiberᵉ
  pr1ᵉ (pr2ᵉ preserves-id-hom-arrow-fiberᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ preserves-id-hom-arrow-fiberᵉ) = coh-preserves-id-hom-arrow-fiberᵉ
```

### The functorial action of `fiber` preserves composition of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (βᵉ : hom-arrowᵉ gᵉ hᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  (bᵉ : Bᵉ)
  where

  preserves-comp-map-fiberᵉ :
    map-fiberᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ) bᵉ ~ᵉ
    map-fiberᵉ gᵉ hᵉ βᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ) ∘ᵉ map-fiberᵉ fᵉ gᵉ αᵉ bᵉ
  preserves-comp-map-fiberᵉ (aᵉ ,ᵉ reflᵉ) =
    apᵉ
      ( pairᵉ _)
      ( ( right-unitᵉ) ∙ᵉ
        ( distributive-inv-concatᵉ
          ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
          ( coh-hom-arrowᵉ gᵉ hᵉ βᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))) ∙ᵉ
        ( apᵉ
          ( concatᵉ (invᵉ (coh-hom-arrowᵉ gᵉ hᵉ βᵉ (pr1ᵉ αᵉ aᵉ))) _)
          ( invᵉ
            ( ( ap²ᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ) right-unitᵉ) ∙ᵉ
              ( ap-invᵉ
                ( map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ)
                ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))))))

  compute-left-whisker-inclusion-fiber-preserves-comp-map-fiberᵉ :
    inclusion-fiberᵉ hᵉ ·lᵉ preserves-comp-map-fiberᵉ ~ᵉ refl-htpyᵉ
  compute-left-whisker-inclusion-fiber-preserves-comp-map-fiberᵉ (aᵉ ,ᵉ reflᵉ) =
    ( invᵉ (ap-compᵉ (inclusion-fiberᵉ hᵉ) (pairᵉ _) _)) ∙ᵉ
    ( ap-constᵉ _ _)

  coh-preserves-comp-hom-arrow-fiberᵉ :
    coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( coh-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ hᵉ)
        ( hom-arrow-fiberᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ) bᵉ))
      ( coh-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ hᵉ)
        ( comp-hom-arrowᵉ
          ( inclusion-fiberᵉ fᵉ)
          ( inclusion-fiberᵉ gᵉ)
          ( inclusion-fiberᵉ hᵉ)
          ( hom-arrow-fiberᵉ gᵉ hᵉ βᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ))
          ( hom-arrow-fiberᵉ fᵉ gᵉ αᵉ bᵉ)))
      ( inclusion-fiberᵉ hᵉ ·lᵉ preserves-comp-map-fiberᵉ)
  coh-preserves-comp-hom-arrow-fiberᵉ pᵉ =
    apᵉ
      ( concatᵉ _ _)
      ( compute-left-whisker-inclusion-fiber-preserves-comp-map-fiberᵉ pᵉ)

  preserves-comp-hom-arrow-fiberᵉ :
    htpy-hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ hᵉ)
      ( hom-arrow-fiberᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ) bᵉ)
      ( comp-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ gᵉ)
        ( inclusion-fiberᵉ hᵉ)
        ( hom-arrow-fiberᵉ gᵉ hᵉ βᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ bᵉ))
        ( hom-arrow-fiberᵉ fᵉ gᵉ αᵉ bᵉ))
  pr1ᵉ preserves-comp-hom-arrow-fiberᵉ = preserves-comp-map-fiberᵉ
  pr1ᵉ (pr2ᵉ preserves-comp-hom-arrow-fiberᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ preserves-comp-hom-arrow-fiberᵉ) = coh-preserves-comp-hom-arrow-fiberᵉ
```

### The functorial action of `fiber` preserves homotopies of morphisms of fibers

Givenᵉ twoᵉ morphismsᵉ ofᵉ arrowsᵉ

```text
        α₀ᵉ
      ------>ᵉ
    Aᵉ ------>ᵉ Xᵉ
    |   β₀ᵉ    |
    |         |
  fᵉ |  αᵉ  βᵉ   | gᵉ
    |         |
    ∨ᵉ   α₁ᵉ    ∨ᵉ
    Bᵉ ------>ᵉ Yᵉ
      ------>ᵉ
        β₁ᵉ
```

with aᵉ homotopyᵉ `γᵉ : αᵉ ~ᵉ β`ᵉ ofᵉ morphismsᵉ ofᵉ arrows,ᵉ weᵉ obtainᵉ aᵉ commutingᵉ
diagramᵉ ofᵉ theᵉ formᵉ

```text
           fiberᵉ gᵉ (α₁ᵉ bᵉ)
            ∧ᵉ     |   \ᵉ
           /ᵉ      |    \ᵉ (xᵉ ,ᵉ qᵉ) ↦ᵉ (xᵉ ,ᵉ qᵉ ∙ᵉ γ₁ᵉ bᵉ)
          /ᵉ       |     \ᵉ
         /ᵉ        |      ∨ᵉ
  fiberᵉ fᵉ bᵉ -------->ᵉ fiberᵉ gᵉ (β₁ᵉ bᵉ)
        |         |     /ᵉ
        |         |    /ᵉ
        |         |   /ᵉ
        |         |  /ᵉ
        ∨ᵉ         ∨ᵉ ∨ᵉ
        Aᵉ ------->ᵉ Xᵉ
```

Toᵉ showᵉ thatᵉ weᵉ haveᵉ suchᵉ aᵉ commutingᵉ diagram,ᵉ weᵉ haveᵉ to showᵉ thatᵉ theᵉ topᵉ
triangleᵉ commutes,ᵉ andᵉ thatᵉ thereᵉ isᵉ aᵉ homotopyᵉ fillingᵉ theᵉ diagramᵉ:

Weᵉ firstᵉ showᵉ thatᵉ theᵉ topᵉ triangleᵉ commutes.ᵉ Toᵉ seeᵉ this,ᵉ let
`(aᵉ ,ᵉ reflᵉ) : fiberᵉ fᵉ (fᵉ a)`.ᵉ Thenᵉ weᵉ haveᵉ to showᵉ thatᵉ

```text
  ((xᵉ ,ᵉ qᵉ) ↦ᵉ (xᵉ ,ᵉ qᵉ ∙ᵉ γ₁ᵉ bᵉ)) (map-fiberᵉ fᵉ gᵉ αᵉ (aᵉ ,ᵉ reflᵉ)) ＝ᵉ
  map-fiberᵉ fᵉ gᵉ βᵉ (aᵉ ,ᵉ reflᵉ)
```

Simplyᵉ computingᵉ theᵉ left-handᵉ sideᵉ andᵉ theᵉ right-handᵉ side,ᵉ we'reᵉ taskedᵉ with
constructingᵉ anᵉ identificationᵉ

```text
  (α₀ᵉ aᵉ ,ᵉ ((αᵉ a)⁻¹ᵉ ∙ᵉ reflᵉ) ∙ᵉ γ₁ᵉ (fᵉ aᵉ)) ＝ᵉ (β₀ᵉ aᵉ ,ᵉ (βᵉ a)⁻¹ᵉ ∙ᵉ reflᵉ)
```

Byᵉ theᵉ characterizationᵉ ofᵉ equalityᵉ in fibers,ᵉ itᵉ sufficesᵉ to constructᵉ
identificationsᵉ

```text
  pᵉ : α₀ᵉ aᵉ ＝ᵉ β₀ᵉ aᵉ
  qᵉ : apᵉ gᵉ pᵉ ∙ᵉ ((βᵉ a)⁻¹ᵉ ∙ᵉ reflᵉ) ＝ᵉ ((αᵉ a)⁻¹ᵉ ∙ᵉ reflᵉ) ∙ᵉ γ₁ᵉ (fᵉ aᵉ)
```

Theᵉ firstᵉ identificationᵉ isᵉ `γ₀ᵉ a`.ᵉ Toᵉ obtainᵉ theᵉ secondᵉ identification,ᵉ weᵉ
firstᵉ simplifyᵉ using theᵉ rightᵉ unitᵉ law.ᵉ I.e.,ᵉ itᵉ sufficesᵉ to constructᵉ anᵉ
identificationᵉ

```text
  apᵉ gᵉ pᵉ ∙ᵉ (βᵉ a)⁻¹ᵉ ＝ᵉ (αᵉ a)⁻¹ᵉ ∙ᵉ γ₁ᵉ (fᵉ a).ᵉ
```

Nowᵉ weᵉ proceedᵉ byᵉ transposingᵉ equalityᵉ onᵉ bothᵉ sides,ᵉ i.e.,ᵉ itᵉ sufficesᵉ to
costructᵉ anᵉ identificationᵉ

```text
  αᵉ aᵉ ∙ᵉ apᵉ gᵉ pᵉ ＝ᵉ γ₁ᵉ (fᵉ aᵉ) ∙ᵉ βᵉ a.ᵉ
```

Theᵉ identificationᵉ `γᵉ a`ᵉ hasᵉ exactlyᵉ thisᵉ type.ᵉ Thisᵉ completesᵉ theᵉ constructionᵉ
ofᵉ theᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ upperᵉ triangleᵉ commutes.ᵉ Sinceᵉ itᵉ isᵉ
constructedᵉ asᵉ aᵉ familyᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
  eq-Eq-fiberᵉ gᵉ (γ₀ᵉ aᵉ) _,ᵉ
```

itᵉ followsᵉ thatᵉ whenᵉ weᵉ leftᵉ whiskerᵉ thisᵉ homotopyᵉ with `inclusion-fiberᵉ g`,ᵉ weᵉ
recoverᵉ theᵉ homotopyᵉ `γ₀ᵉ ·rᵉ inclusion-fiberᵉ f`.ᵉ

Nowᵉ itᵉ remainsᵉ to fillᵉ aᵉ coherenceᵉ forᵉ theᵉ squareᵉ ofᵉ homotopiesᵉ

```text
                   γ₀ᵉ ·rᵉ iᵉ
                ·ᵉ --------->ᵉ ·ᵉ
                |            |
 cohᵉ (trᵉ ∘ᵉ αᵉ bᵉ) |            | coh-hom-arrow-fiberᵉ fᵉ gᵉ βᵉ bᵉ
    ≐ᵉ refl-htpyᵉ |            | ≐ᵉ refl-htpyᵉ
                ∨ᵉ            ∨ᵉ
                ·ᵉ --------->ᵉ ·ᵉ
                   iᵉ ·rᵉ Hᵉ
```

where `H`ᵉ isᵉ theᵉ homotopyᵉ thatᵉ weᵉ justᵉ constructed,ᵉ witnessingᵉ thatᵉ theᵉ upperᵉ
triangleᵉ commutes,ᵉ andᵉ where weᵉ haveᵉ writtenᵉ `i`ᵉ forᵉ allᵉ fiberᵉ inclusions.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ βᵉ : hom-arrowᵉ fᵉ gᵉ) (γᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ)
  (bᵉ : Bᵉ)
  where

  htpy-fiberᵉ :
    ( totᵉ (λ xᵉ → concat'ᵉ (gᵉ xᵉ) (htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ bᵉ)) ∘ᵉ
      map-fiberᵉ fᵉ gᵉ αᵉ bᵉ) ~ᵉ
    ( map-fiberᵉ fᵉ gᵉ βᵉ bᵉ)
  htpy-fiberᵉ (aᵉ ,ᵉ reflᵉ) =
    eq-Eq-fiberᵉ gᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ (fᵉ aᵉ))
      ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ aᵉ)
      ( ( apᵉ
          ( concatᵉ
            ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ aᵉ))
            ( map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ (fᵉ aᵉ)))
          ( right-unitᵉ)) ∙ᵉ
        ( double-transpose-eq-concat'ᵉ
          ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ (fᵉ aᵉ))
          ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
          ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)
          ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ aᵉ))
          ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ aᵉ)) ∙ᵉ
        ( invᵉ
          ( apᵉ
            ( concat'ᵉ
              ( gᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
              ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ (fᵉ aᵉ)))
            ( right-unitᵉ))))

  compute-left-whisker-inclusion-fiber-htpy-fiberᵉ :
    inclusion-fiberᵉ gᵉ ·lᵉ htpy-fiberᵉ ~ᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ ·rᵉ inclusion-fiberᵉ fᵉ
  compute-left-whisker-inclusion-fiber-htpy-fiberᵉ (aᵉ ,ᵉ reflᵉ) =
    compute-ap-inclusion-fiber-eq-Eq-fiberᵉ gᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ (fᵉ aᵉ))
      ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ aᵉ)
      ( _)

  htpy-codomain-htpy-hom-arrow-fiberᵉ :
    map-codomain-hom-arrow-fiberᵉ fᵉ gᵉ αᵉ bᵉ ~ᵉ
    map-codomain-hom-arrow-fiberᵉ fᵉ gᵉ βᵉ bᵉ
  htpy-codomain-htpy-hom-arrow-fiberᵉ =
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ

  coh-htpy-hom-arrow-fiberᵉ :
    coherence-square-homotopiesᵉ
      ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ ·rᵉ inclusion-fiberᵉ fᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( inclusion-fiberᵉ gᵉ ·lᵉ htpy-fiberᵉ)
  coh-htpy-hom-arrow-fiberᵉ =
    compute-left-whisker-inclusion-fiber-htpy-fiberᵉ ∙hᵉ inv-htpyᵉ right-unit-htpyᵉ

  htpy-hom-arrow-fiberᵉ :
    htpy-hom-arrowᵉ
      ( inclusion-fiberᵉ fᵉ)
      ( inclusion-fiberᵉ gᵉ)
      ( comp-hom-arrowᵉ
        ( inclusion-fiberᵉ fᵉ)
        ( inclusion-fiberᵉ gᵉ)
        ( inclusion-fiberᵉ gᵉ)
        ( tr-hom-arrow-inclusion-fiberᵉ gᵉ
          ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ γᵉ bᵉ))
        ( hom-arrow-fiberᵉ fᵉ gᵉ αᵉ bᵉ))
      ( hom-arrow-fiberᵉ fᵉ gᵉ βᵉ bᵉ)
  pr1ᵉ htpy-hom-arrow-fiberᵉ = htpy-fiberᵉ
  pr1ᵉ (pr2ᵉ htpy-hom-arrow-fiberᵉ) = htpy-codomain-htpy-hom-arrow-fiberᵉ
  pr2ᵉ (pr2ᵉ htpy-hom-arrow-fiberᵉ) = coh-htpy-hom-arrow-fiberᵉ
```

### Computing `map-fiber-vertical-map-cone` of a horizontal pasting of cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (iᵉ : Xᵉ → Yᵉ) (jᵉ : Yᵉ → Zᵉ) (hᵉ : Cᵉ → Zᵉ)
  where

  preserves-pasting-horizontal-map-fiber-vertical-map-coneᵉ :
    (cᵉ : coneᵉ jᵉ hᵉ Bᵉ) (dᵉ : coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) Aᵉ) (xᵉ : Xᵉ) →
    ( map-fiber-vertical-map-coneᵉ (jᵉ ∘ᵉ iᵉ) hᵉ
      ( pasting-horizontal-coneᵉ iᵉ jᵉ hᵉ cᵉ dᵉ)
      ( xᵉ)) ~ᵉ
    ( map-fiber-vertical-map-coneᵉ jᵉ hᵉ cᵉ (iᵉ xᵉ) ∘ᵉ
      map-fiber-vertical-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ xᵉ)
  preserves-pasting-horizontal-map-fiber-vertical-map-coneᵉ cᵉ dᵉ =
    preserves-comp-map-fiberᵉ
      ( vertical-map-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ)
      ( vertical-map-coneᵉ jᵉ hᵉ cᵉ)
      ( hᵉ)
      ( hom-arrow-coneᵉ jᵉ hᵉ cᵉ)
      ( hom-arrow-coneᵉ iᵉ (vertical-map-coneᵉ jᵉ hᵉ cᵉ) dᵉ)
```

### Computing `map-fiber-vertical-map-cone` of a horizontal pasting of cones

Noteᵉ: Thereᵉ shouldᵉ beᵉ aᵉ definitionᵉ ofᵉ verticalᵉ compositionᵉ ofᵉ morphismsᵉ ofᵉ
arrows,ᵉ andᵉ aᵉ proofᵉ thatᵉ `hom-arrow-fiber`ᵉ preservesᵉ verticalᵉ composition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  (fᵉ : Cᵉ → Zᵉ) (gᵉ : Yᵉ → Zᵉ) (hᵉ : Xᵉ → Yᵉ)
  where

  preserves-pasting-vertical-map-fiber-vertical-map-coneᵉ :
    (cᵉ : coneᵉ fᵉ gᵉ Bᵉ) (dᵉ : coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ Aᵉ) (xᵉ : Cᵉ) →
    ( ( map-fiber-vertical-map-coneᵉ fᵉ (gᵉ ∘ᵉ hᵉ)
        ( pasting-vertical-coneᵉ fᵉ gᵉ hᵉ cᵉ dᵉ)
        ( xᵉ)) ∘ᵉ
      ( map-inv-compute-fiber-compᵉ (pr1ᵉ cᵉ) (pr1ᵉ dᵉ) xᵉ)) ~ᵉ
    ( ( map-inv-compute-fiber-compᵉ gᵉ hᵉ (fᵉ xᵉ)) ∘ᵉ
      ( map-Σᵉ
        ( λ tᵉ → fiberᵉ hᵉ (pr1ᵉ tᵉ))
        ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ xᵉ)
        ( λ tᵉ →
          map-fiber-vertical-map-coneᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) hᵉ dᵉ (pr1ᵉ tᵉ))))
  preserves-pasting-vertical-map-fiber-vertical-map-coneᵉ
    (pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ) (p'ᵉ ,ᵉ q'ᵉ ,ᵉ H'ᵉ) .(pᵉ (p'ᵉ aᵉ))
    ((.(p'ᵉ aᵉ) ,ᵉ reflᵉ) ,ᵉ (aᵉ ,ᵉ reflᵉ)) =
    eq-pair-eq-fiberᵉ
      ( ( right-unitᵉ) ∙ᵉ
        ( distributive-inv-concatᵉ (Hᵉ (p'ᵉ aᵉ)) (apᵉ gᵉ (H'ᵉ aᵉ))) ∙ᵉ
        ( apᵉ
          ( concatᵉ (invᵉ (apᵉ gᵉ (H'ᵉ aᵉ))) (fᵉ (pᵉ (p'ᵉ aᵉ))))
          ( invᵉ right-unitᵉ)) ∙ᵉ
        ( apᵉ
          ( concat'ᵉ (gᵉ (hᵉ (q'ᵉ aᵉ)))
            ( pr2ᵉ
              ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ
                ( pᵉ ,ᵉ qᵉ ,ᵉ Hᵉ)
                ( pᵉ (p'ᵉ aᵉ))
                ( p'ᵉ aᵉ ,ᵉ reflᵉ))))
          ( ( invᵉ (ap-invᵉ gᵉ (H'ᵉ aᵉ))) ∙ᵉ
            ( ap²ᵉ gᵉ (invᵉ right-unitᵉ)))))
```

## See also

-ᵉ Inᵉ [retractsᵉ ofᵉ maps](foundation.retracts-of-maps.md),ᵉ weᵉ showᵉ thatᵉ ifᵉ `g`ᵉ isᵉ
  aᵉ retractᵉ ofᵉ `g'`,ᵉ thenᵉ theᵉ fibersᵉ ofᵉ `g`ᵉ areᵉ retractsᵉ ofᵉ theᵉ fibersᵉ ofᵉ `g'`.ᵉ

## Table of files about fibers of maps

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ fibersᵉ ofᵉ mapsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/fibers-of-maps.mdᵉ}}