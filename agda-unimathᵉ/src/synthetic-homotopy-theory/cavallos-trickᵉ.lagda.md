# Cavallo's trick

```agda
module synthetic-homotopy-theory.cavallos-trickᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

**Cavallo'sᵉ trick**ᵉ isᵉ aᵉ wayᵉ ofᵉ upgradingᵉ anᵉ unpointedᵉ
[homotopy](foundation.homotopies.mdᵉ) betweenᵉ
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ) to aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.md).ᵉ

Originally,ᵉ thisᵉ trickᵉ wasᵉ formulatedᵉ byᵉ Evanᵉ Cavalloᵉ forᵉ homogeneousᵉ spaces,ᵉ
butᵉ itᵉ worksᵉ asᵉ soonᵉ asᵉ theᵉ evaluationᵉ mapᵉ `(idᵉ ~ᵉ idᵉ) → Ωᵉ B`ᵉ hasᵉ aᵉ section.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  where

  htpy-cavallos-trickᵉ :
    (fᵉ gᵉ : Aᵉ →∗ᵉ Bᵉ) → sectionᵉ (λ (Hᵉ : idᵉ ~ᵉ idᵉ) → Hᵉ (point-Pointed-Typeᵉ Bᵉ)) →
    (map-pointed-mapᵉ fᵉ ~ᵉ map-pointed-mapᵉ gᵉ) →
    unpointed-htpy-pointed-mapᵉ fᵉ gᵉ
  htpy-cavallos-trickᵉ (fᵉ ,ᵉ reflᵉ) (gᵉ ,ᵉ qᵉ) (Kᵉ ,ᵉ αᵉ) Hᵉ aᵉ =
    Kᵉ (invᵉ qᵉ ∙ᵉ invᵉ (Hᵉ (point-Pointed-Typeᵉ Aᵉ))) (fᵉ aᵉ) ∙ᵉ Hᵉ aᵉ

  coherence-point-cavallos-trickᵉ :
    (fᵉ gᵉ : Aᵉ →∗ᵉ Bᵉ) (sᵉ : sectionᵉ (λ (Hᵉ : idᵉ ~ᵉ idᵉ) → Hᵉ (point-Pointed-Typeᵉ Bᵉ))) →
    (Hᵉ : map-pointed-mapᵉ fᵉ ~ᵉ map-pointed-mapᵉ gᵉ) →
    coherence-point-unpointed-htpy-pointed-Πᵉ fᵉ gᵉ
      ( htpy-cavallos-trickᵉ fᵉ gᵉ sᵉ Hᵉ)
  coherence-point-cavallos-trickᵉ (fᵉ ,ᵉ reflᵉ) (gᵉ ,ᵉ qᵉ) (Kᵉ ,ᵉ αᵉ) Hᵉ =
    invᵉ
      ( ( right-whisker-concatᵉ
          ( ( right-whisker-concatᵉ (αᵉ _) (Hᵉ _)) ∙ᵉ
            ( is-section-inv-concat'ᵉ (Hᵉ _) (invᵉ qᵉ)))
          ( qᵉ)) ∙ᵉ
        ( left-invᵉ qᵉ))

  cavallos-trickᵉ :
    (fᵉ gᵉ : Aᵉ →∗ᵉ Bᵉ) → sectionᵉ (λ (Hᵉ : idᵉ ~ᵉ idᵉ) → Hᵉ (point-Pointed-Typeᵉ Bᵉ)) →
    (map-pointed-mapᵉ fᵉ ~ᵉ map-pointed-mapᵉ gᵉ) → fᵉ ~∗ᵉ gᵉ
  pr1ᵉ (cavallos-trickᵉ fᵉ gᵉ sᵉ Hᵉ) = htpy-cavallos-trickᵉ fᵉ gᵉ sᵉ Hᵉ
  pr2ᵉ (cavallos-trickᵉ fᵉ gᵉ sᵉ Hᵉ) = coherence-point-cavallos-trickᵉ fᵉ gᵉ sᵉ Hᵉ
```

## References

-ᵉ Cavallo'sᵉ trickᵉ wasᵉ originallyᵉ formalizedᵉ in theᵉ
  [cubicalᵉ agdaᵉ library](https://agda.github.io/cubical/Cubical.Foundations.Pointed.Homogeneous.html).ᵉ
-ᵉ Theᵉ aboveᵉ generalizationᵉ wasᵉ foundᵉ byᵉ Buchholtz,ᵉ Christensen,ᵉ Rijke,ᵉ andᵉ
  Taxeråsᵉ Flaten,ᵉ in {{#citeᵉ BCFR23}}.ᵉ

{{#bibliographyᵉ}}