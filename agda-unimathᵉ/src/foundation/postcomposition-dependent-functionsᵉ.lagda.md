# Postcomposition of dependent functions

```agda
module foundation.postcomposition-dependent-functionsᵉ where

open import foundation-core.postcomposition-dependent-functionsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ andᵉ aᵉ familyᵉ ofᵉ mapsᵉ `fᵉ : {aᵉ : Aᵉ} → Xᵉ aᵉ → Yᵉ a`,ᵉ theᵉ
{{#conceptᵉ "postcompositionᵉ function"ᵉ Disambiguation="ofᵉ dependentᵉ functionsᵉ byᵉ aᵉ familyᵉ ofᵉ maps"ᵉ Agda=postcomp-Πᵉ}}
ofᵉ dependentᵉ functionsᵉ `(aᵉ : Aᵉ) → Xᵉ a`ᵉ byᵉ theᵉ familyᵉ ofᵉ mapsᵉ `f`ᵉ

```text
  postcomp-Πᵉ Aᵉ fᵉ : ((aᵉ : Aᵉ) → Xᵉ aᵉ) → ((aᵉ : Aᵉ) → Yᵉ aᵉ)
```

isᵉ definedᵉ byᵉ `λᵉ hᵉ xᵉ → fᵉ (hᵉ x)`.ᵉ

Noteᵉ that,ᵉ sinceᵉ theᵉ definitionᵉ ofᵉ theᵉ familyᵉ ofᵉ mapsᵉ `f`ᵉ dependsᵉ onᵉ theᵉ baseᵉ
`A`,ᵉ postcompositionᵉ ofᵉ dependentᵉ functionsᵉ doesᵉ notᵉ generalizeᵉ
[postcompositionᵉ ofᵉ functions](foundation-core.postcomposition-functions.mdᵉ) in
theᵉ sameᵉ wayᵉ thatᵉ
[precompositionᵉ ofᵉ dependentᵉ functions](foundation-core.precomposition-dependent-functions.mdᵉ)
generalizesᵉ
[precompositionᵉ ofᵉ functions](foundation-core.precomposition-functions.md).ᵉ Ifᵉ
`A`ᵉ canᵉ varyᵉ whileᵉ keepingᵉ `f`ᵉ fixed,ᵉ weᵉ haveᵉ necessarilyᵉ reducedᵉ to theᵉ caseᵉ ofᵉ
[postcompositionᵉ ofᵉ functions](foundation-core.postcomposition-functions.md).ᵉ

## Properties

### The action on identifications of postcomposition by a family map

Considerᵉ aᵉ mapᵉ `fᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ x`ᵉ andᵉ twoᵉ functionsᵉ
`gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ x`.ᵉ Thenᵉ theᵉ
[actionᵉ onᵉ identifications](foundation.action-on-identifications-functions.mdᵉ)
`apᵉ (postcomp-Πᵉ Aᵉ f)`ᵉ fitsᵉ in aᵉ
[commutingᵉ square](foundation-core.commuting-squares-of-maps.mdᵉ)

```text
                   apᵉ (postcomp-Πᵉ Aᵉ fᵉ)
       (gᵉ ＝ᵉ hᵉ) ------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ＝ᵉ fᵉ ∘ᵉ hᵉ)
          |                                       |
  htpy-eqᵉ |                                       | htpy-eqᵉ
          ∨ᵉ                                       ∨ᵉ
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ h).ᵉ
                          fᵉ ·lᵉ_
```

Similarly,ᵉ theᵉ actionᵉ onᵉ identificationsᵉ `apᵉ (postcomp-Πᵉ Aᵉ f)`ᵉ fitsᵉ in aᵉ
commutingᵉ squareᵉ

```text
                    apᵉ (postcomp-Πᵉ Aᵉ fᵉ)
       (gᵉ ＝ᵉ hᵉ) ------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ＝ᵉ fᵉ ∘ᵉ hᵉ)
          ∧ᵉ                                       ∧ᵉ
  eq-htpyᵉ |                                       | eq-htpyᵉ
          |                                       |
       (gᵉ ~ᵉ hᵉ) -------------------------->ᵉ (fᵉ ∘ᵉ gᵉ ~ᵉ fᵉ ∘ᵉ h).ᵉ
                          fᵉ ·lᵉ_
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  (fᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ) {gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  compute-htpy-eq-ap-postcomp-Πᵉ :
    coherence-square-mapsᵉ
      ( apᵉ (postcomp-Πᵉ Aᵉ fᵉ) {xᵉ = gᵉ} {yᵉ = hᵉ})
      ( htpy-eqᵉ)
      ( htpy-eqᵉ)
      ( fᵉ ·lᵉ_)
  compute-htpy-eq-ap-postcomp-Πᵉ reflᵉ = reflᵉ

  compute-eq-htpy-ap-postcomp-Πᵉ :
    coherence-square-mapsᵉ
      ( fᵉ ·lᵉ_)
      ( eq-htpyᵉ)
      ( eq-htpyᵉ)
      ( apᵉ (postcomp-Πᵉ Aᵉ fᵉ))
  compute-eq-htpy-ap-postcomp-Πᵉ =
    vertical-inv-equiv-coherence-square-mapsᵉ
      ( apᵉ (postcomp-Πᵉ Aᵉ fᵉ))
      ( equiv-funextᵉ)
      ( equiv-funextᵉ)
      ( fᵉ ·lᵉ_)
      ( compute-htpy-eq-ap-postcomp-Πᵉ)
```