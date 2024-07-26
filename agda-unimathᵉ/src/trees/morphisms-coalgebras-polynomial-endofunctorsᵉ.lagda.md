# Morphisms of coalgebras of polynomial endofunctors

```agda
module trees.morphisms-coalgebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import trees.coalgebras-polynomial-endofunctorsᵉ
open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Aᵉ **morphism**ᵉ ofᵉ coalgebrasᵉ ofᵉ aᵉ polynomialᵉ endofunctorᵉ `Pᵉ Aᵉ B`ᵉ consistsᵉ ofᵉ aᵉ
functionᵉ `fᵉ : Xᵉ → Y`ᵉ betweenᵉ theirᵉ underlyingᵉ types,ᵉ equippedᵉ with aᵉ homotopyᵉ
witnessingᵉ thatᵉ theᵉ squareᵉ

```text
              fᵉ
      Xᵉ ------------->ᵉ Yᵉ
      |                |
      |                |
      ∨ᵉ                ∨ᵉ
  Pᵉ Aᵉ Bᵉ Xᵉ --------->ᵉ Pᵉ Aᵉ Bᵉ Yᵉ
           Pᵉ Aᵉ Bᵉ fᵉ
```

commutes.ᵉ

## Definitions

### Morphisms of coalgebras for polynomial endofunctors

```agda
hom-coalgebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : coalgebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
hom-coalgebra-polynomial-endofunctorᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ Yᵉ =
  Σᵉ ( type-coalgebra-polynomial-endofunctorᵉ Xᵉ →
      type-coalgebra-polynomial-endofunctorᵉ Yᵉ)
    ( λ fᵉ →
      ( coherence-square-mapsᵉ fᵉ
          ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ)
          ( structure-coalgebra-polynomial-endofunctorᵉ Yᵉ)
          ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ)))

map-hom-coalgebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : coalgebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) →
  hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ →
  type-coalgebra-polynomial-endofunctorᵉ Xᵉ →
  type-coalgebra-polynomial-endofunctorᵉ Yᵉ
map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ = pr1ᵉ fᵉ

structure-hom-coalgebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : coalgebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
  coherence-square-mapsᵉ
    ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
    ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ)
    ( structure-coalgebra-polynomial-endofunctorᵉ Yᵉ)
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
      ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ))
structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ = pr2ᵉ fᵉ
```

## Properties

### The identity type of morphisms of coalgebras of polynomial endofunctors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : coalgebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  (Yᵉ : coalgebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ)
  (fᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ)
  where

  htpy-hom-coalgebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-coalgebra-polynomial-endofunctorᵉ gᵉ =
    Σᵉ ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ ~ᵉ
        map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ gᵉ)
      ( λ Hᵉ →
        ( ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
          ( structure-coalgebra-polynomial-endofunctorᵉ Yᵉ ·lᵉ Hᵉ)) ~ᵉ
        ( ( ( htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ Hᵉ) ·rᵉ
            ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ)) ∙hᵉ
          ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ gᵉ)))

  refl-htpy-hom-coalgebra-polynomial-endofunctorᵉ :
    htpy-hom-coalgebra-polynomial-endofunctorᵉ fᵉ
  pr1ᵉ refl-htpy-hom-coalgebra-polynomial-endofunctorᵉ = refl-htpyᵉ
  pr2ᵉ refl-htpy-hom-coalgebra-polynomial-endofunctorᵉ zᵉ =
    ( right-unitᵉ) ∙ᵉ
    ( invᵉ
      ( apᵉ
        ( concat'ᵉ
          ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
            ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
            ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ zᵉ))
          ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ zᵉ))
        ( coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ
          ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
          ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ zᵉ))))

  htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-hom-coalgebra-polynomial-endofunctorᵉ gᵉ
  htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ .fᵉ reflᵉ =
    refl-htpy-hom-coalgebra-polynomial-endofunctorᵉ

  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctorᵉ :
    is-torsorialᵉ htpy-hom-coalgebra-polynomial-endofunctorᵉ
  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctorᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ))
      ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ ,ᵉ refl-htpyᵉ)
      ( is-contr-equiv'ᵉ
        ( Σᵉ ( coherence-square-mapsᵉ
              ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
              ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ)
              ( structure-coalgebra-polynomial-endofunctorᵉ Yᵉ)
              ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
                ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)))
            ( λ Gᵉ →
              ( ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
                ( refl-htpyᵉ)) ~ᵉ
              ( Gᵉ)))
        ( equiv-totᵉ
          ( λ Gᵉ →
            equiv-concat-htpy'ᵉ
              ( ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
                ( refl-htpyᵉ))
              ( λ xᵉ →
                apᵉ
                  ( concat'ᵉ
                    ( ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
                        ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
                        ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ xᵉ)))
                    (Gᵉ xᵉ))
                  ( invᵉ
                    ( coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ
                      ( map-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)
                      ( structure-coalgebra-polynomial-endofunctorᵉ Xᵉ xᵉ))))))
        ( is-torsorial-htpyᵉ
          ( ( structure-hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
            ( refl-htpyᵉ))))

  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ gᵉ)
  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-coalgebra-polynomial-endofunctorᵉ)
      ( htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ)

  extensionality-hom-coalgebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-coalgebra-polynomial-endofunctorᵉ gᵉ
  pr1ᵉ (extensionality-hom-coalgebra-polynomial-endofunctorᵉ gᵉ) =
    htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ gᵉ
  pr2ᵉ (extensionality-hom-coalgebra-polynomial-endofunctorᵉ gᵉ) =
    is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ gᵉ

  eq-htpy-hom-coalgebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-coalgebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    htpy-hom-coalgebra-polynomial-endofunctorᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-coalgebra-polynomial-endofunctorᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctorᵉ gᵉ)
```