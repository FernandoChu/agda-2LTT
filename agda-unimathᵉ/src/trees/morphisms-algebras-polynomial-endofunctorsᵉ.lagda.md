# Morphisms of algebras of polynomial endofunctors

```agda
module trees.morphisms-algebras-polynomial-endofunctorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import trees.algebras-polynomial-endofunctorsᵉ
open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Aᵉ **morphism**ᵉ ofᵉ algebrasᵉ ofᵉ aᵉ polynomialᵉ endofunctorᵉ `Pᵉ Aᵉ B`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ
`fᵉ : Xᵉ → Y$ᵉ betweenᵉ theᵉ underlyingᵉ types,ᵉ equippedᵉ with aᵉ homotopyᵉ witnessingᵉ
thatᵉ theᵉ squareᵉ

```text
           Pᵉ Aᵉ Bᵉ fᵉ
  Pᵉ Aᵉ Bᵉ Xᵉ --------->ᵉ Pᵉ Aᵉ Bᵉ Yᵉ
      |                |
      |                |
      ∨ᵉ                ∨ᵉ
      Xᵉ ------------->ᵉ Yᵉ
               fᵉ
```

commutes.ᵉ

## Definitions

### Morphisms of algebras for polynomial endofunctors

```agda
hom-algebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : algebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
hom-algebra-polynomial-endofunctorᵉ {Aᵉ = Aᵉ} {Bᵉ} Xᵉ Yᵉ =
  Σᵉ ( type-algebra-polynomial-endofunctorᵉ Xᵉ →
      type-algebra-polynomial-endofunctorᵉ Yᵉ)
    ( λ fᵉ →
      ( fᵉ ∘ᵉ (structure-algebra-polynomial-endofunctorᵉ Xᵉ)) ~ᵉ
      ( ( structure-algebra-polynomial-endofunctorᵉ Yᵉ) ∘ᵉ
        ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ fᵉ)))

map-hom-algebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : algebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) →
  hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ →
  type-algebra-polynomial-endofunctorᵉ Xᵉ →
  type-algebra-polynomial-endofunctorᵉ Yᵉ
map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ = pr1ᵉ fᵉ

structure-hom-algebra-polynomial-endofunctorᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ) →
  (Yᵉ : algebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ) →
  (fᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
  ( ( map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∘ᵉ
    ( structure-algebra-polynomial-endofunctorᵉ Xᵉ)) ~ᵉ
  ( ( structure-algebra-polynomial-endofunctorᵉ Yᵉ) ∘ᵉ
    ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
      ( map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ)))
structure-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ = pr2ᵉ fᵉ
```

## Properties

### The identity type of morphisms of algebras of polynomial endofunctors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Xᵉ : algebra-polynomial-endofunctorᵉ l3ᵉ Aᵉ Bᵉ)
  (Yᵉ : algebra-polynomial-endofunctorᵉ l4ᵉ Aᵉ Bᵉ)
  (fᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ)
  where

  htpy-hom-algebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-algebra-polynomial-endofunctorᵉ gᵉ =
    Σᵉ ( map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ ~ᵉ
        map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ gᵉ)
      ( λ Hᵉ →
        ( ( structure-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) ∙hᵉ
          ( ( structure-algebra-polynomial-endofunctorᵉ Yᵉ) ·lᵉ
            ( htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ Hᵉ))) ~ᵉ
        ( ( Hᵉ ·rᵉ structure-algebra-polynomial-endofunctorᵉ Xᵉ) ∙hᵉ
          ( structure-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ gᵉ)))

  refl-htpy-hom-algebra-polynomial-endofunctorᵉ :
    htpy-hom-algebra-polynomial-endofunctorᵉ fᵉ
  pr1ᵉ refl-htpy-hom-algebra-polynomial-endofunctorᵉ = refl-htpyᵉ
  pr2ᵉ refl-htpy-hom-algebra-polynomial-endofunctorᵉ zᵉ =
    ( apᵉ
      ( λ tᵉ →
        concatᵉ
          ( structure-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ zᵉ)
          ( structure-algebra-polynomial-endofunctorᵉ Yᵉ
            ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ
              ( map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) zᵉ))
          ( apᵉ (structure-algebra-polynomial-endofunctorᵉ Yᵉ) tᵉ))
      ( coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ
        ( map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) zᵉ)) ∙ᵉ
    ( right-unitᵉ)

  htpy-eq-hom-algebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-hom-algebra-polynomial-endofunctorᵉ gᵉ
  htpy-eq-hom-algebra-polynomial-endofunctorᵉ .fᵉ reflᵉ =
    refl-htpy-hom-algebra-polynomial-endofunctorᵉ

  is-torsorial-htpy-hom-algebra-polynomial-endofunctorᵉ :
    is-torsorialᵉ htpy-hom-algebra-polynomial-endofunctorᵉ
  is-torsorial-htpy-hom-algebra-polynomial-endofunctorᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ))
      ( pairᵉ (map-hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ fᵉ) refl-htpyᵉ)
      ( is-contr-equiv'ᵉ
        ( Σᵉ ( ( (pr1ᵉ fᵉ) ∘ᵉ pr2ᵉ Xᵉ) ~ᵉ
              ( pr2ᵉ Yᵉ ∘ᵉ map-polynomial-endofunctorᵉ Aᵉ Bᵉ (pr1ᵉ fᵉ)))
            ( λ Hᵉ → (pr2ᵉ fᵉ) ~ᵉ Hᵉ))
        ( equiv-totᵉ
          ( λ Hᵉ →
            ( equiv-concat-htpyᵉ
              ( λ xᵉ →
                apᵉ
                  ( concatᵉ
                    ( pr2ᵉ fᵉ xᵉ)
                    ( structure-algebra-polynomial-endofunctorᵉ Yᵉ
                      ( map-polynomial-endofunctorᵉ Aᵉ Bᵉ (pr1ᵉ fᵉ) xᵉ)))
                  ( apᵉ
                    ( apᵉ (pr2ᵉ Yᵉ))
                    ( coh-refl-htpy-polynomial-endofunctorᵉ Aᵉ Bᵉ (pr1ᵉ fᵉ) xᵉ)))
              ( Hᵉ)) ∘eᵉ
            ( equiv-concat-htpyᵉ right-unit-htpyᵉ Hᵉ)))
        ( is-torsorial-htpyᵉ (pr2ᵉ fᵉ)))

  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-hom-algebra-polynomial-endofunctorᵉ gᵉ)
  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctorᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-algebra-polynomial-endofunctorᵉ)
      ( htpy-eq-hom-algebra-polynomial-endofunctorᵉ)

  extensionality-hom-algebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-algebra-polynomial-endofunctorᵉ gᵉ
  pr1ᵉ (extensionality-hom-algebra-polynomial-endofunctorᵉ gᵉ) =
    htpy-eq-hom-algebra-polynomial-endofunctorᵉ gᵉ
  pr2ᵉ (extensionality-hom-algebra-polynomial-endofunctorᵉ gᵉ) =
    is-equiv-htpy-eq-hom-algebra-polynomial-endofunctorᵉ gᵉ

  eq-htpy-hom-algebra-polynomial-endofunctorᵉ :
    (gᵉ : hom-algebra-polynomial-endofunctorᵉ Xᵉ Yᵉ) →
    htpy-hom-algebra-polynomial-endofunctorᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-algebra-polynomial-endofunctorᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-algebra-polynomial-endofunctorᵉ gᵉ)
```