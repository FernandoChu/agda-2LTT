# Coproduct decompositions

```agda
module foundation.coproduct-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-decompositions-subuniverseᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ)
  where

  binary-coproduct-Decompositionᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
  binary-coproduct-Decompositionᵉ =
    Σᵉ ( UUᵉ l2ᵉ) ( λ Aᵉ → Σᵉ ( UUᵉ l3ᵉ) ( λ Bᵉ → (Xᵉ ≃ᵉ (Aᵉ +ᵉ Bᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  (dᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Xᵉ)
  where

  left-summand-binary-coproduct-Decompositionᵉ : UUᵉ l2ᵉ
  left-summand-binary-coproduct-Decompositionᵉ = pr1ᵉ dᵉ

  right-summand-binary-coproduct-Decompositionᵉ : UUᵉ l3ᵉ
  right-summand-binary-coproduct-Decompositionᵉ = pr1ᵉ (pr2ᵉ dᵉ)

  matching-correspondence-binary-coproduct-Decompositionᵉ :
    Xᵉ ≃ᵉ
    ( left-summand-binary-coproduct-Decompositionᵉ +ᵉ
      right-summand-binary-coproduct-Decompositionᵉ)
  matching-correspondence-binary-coproduct-Decompositionᵉ = pr2ᵉ (pr2ᵉ dᵉ)
```

## Propositions

### Coproduct decomposition is equivalent to coproduct decomposition of a full subuniverse

```agda
equiv-coproduct-Decomposition-full-subuniverseᵉ :
  {l1ᵉ : Level} → (Xᵉ : UUᵉ l1ᵉ) →
  binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ ≃ᵉ
  binary-coproduct-Decomposition-subuniverseᵉ (λ _ → unit-Propᵉ) (Xᵉ ,ᵉ starᵉ)
pr1ᵉ (equiv-coproduct-Decomposition-full-subuniverseᵉ Xᵉ) dᵉ =
  ( left-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ starᵉ) ,ᵉ
  ( right-summand-binary-coproduct-Decompositionᵉ dᵉ ,ᵉ starᵉ) ,ᵉ
  ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
pr2ᵉ (equiv-coproduct-Decomposition-full-subuniverseᵉ Xᵉ) =
  is-equiv-is-invertibleᵉ
    ( λ dᵉ →
      type-left-summand-binary-coproduct-Decomposition-subuniverseᵉ
        ( λ _ → unit-Propᵉ)
        ( Xᵉ ,ᵉ starᵉ)
        ( dᵉ) ,ᵉ
      type-right-summand-binary-coproduct-Decomposition-subuniverseᵉ
        ( λ _ → unit-Propᵉ)
        ( Xᵉ ,ᵉ starᵉ)
        ( dᵉ) ,ᵉ
      matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
        ( λ _ → unit-Propᵉ)
        ( Xᵉ ,ᵉ starᵉ)
        ( dᵉ))
    ( λ dᵉ →
      eq-equiv-binary-coproduct-Decomposition-subuniverseᵉ
        ( λ _ → unit-Propᵉ)
        ( Xᵉ ,ᵉ starᵉ)
        ( _)
        ( dᵉ)
        ( id-equivᵉ ,ᵉ
          ( id-equivᵉ ,ᵉ
            right-whisker-compᵉ
              ( id-map-coproductᵉ _ _)
              ( map-equivᵉ
                ( matching-correspondence-binary-coproduct-Decomposition-subuniverseᵉ
                  ( λ _ → unit-Propᵉ)
                  ( Xᵉ ,ᵉ starᵉ)
                  ( dᵉ))))))
    ( refl-htpyᵉ)
```

### Characterization of equality of binary coproduct Decomposition

```agda
equiv-binary-coproduct-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Yᵉ : binary-coproduct-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-binary-coproduct-Decompositionᵉ Xᵉ Yᵉ =
  Σᵉ ( left-summand-binary-coproduct-Decompositionᵉ Xᵉ ≃ᵉ
      left-summand-binary-coproduct-Decompositionᵉ Yᵉ)
    ( λ elᵉ →
      Σᵉ ( right-summand-binary-coproduct-Decompositionᵉ Xᵉ ≃ᵉ
          right-summand-binary-coproduct-Decompositionᵉ Yᵉ)
        ( λ erᵉ →
          ( map-coproductᵉ (map-equivᵉ elᵉ) (map-equivᵉ erᵉ) ∘ᵉ
            map-equivᵉ
              ( matching-correspondence-binary-coproduct-Decompositionᵉ Xᵉ)) ~ᵉ
          ( map-equivᵉ
            ( matching-correspondence-binary-coproduct-Decompositionᵉ Yᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Yᵉ : binary-coproduct-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ)
  (eᵉ : equiv-binary-coproduct-Decompositionᵉ Xᵉ Yᵉ)
  where

  equiv-left-summand-equiv-binary-coproduct-Decompositionᵉ :
    left-summand-binary-coproduct-Decompositionᵉ Xᵉ ≃ᵉ
    left-summand-binary-coproduct-Decompositionᵉ Yᵉ
  equiv-left-summand-equiv-binary-coproduct-Decompositionᵉ = pr1ᵉ eᵉ

  map-equiv-left-summand-equiv-binary-coproduct-Decompositionᵉ :
    left-summand-binary-coproduct-Decompositionᵉ Xᵉ →
    left-summand-binary-coproduct-Decompositionᵉ Yᵉ
  map-equiv-left-summand-equiv-binary-coproduct-Decompositionᵉ =
    map-equivᵉ equiv-left-summand-equiv-binary-coproduct-Decompositionᵉ

  equiv-right-summand-equiv-binary-coproduct-Decompositionᵉ :
    right-summand-binary-coproduct-Decompositionᵉ Xᵉ ≃ᵉ
    right-summand-binary-coproduct-Decompositionᵉ Yᵉ
  equiv-right-summand-equiv-binary-coproduct-Decompositionᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  map-equiv-right-summand-equiv-binary-coproduct-Decompositionᵉ :
    right-summand-binary-coproduct-Decompositionᵉ Xᵉ →
    right-summand-binary-coproduct-Decompositionᵉ Yᵉ
  map-equiv-right-summand-equiv-binary-coproduct-Decompositionᵉ =
    map-equivᵉ (equiv-right-summand-equiv-binary-coproduct-Decompositionᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  id-equiv-binary-coproduct-Decompositionᵉ :
    equiv-binary-coproduct-Decompositionᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-binary-coproduct-Decompositionᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-binary-coproduct-Decompositionᵉ) = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-binary-coproduct-Decompositionᵉ) xᵉ =
    id-map-coproductᵉ
      ( left-summand-binary-coproduct-Decompositionᵉ Xᵉ)
      ( right-summand-binary-coproduct-Decompositionᵉ Xᵉ)
      ( map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decompositionᵉ Xᵉ)
        ( xᵉ))

  is-torsorial-equiv-binary-coproduct-Decompositionᵉ :
    is-torsorialᵉ (equiv-binary-coproduct-Decompositionᵉ Xᵉ)
  is-torsorial-equiv-binary-coproduct-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ ( left-summand-binary-coproduct-Decompositionᵉ Xᵉ))
      ( left-summand-binary-coproduct-Decompositionᵉ Xᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (right-summand-binary-coproduct-Decompositionᵉ Xᵉ))
        ( right-summand-binary-coproduct-Decompositionᵉ Xᵉ ,ᵉ id-equivᵉ)
        ( is-torsorial-htpy-equivᵉ
          ( equiv-coproductᵉ id-equivᵉ id-equivᵉ ∘eᵉ
            matching-correspondence-binary-coproduct-Decompositionᵉ Xᵉ)))

  equiv-eq-binary-coproduct-Decompositionᵉ :
    (Yᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) → (Xᵉ ＝ᵉ Yᵉ) →
    equiv-binary-coproduct-Decompositionᵉ Xᵉ Yᵉ
  equiv-eq-binary-coproduct-Decompositionᵉ .Xᵉ reflᵉ =
    id-equiv-binary-coproduct-Decompositionᵉ

  is-equiv-equiv-eq-binary-coproduct-Decompositionᵉ :
    (Yᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-binary-coproduct-Decompositionᵉ Yᵉ)
  is-equiv-equiv-eq-binary-coproduct-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-binary-coproduct-Decompositionᵉ
      equiv-eq-binary-coproduct-Decompositionᵉ

  extensionality-binary-coproduct-Decompositionᵉ :
    (Yᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-binary-coproduct-Decompositionᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-binary-coproduct-Decompositionᵉ Yᵉ) =
    equiv-eq-binary-coproduct-Decompositionᵉ Yᵉ
  pr2ᵉ (extensionality-binary-coproduct-Decompositionᵉ Yᵉ) =
    is-equiv-equiv-eq-binary-coproduct-Decompositionᵉ Yᵉ

  eq-equiv-binary-coproduct-Decompositionᵉ :
    (Yᵉ : binary-coproduct-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    equiv-binary-coproduct-Decompositionᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-binary-coproduct-Decompositionᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-binary-coproduct-Decompositionᵉ Yᵉ)
```

### Equivalence between `X → Fin 2` and `binary-coproduct-Decomposition l1 l1 X`

```agda
module _
  {l1ᵉ : Level}
  (Xᵉ : UUᵉ l1ᵉ)
  where

  module _
    (fᵉ : Xᵉ → Finᵉ 2ᵉ)
    where

    matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
      (Xᵉ ≃ᵉ ((fiberᵉ fᵉ (inlᵉ (inrᵉ starᵉ))) +ᵉ (fiberᵉ fᵉ (inrᵉ starᵉ))))
    matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ =
      ( ( equiv-coproductᵉ
          ( left-unit-law-Σ-is-contrᵉ ( is-contr-Fin-one-ℕᵉ) ( inrᵉ starᵉ))
          ( left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ)) ∘eᵉ
        ( ( right-distributive-Σ-coproductᵉ ( Finᵉ 1ᵉ) unitᵉ (λ xᵉ → fiberᵉ fᵉ xᵉ) ∘eᵉ
            ( inv-equiv-total-fiberᵉ fᵉ))))

    compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
      (xᵉ : Xᵉ) →
      (inlᵉ (inrᵉ starᵉ) ＝ᵉ fᵉ xᵉ) →
      Σᵉ ( Σᵉ ( fiberᵉ fᵉ (inlᵉ (inrᵉ starᵉ)))
            ( λ yᵉ →
              inlᵉ yᵉ ＝ᵉ
              ( map-equivᵉ
                ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
                ( xᵉ))))
        ( λ zᵉ → pr1ᵉ (pr1ᵉ zᵉ) ＝ᵉ xᵉ)
    compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
      xᵉ pᵉ =
      trᵉ
        ( λ aᵉ →
          Σᵉ ( Σᵉ ( fiberᵉ fᵉ (inlᵉ (inrᵉ starᵉ)))
              ( λ yᵉ →
                inlᵉ yᵉ ＝ᵉ
                ( map-coproductᵉ
                  ( map-left-unit-law-Σ-is-contrᵉ
                    ( is-contr-Fin-one-ℕᵉ)
                    ( inrᵉ starᵉ))
                  ( map-left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ))
                ( map-right-distributive-Σ-coproductᵉ
                  ( Finᵉ 1ᵉ)
                  ( unitᵉ)
                  ( λ xᵉ → fiberᵉ fᵉ xᵉ)
                  ( pr1ᵉ aᵉ ,ᵉ xᵉ ,ᵉ pr2ᵉ aᵉ))))
            ( λ zᵉ → pr1ᵉ (pr1ᵉ zᵉ) ＝ᵉ xᵉ))
        ( eq-pair-Σᵉ pᵉ ( tr-Id-rightᵉ pᵉ (invᵉ pᵉ) ∙ᵉ left-invᵉ pᵉ))
        ( ( ( xᵉ ,ᵉ (invᵉ pᵉ)) ,ᵉ
            ( apᵉ
              ( inlᵉ)
              ( invᵉ
                ( map-inv-eq-transpose-equivᵉ
                  ( left-unit-law-Σ-is-contrᵉ is-contr-Fin-one-ℕᵉ (inrᵉ starᵉ))
                  ( reflᵉ))))) ,ᵉ
          reflᵉ)

    compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ :
      (yᵉ : fiberᵉ fᵉ (inlᵉ (inrᵉ starᵉ))) →
      pr1ᵉ yᵉ ＝ᵉ
      map-inv-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
        ( inlᵉ yᵉ)
    compute-left-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ
      yᵉ =
      map-eq-transpose-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
        ( invᵉ
          ( pr2ᵉ
            ( pr1ᵉ
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( pr1ᵉ yᵉ)
                ( invᵉ (pr2ᵉ yᵉ))))) ∙ᵉ
          apᵉ
            inlᵉ
            ( eq-pair-Σᵉ
              ( pr2ᵉ
                ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                  ( pr1ᵉ yᵉ)
                  ( invᵉ (pr2ᵉ yᵉ))))
              ( eq-is-propᵉ (is-set-Finᵉ 2 _ _))))

    compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
      (xᵉ : Xᵉ) →
      (inrᵉ starᵉ ＝ᵉ fᵉ xᵉ) →
      Σᵉ ( Σᵉ ( fiberᵉ fᵉ (inrᵉ starᵉ))
            ( λ yᵉ →
              inrᵉ yᵉ ＝ᵉ
              ( map-equivᵉ
                ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
                ( xᵉ))))
        ( λ zᵉ → pr1ᵉ (pr1ᵉ zᵉ) ＝ᵉ xᵉ)
    compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
      xᵉ pᵉ =
      trᵉ
        ( λ aᵉ →
          Σᵉ ( Σᵉ ( fiberᵉ fᵉ (inrᵉ starᵉ))
                ( λ yᵉ →
                  inrᵉ yᵉ ＝ᵉ
                  ( map-coproductᵉ
                    ( map-left-unit-law-Σ-is-contrᵉ
                      ( is-contr-Fin-one-ℕᵉ)
                      ( inrᵉ starᵉ))
                    ( map-left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ))
                  ( map-right-distributive-Σ-coproductᵉ
                    ( Finᵉ 1ᵉ)
                    ( unitᵉ)
                    ( λ xᵉ → fiberᵉ fᵉ xᵉ)
                    ( pr1ᵉ aᵉ ,ᵉ xᵉ ,ᵉ pr2ᵉ aᵉ))))
            ( λ zᵉ → pr1ᵉ (pr1ᵉ zᵉ) ＝ᵉ xᵉ))
        ( eq-pair-Σᵉ pᵉ ( tr-Id-rightᵉ pᵉ (invᵉ pᵉ) ∙ᵉ left-invᵉ pᵉ))
        ( ( ( xᵉ ,ᵉ (invᵉ pᵉ)) ,ᵉ
            ( apᵉ
              ( inrᵉ)
              ( invᵉ
                  ( map-inv-eq-transpose-equivᵉ
                    ( left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ)
                    ( reflᵉ))))) ,ᵉ
          reflᵉ)

    compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ :
      (yᵉ : fiberᵉ fᵉ (inrᵉ starᵉ)) →
      pr1ᵉ yᵉ ＝ᵉ
      map-inv-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
        ( inrᵉ yᵉ)
    compute-right-inv-matching-correspondence-binary-coporducd-Decomposition-map-into-Fin-Two-ℕᵉ
      yᵉ =
      map-eq-transpose-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
        ( invᵉ
          ( pr2ᵉ
            ( pr1ᵉ
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( pr1ᵉ yᵉ)
                ( invᵉ (pr2ᵉ yᵉ))))) ∙ᵉ
          apᵉ
            inrᵉ
            ( eq-pair-Σᵉ
              ( pr2ᵉ
                ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                  ( pr1ᵉ yᵉ)
                  ( invᵉ (pr2ᵉ yᵉ))))
              ( eq-is-propᵉ (is-set-Finᵉ 2 _ _))))

    map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
      binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ
    pr1ᵉ (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ) =
      fiberᵉ fᵉ (inlᵉ (inrᵉ starᵉ))
    pr1ᵉ (pr2ᵉ (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)) =
      fiberᵉ fᵉ (inrᵉ starᵉ)
    pr2ᵉ (pr2ᵉ (map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)) =
      matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    ( left-summand-binary-coproduct-Decompositionᵉ dᵉ +ᵉ
      right-summand-binary-coproduct-Decompositionᵉ dᵉ) →
    Finᵉ 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ (inlᵉ _) =
    inlᵉ (inrᵉ starᵉ)
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ (inrᵉ _) =
    inrᵉ starᵉ

  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    Xᵉ → Finᵉ 2
  map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ xᵉ =
    map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
      ( dᵉ)
      ( map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
        ( xᵉ))

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    (tᵉ :
      ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) +ᵉ
      ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)) →
    ( inlᵉ (inrᵉ starᵉ) ＝ᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
        ( dᵉ)
        ( tᵉ)) →
    Σᵉ ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
      ( λ aᵉ → inlᵉ aᵉ ＝ᵉ tᵉ)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ (inlᵉ yᵉ) xᵉ =
    yᵉ ,ᵉ reflᵉ

  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    (xᵉ : Xᵉ) →
    ( inlᵉ (inrᵉ starᵉ) ＝ᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ xᵉ) →
    Σᵉ ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
      ( λ aᵉ →
        inlᵉ aᵉ ＝ᵉ
        map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) xᵉ)
  compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ xᵉ pᵉ =
    compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
      ( dᵉ)
      ( map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) xᵉ)
      ( pᵉ)

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    (tᵉ :
      ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) +ᵉ
      ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)) →
    ( inrᵉ starᵉ ＝ᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
        ( dᵉ)
        ( tᵉ)) →
    Σᵉ ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
      ( λ aᵉ → inrᵉ aᵉ ＝ᵉ tᵉ)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ (inrᵉ yᵉ) xᵉ =
    yᵉ ,ᵉ reflᵉ

  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    (xᵉ : Xᵉ) →
    ( inrᵉ starᵉ ＝ᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ xᵉ) →
    Σᵉ ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
      ( λ aᵉ →
        inrᵉ aᵉ ＝ᵉ
        map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) xᵉ)
  compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ xᵉ pᵉ =
    compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
      ( dᵉ)
      ( map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) xᵉ)
      ( pᵉ)

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ :
    (fᵉ : Xᵉ → Finᵉ 2ᵉ) →
    (xᵉ : Xᵉ) →
    (vᵉ : (inlᵉ (inrᵉ starᵉ) ＝ᵉ fᵉ xᵉ) +ᵉ (inrᵉ starᵉ ＝ᵉ fᵉ xᵉ)) →
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ fᵉ) xᵉ ＝ᵉ
      fᵉ xᵉ)
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    fᵉ xᵉ (inlᵉ yᵉ) =
    ( invᵉ
      ( apᵉ
          ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
              ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ fᵉ))
          ( pr2ᵉ
            ( pr1ᵉ
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                fᵉ
                xᵉ
                yᵉ)))) ∙ᵉ
      yᵉ)
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    fᵉ xᵉ (inrᵉ yᵉ) =
    ( invᵉ
      ( apᵉ
          ( λ pᵉ →
            map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
              ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ fᵉ)
              ( pᵉ))
          ( pr2ᵉ
            ( pr1ᵉ
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                fᵉ
                xᵉ
                yᵉ)))) ∙ᵉ
      yᵉ)

  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ ∘ᵉ
      map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ) ~ᵉ
    idᵉ
  is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    fᵉ =
    eq-htpyᵉ
      ( λ xᵉ →
        is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
          ( fᵉ)
          ( xᵉ)
          ( map-coproductᵉ
            ( map-left-unit-law-Σ-is-contrᵉ is-contr-Fin-one-ℕᵉ ( inrᵉ starᵉ))
            ( map-left-unit-law-Σ-is-contrᵉ is-contr-unitᵉ starᵉ)
            ( map-right-distributive-Σ-coproductᵉ
              ( Finᵉ 1ᵉ)
              ( unitᵉ)
              ( λ yᵉ → yᵉ ＝ᵉ fᵉ xᵉ)
              ( fᵉ xᵉ ,ᵉ reflᵉ))))

  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    left-summand-binary-coproduct-Decompositionᵉ
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ)) ≃ᵉ
    left-summand-binary-coproduct-Decompositionᵉ dᵉ
  equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ =
    ( ( right-unit-law-coproductᵉ
          ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)) ∘eᵉ
      ( ( equiv-coproductᵉ
          ( right-unit-law-Σ-is-contrᵉ (λ _ → is-contr-unitᵉ) ∘eᵉ
            equiv-totᵉ
              ( λ _ → extensionality-Finᵉ 2 (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ))))
          ( right-absorption-Σᵉ
              (right-summand-binary-coproduct-Decompositionᵉ dᵉ) ∘eᵉ
            equiv-totᵉ
              ( λ _ → extensionality-Finᵉ 2 (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ))))) ∘eᵉ
        ( ( right-distributive-Σ-coproductᵉ
            ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
            ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
            ( λ yᵉ →
              map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                dᵉ yᵉ ＝ᵉ inlᵉ (inrᵉ starᵉ))) ∘eᵉ
          ( equiv-Σ-equiv-baseᵉ
            ( λ yᵉ →
              map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                dᵉ yᵉ ＝ᵉ inlᵉ (inrᵉ starᵉ))
            ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)))))

  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    right-summand-binary-coproduct-Decompositionᵉ
      ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ)) ≃ᵉ
    right-summand-binary-coproduct-Decompositionᵉ dᵉ
  equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ =
    ( ( left-unit-law-coproductᵉ
        ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)) ∘eᵉ
      ( ( equiv-coproductᵉ
          ( right-absorption-Σᵉ
              ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) ∘eᵉ
            equiv-totᵉ
              ( λ _ → extensionality-Finᵉ 2 (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ)))
          ( right-unit-law-Σ-is-contrᵉ (λ _ → is-contr-unitᵉ) ∘eᵉ
            equiv-totᵉ
              ( λ _ → extensionality-Finᵉ 2 (inrᵉ starᵉ) (inrᵉ starᵉ)))) ∘eᵉ
        ( ( right-distributive-Σ-coproductᵉ
            ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
            ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
            ( λ yᵉ →
              map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                dᵉ yᵉ ＝ᵉ inrᵉ starᵉ)) ∘eᵉ
          ( equiv-Σ-equiv-baseᵉ
            ( λ yᵉ →
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                dᵉ yᵉ) ＝ᵉ
              ( inrᵉ starᵉ))
            ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)))))

  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    ( dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    ( inlᵉ ∘ᵉ
      ( map-equivᵉ
        ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( dᵉ)))) ~ᵉ
    ( ( map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)) ∘ᵉ pr1ᵉ)
  compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ (xᵉ ,ᵉ pᵉ) =
    apᵉ
      ( λ xᵉ →
        inlᵉ
        ( map-equivᵉ
            ( ( right-unit-law-coproductᵉ
                ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)) ∘eᵉ
              ( ( equiv-coproductᵉ
                  ( right-unit-law-Σ-is-contrᵉ (λ _ → is-contr-unitᵉ) ∘eᵉ
                    equiv-totᵉ
                      ( λ _ →
                        extensionality-Finᵉ 2 (inlᵉ (inrᵉ starᵉ)) (inlᵉ (inrᵉ starᵉ))))
                  ( right-absorption-Σᵉ
                      (right-summand-binary-coproduct-Decompositionᵉ dᵉ) ∘eᵉ
                    equiv-totᵉ
                      ( λ _ →
                        extensionality-Finᵉ 2 (inrᵉ starᵉ) (inlᵉ (inrᵉ starᵉ))))) ∘eᵉ
                ( ( right-distributive-Σ-coproductᵉ
                    ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
                    ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
                    ( λ yᵉ →
                      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                        dᵉ yᵉ ＝ᵉ
                      inlᵉ (inrᵉ starᵉ))))))
            ( xᵉ)))
      ( eq-pair-Σᵉ
        {tᵉ =
          pairᵉ
            ( inlᵉ
              ( pr1ᵉ
                ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                    dᵉ xᵉ (invᵉ pᵉ))))
            ( reflᵉ)}
          ( invᵉ
            ( pr2ᵉ
              ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ)
                ( xᵉ)
                ( invᵉ pᵉ))))
          ( eq-is-propᵉ
            ( is-set-Finᵉ 2 _ _))) ∙ᵉ
    ( pr2ᵉ
        ( compute-left-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( dᵉ)
          ( xᵉ)
          ( invᵉ pᵉ)))

  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    ( dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    ( inrᵉ ∘ᵉ
      ( map-equivᵉ
        ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( dᵉ)))) ~ᵉ
    ( map-equivᵉ
      ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) ∘ᵉ pr1ᵉ)
  compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ (xᵉ ,ᵉ pᵉ) =
    apᵉ
      ( λ xᵉ →
        inrᵉ
          ( map-equivᵉ
            ( ( left-unit-law-coproductᵉ
                ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)) ∘eᵉ
              ( ( equiv-coproductᵉ
                  ( right-absorption-Σᵉ
                      ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) ∘eᵉ
                    equiv-totᵉ
                      ( λ _ →
                        extensionality-Finᵉ 2 (inlᵉ (inrᵉ starᵉ)) (inrᵉ starᵉ)))
                  ( right-unit-law-Σ-is-contrᵉ (λ _ → is-contr-unitᵉ) ∘eᵉ
                    equiv-totᵉ
                      ( λ _ → extensionality-Finᵉ 2 (inrᵉ starᵉ) (inrᵉ starᵉ)))) ∘eᵉ
                ( ( right-distributive-Σ-coproductᵉ
                    ( left-summand-binary-coproduct-Decompositionᵉ dᵉ)
                    ( right-summand-binary-coproduct-Decompositionᵉ dᵉ)
                    ( λ yᵉ →
                      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
                        dᵉ yᵉ ＝ᵉ inrᵉ starᵉ)))))
            ( xᵉ)))
      ( eq-pair-Σᵉ
        { tᵉ =
          ( inrᵉ
            ( pr1ᵉ
              ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ)
                ( xᵉ)
                ( invᵉ pᵉ))) ,ᵉ
            reflᵉ)}
        ( invᵉ
          ( pr2ᵉ
            ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( dᵉ)
              ( xᵉ)
              ( invᵉ pᵉ))))
        ( eq-is-propᵉ
          ( is-set-Finᵉ 2 _ _))) ∙ᵉ
    ( pr2ᵉ
      ( compute-right-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( dᵉ)
        ( xᵉ)
        ( invᵉ pᵉ)))

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ :
    ( dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    ( xᵉ : Xᵉ) →
    ( ( inlᵉ (inrᵉ starᵉ) ＝ᵉ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( dᵉ)
          ( xᵉ))) +ᵉ
      ( inrᵉ starᵉ ＝ᵉ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( dᵉ)
          ( xᵉ)))) →
    ( map-coproductᵉ
        ( map-equivᵉ
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ)))
        ( map-equivᵉ
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ))) ∘ᵉ
      map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ)))
      ( xᵉ) ＝ᵉ
    map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ) xᵉ
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ xᵉ (inlᵉ pᵉ) =
    apᵉ
      ( map-coproductᵉ
        ( map-equivᵉ
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ)))
        ( map-equivᵉ
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ))))
      ( invᵉ
        ( pr2ᵉ
          ( pr1ᵉ
            ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ))
              ( xᵉ)
              ( pᵉ))))) ∙ᵉ
    ( compute-equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
      ( dᵉ)
      ( pr1ᵉ
        ( pr1ᵉ
          ( pr1ᵉ
            ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ))
              ( xᵉ)
              ( pᵉ)))) ,ᵉ
        ( pr2ᵉ
          ( pr1ᵉ
            ( pr1ᵉ
              ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                  ( dᵉ))
                ( xᵉ)
                ( pᵉ)))))) ∙ᵉ
      apᵉ
        ( map-equivᵉ
          ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ))
        ( pr2ᵉ
          ( compute-left-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( dᵉ))
            ( xᵉ)
            ( pᵉ))))
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
    dᵉ xᵉ (inrᵉ pᵉ) =
    apᵉ
      ( map-coproductᵉ
        ( map-equivᵉ
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ)))
        ( map-equivᵉ
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ))))
      ( invᵉ
        ( pr2ᵉ
          ( pr1ᵉ
            ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ))
              ( xᵉ)
              ( pᵉ))))) ∙ᵉ
    ( compute-equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
      ( dᵉ)
      ( pr1ᵉ
        ( pr1ᵉ
          ( pr1ᵉ
            ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ))
              ( xᵉ)
              ( pᵉ)))) ,ᵉ
        pr2ᵉ
          ( pr1ᵉ
            ( pr1ᵉ
              ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                  ( dᵉ))
                ( xᵉ)
                ( pᵉ))))) ∙ᵉ
      apᵉ
        ( map-equivᵉ
          ( matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ))
        ( pr2ᵉ
            ( compute-right-matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
              ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
                ( dᵉ))
              ( xᵉ)
              ( pᵉ))))

  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helperᵉ :
    (yᵉ : Finᵉ 2ᵉ) → (inlᵉ (inrᵉ starᵉ) ＝ᵉ yᵉ) +ᵉ (inrᵉ starᵉ ＝ᵉ yᵉ)
  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helperᵉ (inlᵉ xᵉ) =
    inlᵉ (apᵉ inlᵉ (eq-is-contrᵉ is-contr-Fin-one-ℕᵉ))
  value-map-into-Fin-Two-ℕ-eq-zero-or-one-helperᵉ (inrᵉ xᵉ) =
    inrᵉ (apᵉ inrᵉ (eq-is-contrᵉ is-contr-unitᵉ))

  value-map-into-Fin-Two-ℕ-eq-zero-or-oneᵉ :
    (fᵉ : Xᵉ → Finᵉ 2ᵉ) →
    (xᵉ : Xᵉ) →
    (inlᵉ (inrᵉ starᵉ) ＝ᵉ fᵉ xᵉ) +ᵉ (inrᵉ starᵉ ＝ᵉ fᵉ xᵉ)
  value-map-into-Fin-Two-ℕ-eq-zero-or-oneᵉ fᵉ xᵉ =
    value-map-into-Fin-Two-ℕ-eq-zero-or-one-helperᵉ (fᵉ xᵉ)

  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    ( dᵉ : binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ) →
    ( map-coproductᵉ
        ( map-equivᵉ
          ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ)))
        ( map-equivᵉ
          ( equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ))) ∘ᵉ
      map-equivᵉ
        ( matching-correspondence-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
          (map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
            ( dᵉ)))) ~ᵉ
    map-equivᵉ (matching-correspondence-binary-coproduct-Decompositionᵉ dᵉ)
  matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
    dᵉ xᵉ =
    matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕ-helperᵉ
      ( dᵉ)
      ( xᵉ)
      ( value-map-into-Fin-Two-ℕ-eq-zero-or-oneᵉ
        ( map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ)
        ( xᵉ))

  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ ∘ᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ) ~ᵉ
    idᵉ
  is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ dᵉ =
    eq-equiv-binary-coproduct-Decompositionᵉ
      ( ( map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ ∘ᵉ
          map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
        ( dᵉ))
      ( dᵉ)
      ( equiv-left-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( dᵉ) ,ᵉ
        equiv-right-summand-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( dᵉ) ,ᵉ
        matching-correspondence-htpy-is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
        ( dᵉ))

  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    is-equivᵉ map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
  is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
      ( is-section-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)
      ( is-retraction-map-inv-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ)

  equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ :
    (Xᵉ → Finᵉ 2ᵉ) ≃ᵉ binary-coproduct-Decompositionᵉ l1ᵉ l1ᵉ Xᵉ
  pr1ᵉ equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ =
    map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
  pr2ᵉ equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ =
    is-equiv-map-equiv-binary-coproduct-Decomposition-map-into-Fin-Two-ℕᵉ
```