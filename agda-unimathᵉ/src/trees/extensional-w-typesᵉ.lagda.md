# Extensional W-types

```agda
module trees.extensional-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.sliceᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalent-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Aᵉ W-typeᵉ `𝕎ᵉ Aᵉ B`ᵉ isᵉ saidᵉ to beᵉ **extensional**ᵉ ifᵉ forᵉ anyᵉ twoᵉ elementsᵉ
`Sᵉ Tᵉ : 𝕎ᵉ Aᵉ B`ᵉ theᵉ inducedᵉ mapᵉ

```text
  Idᵉ Sᵉ Tᵉ → ((Uᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (Uᵉ ∈-𝕎ᵉ Sᵉ) ≃ᵉ (Uᵉ ∈-𝕎ᵉ Tᵉ))
```

isᵉ anᵉ equivalence.ᵉ

## Definition

### Extensional equality on W-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  extensional-Eq-eq-𝕎ᵉ :
    {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ ＝ᵉ yᵉ → (zᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (zᵉ ∈-𝕎ᵉ xᵉ) ≃ᵉ (zᵉ ∈-𝕎ᵉ yᵉ)
  extensional-Eq-eq-𝕎ᵉ reflᵉ zᵉ = id-equivᵉ

is-extensional-𝕎ᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-extensional-𝕎ᵉ Aᵉ Bᵉ =
  (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-equivᵉ (extensional-Eq-eq-𝕎ᵉ {xᵉ = xᵉ} {yᵉ})

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  Eq-ext-𝕎ᵉ : 𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Aᵉ Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-ext-𝕎ᵉ xᵉ yᵉ = (zᵉ : 𝕎ᵉ Aᵉ Bᵉ) → (zᵉ ∈-𝕎ᵉ xᵉ) ≃ᵉ (zᵉ ∈-𝕎ᵉ yᵉ)

  refl-Eq-ext-𝕎ᵉ : (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Eq-ext-𝕎ᵉ xᵉ xᵉ
  refl-Eq-ext-𝕎ᵉ xᵉ zᵉ = id-equivᵉ

  Eq-ext-eq-𝕎ᵉ : {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} → xᵉ ＝ᵉ yᵉ → Eq-ext-𝕎ᵉ xᵉ yᵉ
  Eq-ext-eq-𝕎ᵉ {xᵉ} reflᵉ = refl-Eq-ext-𝕎ᵉ xᵉ
```

## Properties

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  Eq-Eq-ext-𝕎ᵉ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (uᵉ vᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ vᵉ =
    (zᵉ : 𝕎ᵉ Aᵉ Bᵉ) → map-equivᵉ (uᵉ zᵉ) ~ᵉ map-equivᵉ (vᵉ zᵉ)

  refl-Eq-Eq-ext-𝕎ᵉ : (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (uᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ) → Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ uᵉ
  refl-Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ zᵉ = refl-htpyᵉ

  is-torsorial-Eq-Eq-ext-𝕎ᵉ :
    (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (uᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ) → is-torsorialᵉ (Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ)
  is-torsorial-Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ =
    is-torsorial-Eq-Πᵉ (λ zᵉ → is-torsorial-htpy-equivᵉ (uᵉ zᵉ))

  Eq-Eq-ext-eq-𝕎ᵉ :
    (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (uᵉ vᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ) → uᵉ ＝ᵉ vᵉ → Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ vᵉ
  Eq-Eq-ext-eq-𝕎ᵉ xᵉ yᵉ uᵉ .uᵉ reflᵉ = refl-Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ

  is-equiv-Eq-Eq-ext-eq-𝕎ᵉ :
    (xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ) (uᵉ vᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ) → is-equivᵉ (Eq-Eq-ext-eq-𝕎ᵉ xᵉ yᵉ uᵉ vᵉ)
  is-equiv-Eq-Eq-ext-eq-𝕎ᵉ xᵉ yᵉ uᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ)
      ( Eq-Eq-ext-eq-𝕎ᵉ xᵉ yᵉ uᵉ)

  eq-Eq-Eq-ext-𝕎ᵉ :
    {xᵉ yᵉ : 𝕎ᵉ Aᵉ Bᵉ} {uᵉ vᵉ : Eq-ext-𝕎ᵉ xᵉ yᵉ} → Eq-Eq-ext-𝕎ᵉ xᵉ yᵉ uᵉ vᵉ → uᵉ ＝ᵉ vᵉ
  eq-Eq-Eq-ext-𝕎ᵉ {xᵉ} {yᵉ} {uᵉ} {vᵉ} =
    map-inv-is-equivᵉ (is-equiv-Eq-Eq-ext-eq-𝕎ᵉ xᵉ yᵉ uᵉ vᵉ)

  equiv-total-Eq-ext-𝕎ᵉ :
    (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (Eq-ext-𝕎ᵉ xᵉ) ≃ᵉ Σᵉ Aᵉ (λ aᵉ → Bᵉ (shape-𝕎ᵉ xᵉ) ≃ᵉ Bᵉ aᵉ)
  equiv-total-Eq-ext-𝕎ᵉ (tree-𝕎ᵉ aᵉ fᵉ) =
    ( ( equiv-totᵉ
            ( λ xᵉ →
              ( ( right-unit-law-Σ-is-contrᵉ
                  ( λ eᵉ → is-torsorial-htpyᵉ (fᵉ ∘ᵉ map-inv-equivᵉ eᵉ))) ∘eᵉ
                ( equiv-totᵉ
                  ( λ eᵉ →
                    equiv-totᵉ
                      ( λ gᵉ →
                        equiv-Πᵉ
                          ( λ yᵉ → fᵉ (map-inv-equivᵉ eᵉ yᵉ) ＝ᵉ gᵉ yᵉ)
                          ( eᵉ)
                          ( λ yᵉ →
                            equiv-concatᵉ
                              ( apᵉ fᵉ (is-retraction-map-inv-equivᵉ eᵉ yᵉ))
                              ( gᵉ (map-equivᵉ eᵉ yᵉ))))))) ∘eᵉ
              ( ( equiv-left-swap-Σᵉ) ∘eᵉ
                ( equiv-totᵉ
                  ( λ gᵉ →
                    inv-equivᵉ (equiv-fam-equiv-equiv-sliceᵉ fᵉ gᵉ)))))) ∘eᵉ
          ( associative-Σᵉ
            ( Aᵉ)
            ( λ xᵉ → Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ)
            ( λ tᵉ → Eq-ext-𝕎ᵉ (tree-𝕎ᵉ aᵉ fᵉ) (tree-𝕎ᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ))))) ∘eᵉ
        ( equiv-Σᵉ
          ( λ (tᵉ : Σᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ → 𝕎ᵉ Aᵉ Bᵉ)) →
            Eq-ext-𝕎ᵉ (tree-𝕎ᵉ aᵉ fᵉ) (tree-𝕎ᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)))
          ( inv-equiv-structure-𝕎-Algᵉ)
          ( Hᵉ))
    where
    Hᵉ :
      ( zᵉ : 𝕎ᵉ Aᵉ (λ xᵉ → Bᵉ xᵉ)) →
      Eq-ext-𝕎ᵉ ( tree-𝕎ᵉ aᵉ fᵉ) zᵉ ≃ᵉ
      Eq-ext-𝕎ᵉ
        ( tree-𝕎ᵉ aᵉ fᵉ)
        ( tree-𝕎ᵉ
          ( pr1ᵉ (map-equivᵉ inv-equiv-structure-𝕎-Algᵉ zᵉ))
          ( pr2ᵉ (map-equivᵉ inv-equiv-structure-𝕎-Algᵉ zᵉ)))
    Hᵉ (tree-𝕎ᵉ bᵉ gᵉ) = id-equivᵉ

  is-torsorial-Eq-ext-is-univalent-𝕎ᵉ :
    is-univalentᵉ Bᵉ → (xᵉ : 𝕎ᵉ Aᵉ Bᵉ) → is-torsorialᵉ (Eq-ext-𝕎ᵉ xᵉ)
  is-torsorial-Eq-ext-is-univalent-𝕎ᵉ Hᵉ (tree-𝕎ᵉ aᵉ fᵉ) =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (λ xᵉ → Bᵉ aᵉ ≃ᵉ Bᵉ xᵉ))
      ( equiv-total-Eq-ext-𝕎ᵉ (tree-𝕎ᵉ aᵉ fᵉ))
      ( fundamental-theorem-id'ᵉ (λ xᵉ → equiv-trᵉ Bᵉ) (Hᵉ aᵉ))

  is-extensional-is-univalent-𝕎ᵉ :
    is-univalentᵉ Bᵉ → is-extensional-𝕎ᵉ Aᵉ Bᵉ
  is-extensional-is-univalent-𝕎ᵉ Hᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-ext-is-univalent-𝕎ᵉ Hᵉ xᵉ)
      ( λ yᵉ → extensional-Eq-eq-𝕎ᵉ {yᵉ = yᵉ})

  is-univalent-is-extensional-𝕎ᵉ :
    type-trunc-Propᵉ (𝕎ᵉ Aᵉ Bᵉ) → is-extensional-𝕎ᵉ Aᵉ Bᵉ → is-univalentᵉ Bᵉ
  is-univalent-is-extensional-𝕎ᵉ pᵉ Hᵉ xᵉ =
    apply-universal-property-trunc-Propᵉ pᵉ
      ( Π-Propᵉ Aᵉ (λ yᵉ → is-equiv-Propᵉ (λ (γᵉ : xᵉ ＝ᵉ yᵉ) → equiv-trᵉ Bᵉ γᵉ)))
      ( λ wᵉ →
        fundamental-theorem-idᵉ
          ( is-contr-equiv'ᵉ
            ( Σᵉ (𝕎ᵉ Aᵉ Bᵉ) (Eq-ext-𝕎ᵉ (tree-𝕎ᵉ xᵉ (λ yᵉ → wᵉ))))
            ( equiv-total-Eq-ext-𝕎ᵉ (tree-𝕎ᵉ xᵉ (λ yᵉ → wᵉ)))
            ( fundamental-theorem-id'ᵉ
              ( λ zᵉ → extensional-Eq-eq-𝕎ᵉ)
              ( Hᵉ (tree-𝕎ᵉ xᵉ (λ yᵉ → wᵉ)))))
          ( λ yᵉ → equiv-trᵉ Bᵉ {yᵉ = yᵉ}))
```