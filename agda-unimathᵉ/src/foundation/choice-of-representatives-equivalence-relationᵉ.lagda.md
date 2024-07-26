# Choice of representatives for an equivalence relation

```agda
module foundation.choice-of-representatives-equivalence-relationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-classesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Ifᵉ weᵉ canᵉ constructᵉ aᵉ choiceᵉ ofᵉ representativesᵉ forᵉ eachᵉ equivalenceᵉ class,ᵉ thenᵉ
weᵉ canᵉ constructᵉ theᵉ setᵉ quotientᵉ asᵉ aᵉ retractᵉ ofᵉ theᵉ originalᵉ type.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  is-choice-of-representativesᵉ :
    (Aᵉ → UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-choice-of-representativesᵉ Pᵉ =
    (aᵉ : Aᵉ) → is-contrᵉ (Σᵉ Aᵉ (λ xᵉ → Pᵉ xᵉ ×ᵉ sim-equivalence-relationᵉ Rᵉ aᵉ xᵉ))

  representativesᵉ :
    {Pᵉ : Aᵉ → UUᵉ l3ᵉ} → is-choice-of-representativesᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  representativesᵉ {Pᵉ} Hᵉ = Σᵉ Aᵉ Pᵉ

  class-representativesᵉ :
    {Pᵉ : Aᵉ → UUᵉ l3ᵉ} (Hᵉ : is-choice-of-representativesᵉ Pᵉ) →
    representativesᵉ Hᵉ → equivalence-classᵉ Rᵉ
  class-representativesᵉ Hᵉ aᵉ =
    classᵉ Rᵉ (pr1ᵉ aᵉ)

  abstract
    is-surjective-class-representativesᵉ :
      {Pᵉ : Aᵉ → UUᵉ l3ᵉ} (Hᵉ : is-choice-of-representativesᵉ Pᵉ) →
      is-surjectiveᵉ (class-representativesᵉ Hᵉ)
    is-surjective-class-representativesᵉ Hᵉ (pairᵉ Qᵉ Kᵉ) =
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( trunc-Propᵉ
          ( fiberᵉ (class-representativesᵉ Hᵉ) (pairᵉ Qᵉ Kᵉ)))
        ( λ (pairᵉ aᵉ φᵉ) →
          unit-trunc-Propᵉ
            ( pairᵉ
              ( pairᵉ (pr1ᵉ (centerᵉ (Hᵉ aᵉ))) (pr1ᵉ (pr2ᵉ (centerᵉ (Hᵉ aᵉ)))))
              ( ( apply-effectiveness-class'ᵉ Rᵉ
                  ( symmetric-equivalence-relationᵉ Rᵉ _ _
                    ( pr2ᵉ (pr2ᵉ (centerᵉ (Hᵉ aᵉ)))))) ∙ᵉ
                ( eq-class-equivalence-classᵉ Rᵉ
                  ( pairᵉ Qᵉ Kᵉ)
                  ( backward-implicationᵉ
                    ( φᵉ aᵉ)
                    ( refl-equivalence-relationᵉ Rᵉ _))))))

  abstract
    is-emb-class-representativesᵉ :
      {Pᵉ : Aᵉ → UUᵉ l3ᵉ} (Hᵉ : is-choice-of-representativesᵉ Pᵉ) →
      is-embᵉ (class-representativesᵉ Hᵉ)
    is-emb-class-representativesᵉ {Pᵉ} Hᵉ (pairᵉ aᵉ pᵉ) =
      fundamental-theorem-idᵉ
        ( is-contr-equivᵉ
          ( Σᵉ Aᵉ (λ xᵉ → Pᵉ xᵉ ×ᵉ sim-equivalence-relationᵉ Rᵉ aᵉ xᵉ))
          ( ( associative-Σᵉ Aᵉ Pᵉ (λ zᵉ → sim-equivalence-relationᵉ Rᵉ aᵉ (pr1ᵉ zᵉ))) ∘eᵉ
            ( equiv-totᵉ
              ( λ tᵉ →
                is-effective-classᵉ Rᵉ aᵉ (pr1ᵉ tᵉ))))
          ( Hᵉ aᵉ))
        ( λ yᵉ →
          apᵉ (class-representativesᵉ Hᵉ) {pairᵉ aᵉ pᵉ} {yᵉ})

  abstract
    is-equiv-class-representativesᵉ :
      {Pᵉ : Aᵉ → UUᵉ l3ᵉ} (Hᵉ : is-choice-of-representativesᵉ Pᵉ) →
      is-equivᵉ (class-representativesᵉ Hᵉ)
    is-equiv-class-representativesᵉ Hᵉ =
      is-equiv-is-emb-is-surjectiveᵉ
        ( is-surjective-class-representativesᵉ Hᵉ)
        ( is-emb-class-representativesᵉ Hᵉ)

  equiv-equivalence-class-representativesᵉ :
    {Pᵉ : Aᵉ → UUᵉ l3ᵉ} (Hᵉ : is-choice-of-representativesᵉ Pᵉ) →
    representativesᵉ Hᵉ ≃ᵉ equivalence-classᵉ Rᵉ
  pr1ᵉ (equiv-equivalence-class-representativesᵉ Hᵉ) = class-representativesᵉ Hᵉ
  pr2ᵉ (equiv-equivalence-class-representativesᵉ Hᵉ) =
    is-equiv-class-representativesᵉ Hᵉ
```