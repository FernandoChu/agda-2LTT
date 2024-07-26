# The closed modalities

```agda
module orthogonal-factorization-systems.closed-modalitiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.modal-operatorsᵉ
open import orthogonal-factorization-systems.reflective-subuniversesᵉ
open import orthogonal-factorization-systems.sigma-closed-reflective-subuniversesᵉ

open import synthetic-homotopy-theory.joins-of-typesᵉ
```

</details>

## Idea

Givenᵉ anyᵉ [proposition](foundation.propositions.mdᵉ) `Q`,ᵉ theᵉ
[joinᵉ operation](synthetic-homotopy-theory.joins-of-types.mdᵉ) `_*ᵉ Q`ᵉ definesᵉ aᵉ
[higherᵉ modality](orthogonal-factorization-systems.higher-modalities.md).ᵉ Weᵉ
callᵉ theseᵉ theᵉ **closedᵉ modalities**.ᵉ

## Definition

```agda
operator-closed-modalityᵉ :
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) → operator-modalityᵉ lᵉ (lᵉ ⊔ lQᵉ)
operator-closed-modalityᵉ Qᵉ Aᵉ = Aᵉ *ᵉ type-Propᵉ Qᵉ

unit-closed-modalityᵉ :
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) → unit-modalityᵉ (operator-closed-modalityᵉ {lᵉ} Qᵉ)
unit-closed-modalityᵉ Qᵉ = inl-joinᵉ

is-closed-modalᵉ :
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ) → UUᵉ lᵉ → Propᵉ (lᵉ ⊔ lQᵉ)
pr1ᵉ (is-closed-modalᵉ Qᵉ Bᵉ) = type-Propᵉ Qᵉ → is-contrᵉ Bᵉ
pr2ᵉ (is-closed-modalᵉ Qᵉ Bᵉ) = is-prop-function-typeᵉ is-property-is-contrᵉ
```

## Properties

### The closed modalities define Σ-closed reflective subuniverses

```agda
module _
  {lᵉ lQᵉ : Level} (Qᵉ : Propᵉ lQᵉ)
  where

  is-reflective-subuniverse-closed-modalityᵉ :
    is-reflective-subuniverseᵉ {lᵉ ⊔ lQᵉ} (is-closed-modalᵉ Qᵉ)
  pr1ᵉ is-reflective-subuniverse-closed-modalityᵉ =
    operator-closed-modalityᵉ {lᵉ ⊔ lQᵉ} Qᵉ
  pr1ᵉ (pr2ᵉ is-reflective-subuniverse-closed-modalityᵉ) =
    unit-closed-modalityᵉ Qᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ is-reflective-subuniverse-closed-modalityᵉ)) Aᵉ qᵉ =
    right-zero-law-join-is-contrᵉ
      ( Aᵉ)
      ( type-Propᵉ Qᵉ)
      ( is-proof-irrelevant-is-propᵉ (is-prop-type-Propᵉ Qᵉ) qᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ is-reflective-subuniverse-closed-modalityᵉ)) Bᵉ Aᵉ is-modal-Bᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ fᵉ →
        is-contr-equivᵉ
          ( Σᵉ (Aᵉ → Bᵉ) (_＝ᵉ fᵉ))
          ( equiv-Σ-equiv-baseᵉ
            ( _＝ᵉ fᵉ)
            ( right-unit-law-Σ-is-contrᵉ
              ( λ f'ᵉ →
                is-contr-Σᵉ
                  ( is-contr-Πᵉ is-modal-Bᵉ)
                  ( centerᵉ ∘ᵉ is-modal-Bᵉ)
                  ( is-contr-Πᵉ
                    ( λ (aᵉ ,ᵉ qᵉ) →
                      is-prop-is-contrᵉ
                        ( is-modal-Bᵉ qᵉ)
                        ( f'ᵉ aᵉ)
                        ( centerᵉ (is-modal-Bᵉ qᵉ))))) ∘eᵉ
              ( equiv-up-joinᵉ Bᵉ)))
          ( is-torsorial-Id'ᵉ fᵉ))

  reflective-subuniverse-closed-modalityᵉ :
    reflective-subuniverseᵉ (lᵉ ⊔ lQᵉ) (lᵉ ⊔ lQᵉ)
  pr1ᵉ reflective-subuniverse-closed-modalityᵉ =
    is-closed-modalᵉ Qᵉ
  pr2ᵉ reflective-subuniverse-closed-modalityᵉ =
    is-reflective-subuniverse-closed-modalityᵉ

  is-closed-under-Σ-reflective-subuniverse-closed-modalityᵉ :
    is-closed-under-Σ-reflective-subuniverseᵉ
      ( reflective-subuniverse-closed-modalityᵉ)
  is-closed-under-Σ-reflective-subuniverse-closed-modalityᵉ Aᵉ Bᵉ qᵉ =
    is-contr-Σᵉ
      ( pr2ᵉ Aᵉ qᵉ)
      ( centerᵉ (pr2ᵉ Aᵉ qᵉ))
      ( pr2ᵉ (Bᵉ (centerᵉ (pr2ᵉ Aᵉ qᵉ))) qᵉ)

  closed-under-Σ-reflective-subuniverse-closed-modalityᵉ :
    closed-under-Σ-reflective-subuniverseᵉ (lᵉ ⊔ lQᵉ) (lᵉ ⊔ lQᵉ)
  pr1ᵉ closed-under-Σ-reflective-subuniverse-closed-modalityᵉ =
    reflective-subuniverse-closed-modalityᵉ
  pr2ᵉ closed-under-Σ-reflective-subuniverse-closed-modalityᵉ =
    is-closed-under-Σ-reflective-subuniverse-closed-modalityᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ RSS20ᵉ}}