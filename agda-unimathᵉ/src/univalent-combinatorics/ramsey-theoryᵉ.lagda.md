# Ramsey theory

```agda
module univalent-combinatorics.ramsey-theoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

```agda
coloringᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → UUᵉ lᵉ → UUᵉ lᵉ
coloringᵉ kᵉ Xᵉ = Xᵉ → Finᵉ kᵉ

full-subsetᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → Xᵉ → Propᵉ lzero
full-subsetᵉ Xᵉ xᵉ = unit-Propᵉ

subset-of-sizeᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → 𝔽ᵉ lᵉ → UUᵉ (lsuc lzero ⊔ lᵉ)
subset-of-sizeᵉ kᵉ Xᵉ =
  Σᵉ ( type-𝔽ᵉ Xᵉ → Propᵉ lzero)
    ( λ Pᵉ → has-cardinalityᵉ kᵉ (Σᵉ (type-𝔽ᵉ Xᵉ) (λ xᵉ → type-Propᵉ (Pᵉ xᵉ))))

is-ramsey-setᵉ :
  {lᵉ : Level} {kᵉ : ℕᵉ} (qᵉ : Finᵉ kᵉ → ℕᵉ) (rᵉ : ℕᵉ) (Aᵉ : 𝔽ᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
is-ramsey-setᵉ {lᵉ} {kᵉ} qᵉ rᵉ Aᵉ =
  (cᵉ : coloringᵉ kᵉ (subset-of-sizeᵉ rᵉ Aᵉ)) →
  Σᵉ ( Finᵉ kᵉ)
    ( λ iᵉ →
      Σᵉ ( subset-of-sizeᵉ (qᵉ iᵉ) Aᵉ)
        ( λ Pᵉ →
          (Qᵉ : subset-of-sizeᵉ rᵉ Aᵉ) →
          ((xᵉ : type-𝔽ᵉ Aᵉ) → type-Propᵉ ((pr1ᵉ Qᵉ) xᵉ) → type-Propᵉ ((pr1ᵉ Pᵉ) xᵉ)) →
          Idᵉ (cᵉ Qᵉ) iᵉ))
{-ᵉ
is-ramsey-set-empty-coloringᵉ : (rᵉ : ℕᵉ) → is-ramsey-setᵉ ex-falsoᵉ rᵉ empty-𝔽ᵉ
is-ramsey-set-empty-coloringᵉ zero-ℕᵉ cᵉ = {!!ᵉ}
is-ramsey-set-empty-coloringᵉ (succ-ℕᵉ rᵉ) cᵉ = {!!ᵉ}

is-ramsey-set-Fin-rᵉ :
  {kᵉ : ℕᵉ} (qᵉ : Finᵉ kᵉ → ℕᵉ) (rᵉ : ℕᵉ) → fiberᵉ qᵉ rᵉ → is-ramsey-setᵉ qᵉ rᵉ (Fin-𝔽ᵉ rᵉ)
is-ramsey-set-Fin-rᵉ qᵉ .(qᵉ iᵉ) (pairᵉ iᵉ reflᵉ) cᵉ =
  pairᵉ
    ( cᵉ Rᵉ)
    ( pairᵉ
      {!!ᵉ}
      {!!ᵉ})
    where
    Rᵉ : subset-of-sizeᵉ (qᵉ iᵉ) (Fin-𝔽ᵉ (qᵉ iᵉ))
    Rᵉ = pairᵉ
          ( full-subsetᵉ (Finᵉ (qᵉ iᵉ)))
          ( unit-trunc-Propᵉ (inv-equivᵉ right-unit-law-productᵉ))
    {-ᵉ
    ( pairᵉ
      ( pairᵉ ( full-subsetᵉ (Finᵉ {!!ᵉ}))
             ( unit-trunc-Propᵉ (inv-equivᵉ right-unit-law-productᵉ)))
      ( λ Qᵉ Hᵉ → {!!ᵉ}))
-ᵉ}
-ᵉ}
```