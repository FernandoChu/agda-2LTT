# Multiplication of matrices

```agda
module linear-algebra.multiplication-matricesᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Definition

### Multiplication of matrices

```agda
{-ᵉ
mul-vector-matrixᵉ : {lᵉ : Level} → {Kᵉ : UUᵉ lᵉ} → {mᵉ nᵉ : ℕᵉ} →
                     (Kᵉ → Kᵉ → Kᵉ) → (Kᵉ → Kᵉ → Kᵉ) → Kᵉ →
                     vecᵉ Kᵉ mᵉ → Matᵉ Kᵉ mᵉ nᵉ → vecᵉ Kᵉ nᵉ
mul-vector-matrixᵉ _ _ zeroᵉ empty-vecᵉ empty-vecᵉ = diagonal-productᵉ zeroᵉ
mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ (xᵉ ∷ᵉ xsᵉ) (vᵉ ∷ᵉ vsᵉ) =
  add-vecᵉ addKᵉ (mul-scalar-vectorᵉ mulKᵉ xᵉ vᵉ)
               (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ xsᵉ vsᵉ)

mul-Matᵉ : {l'ᵉ : Level} → {Kᵉ : UUᵉ l'ᵉ} → {lᵉ mᵉ nᵉ : ℕᵉ} →
          (Kᵉ → Kᵉ → Kᵉ) → (Kᵉ → Kᵉ → Kᵉ) → Kᵉ →
          Matᵉ Kᵉ lᵉ mᵉ → Matᵉ Kᵉ mᵉ nᵉ → Matᵉ Kᵉ lᵉ nᵉ
mul-Matᵉ _ _ zeroᵉ empty-vecᵉ _ = empty-vecᵉ
mul-Matᵉ mulKᵉ addKᵉ zeroᵉ (vᵉ ∷ᵉ vsᵉ) mᵉ =
  mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ vᵉ mᵉ
    ∷ᵉ mul-Matᵉ mulKᵉ addKᵉ zeroᵉ vsᵉ mᵉ
-ᵉ}
```

## Properties

```agda
{-ᵉ
mul-transposeᵉ :
  {lᵉ : Level} → {Kᵉ : UUᵉ lᵉ} → {mᵉ nᵉ pᵉ : ℕᵉ} →
  {addKᵉ : Kᵉ → Kᵉ → Kᵉ} {mulKᵉ : Kᵉ → Kᵉ → Kᵉ} {zeroᵉ : Kᵉ} →
  ((xᵉ yᵉ : Kᵉ) → Idᵉ (mulKᵉ xᵉ yᵉ) (mulKᵉ yᵉ xᵉ)) →
  (aᵉ : Matᵉ Kᵉ mᵉ nᵉ) → (bᵉ : Matᵉ Kᵉ nᵉ pᵉ) →
  Idᵉ
    (transposeᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ aᵉ bᵉ))
    (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ (transposeᵉ bᵉ) (transposeᵉ aᵉ))
mul-transposeᵉ mulK-commᵉ empty-vecᵉ bᵉ = {!!ᵉ}
mul-transposeᵉ mulK-commᵉ (aᵉ ∷ᵉ asᵉ) bᵉ = {!!ᵉ}
-ᵉ}
```

## Properties of Matrix Multiplication

-ᵉ distributiveᵉ lawsᵉ (incompleteᵉ)
-ᵉ associativityᵉ (TODOᵉ)
-ᵉ identityᵉ (TODOᵉ)

```agda
{-ᵉ
module _
  {lᵉ : Level}
  {Kᵉ : UUᵉ lᵉ}
  {addKᵉ : Kᵉ → Kᵉ → Kᵉ}
  {mulKᵉ : Kᵉ → Kᵉ → Kᵉ}
  {zeroᵉ : Kᵉ}
  where

  left-distributive-vector-matrixᵉ :
    {nᵉ mᵉ : ℕᵉ} →
    ({lᵉ : ℕᵉ} →  Idᵉ (diagonal-productᵉ {nᵉ = lᵉ} zeroᵉ)
    (add-vecᵉ addKᵉ (diagonal-productᵉ zeroᵉ) (diagonal-productᵉ zeroᵉ))) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → (Idᵉ (mulKᵉ xᵉ (addKᵉ yᵉ zᵉ)) (addKᵉ (mulKᵉ xᵉ yᵉ) (mulKᵉ xᵉ zᵉ)))) →
    ((xᵉ yᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ yᵉ) (addKᵉ yᵉ xᵉ)) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ (addKᵉ yᵉ zᵉ)) (addKᵉ (addKᵉ xᵉ yᵉ) zᵉ)) →
    (aᵉ : vecᵉ Kᵉ nᵉ) (bᵉ : Matᵉ Kᵉ nᵉ mᵉ) (cᵉ : Matᵉ Kᵉ nᵉ mᵉ) →
    Idᵉ (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ aᵉ (add-Matᵉ addKᵉ bᵉ cᵉ))
      (add-vecᵉ addKᵉ (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ aᵉ bᵉ)
                    (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ aᵉ cᵉ))
  left-distributive-vector-matrixᵉ id-vecᵉ _ _ _ empty-vecᵉ empty-vecᵉ empty-vecᵉ =
    id-vecᵉ
  left-distributive-vector-matrixᵉ
    id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ (aᵉ ∷ᵉ asᵉ) (r1ᵉ ∷ᵉ r1sᵉ) (r2ᵉ ∷ᵉ r2sᵉ) =
      apᵉ
        ( λ rᵉ →
          add-vecᵉ addKᵉ rᵉ
            (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ asᵉ (add-Matᵉ addKᵉ r1sᵉ r2sᵉ)))
        (left-distributive-scalar-vectorᵉ {zeroᵉ = zeroᵉ} k-distrᵉ aᵉ r1ᵉ r2ᵉ)
        ∙ᵉ (apᵉ (λ rᵉ → add-vecᵉ addKᵉ (add-vecᵉ addKᵉ (map-vecᵉ (mulKᵉ aᵉ) r1ᵉ)
                                  (mul-scalar-vectorᵉ mulKᵉ aᵉ r2ᵉ)) rᵉ)
              (left-distributive-vector-matrixᵉ
                id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ asᵉ r1sᵉ r2sᵉ)
          ∙ᵉ lemma-shuffleᵉ)
    where
    lemma-shuffleᵉ : {nᵉ : ℕᵉ} →
                    {xᵉ yᵉ zᵉ wᵉ : vecᵉ Kᵉ nᵉ} →
                    Idᵉ (add-vecᵉ addKᵉ (add-vecᵉ addKᵉ xᵉ yᵉ) (add-vecᵉ addKᵉ zᵉ wᵉ))
                       (add-vecᵉ addKᵉ (add-vecᵉ addKᵉ xᵉ zᵉ) (add-vecᵉ addKᵉ yᵉ wᵉ))
    lemma-shuffleᵉ {xᵉ = xᵉ} {yᵉ = yᵉ} {zᵉ = zᵉ} {wᵉ = wᵉ} =
      associative-add-vectorsᵉ {zeroᵉ = zeroᵉ} addK-associativeᵉ (add-vecᵉ addKᵉ xᵉ yᵉ) zᵉ wᵉ
        ∙ᵉ (commutative-add-vectorsᵉ
            {zeroᵉ = zeroᵉ} addK-commᵉ (add-vecᵉ addKᵉ (add-vecᵉ addKᵉ xᵉ yᵉ) zᵉ) wᵉ
        ∙ᵉ (associative-add-vectorsᵉ
            {zeroᵉ = zeroᵉ} addK-associativeᵉ wᵉ (add-vecᵉ addKᵉ xᵉ yᵉ) zᵉ
        ∙ᵉ (apᵉ (λ vᵉ → add-vecᵉ addKᵉ (add-vecᵉ addKᵉ wᵉ vᵉ) zᵉ)
              (commutative-add-vectorsᵉ {zeroᵉ = zeroᵉ} addK-commᵉ xᵉ yᵉ)
        ∙ᵉ (apᵉ (λ vᵉ → add-vecᵉ addKᵉ vᵉ zᵉ)
              (associative-add-vectorsᵉ {zeroᵉ = zeroᵉ} addK-associativeᵉ wᵉ yᵉ xᵉ)
        ∙ᵉ (apᵉ (λ vᵉ → add-vecᵉ addKᵉ (add-vecᵉ addKᵉ vᵉ xᵉ) zᵉ)
              (commutative-add-vectorsᵉ {zeroᵉ = zeroᵉ} addK-commᵉ wᵉ yᵉ)
        ∙ᵉ (invᵉ (associative-add-vectorsᵉ
            {zeroᵉ = zeroᵉ} addK-associativeᵉ (add-vecᵉ addKᵉ yᵉ wᵉ) xᵉ zᵉ)
        ∙ᵉ commutative-add-vectorsᵉ
            {zeroᵉ = zeroᵉ} addK-commᵉ (add-vecᵉ addKᵉ yᵉ wᵉ) (add-vecᵉ addKᵉ xᵉ zᵉ)))))))

  left-distributive-matricesᵉ :
    {nᵉ mᵉ pᵉ : ℕᵉ} →
    ({lᵉ : ℕᵉ} →
      Idᵉ
        (diagonal-productᵉ {nᵉ = lᵉ} zeroᵉ)
        (add-vecᵉ addKᵉ (diagonal-productᵉ zeroᵉ) (diagonal-productᵉ zeroᵉ))) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → (Idᵉ (mulKᵉ xᵉ (addKᵉ yᵉ zᵉ)) (addKᵉ (mulKᵉ xᵉ yᵉ) (mulKᵉ xᵉ zᵉ)))) →
    ((xᵉ yᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ yᵉ) (addKᵉ yᵉ xᵉ)) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ (addKᵉ yᵉ zᵉ)) (addKᵉ (addKᵉ xᵉ yᵉ) zᵉ)) →
    (aᵉ : Matᵉ Kᵉ mᵉ nᵉ) (bᵉ : Matᵉ Kᵉ nᵉ pᵉ) (cᵉ : Matᵉ Kᵉ nᵉ pᵉ) →
    Idᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ aᵉ (add-Matᵉ addKᵉ bᵉ cᵉ))
       (add-Matᵉ addKᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ aᵉ bᵉ)
                     (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ aᵉ cᵉ))
  left-distributive-matricesᵉ _ _ _ _ empty-vecᵉ _ _ = reflᵉ
  left-distributive-matricesᵉ id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ (aᵉ ∷ᵉ asᵉ) bᵉ cᵉ =
    (apᵉ (λ rᵉ → rᵉ ∷ᵉ mul-Matᵉ mulKᵉ addKᵉ zeroᵉ asᵉ (add-Matᵉ addKᵉ bᵉ cᵉ))
        (left-distributive-vector-matrixᵉ
          id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ aᵉ bᵉ cᵉ))
      ∙ᵉ apᵉ (_∷ᵉ_ (add-vecᵉ addKᵉ (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ aᵉ bᵉ)
                              (mul-vector-matrixᵉ mulKᵉ addKᵉ zeroᵉ aᵉ cᵉ)))
          (left-distributive-matricesᵉ
            id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ asᵉ bᵉ cᵉ)
-ᵉ}

{-ᵉ TODOᵉ: rightᵉ distributivityᵉ
  right-distributive-matricesᵉ :
    {nᵉ mᵉ pᵉ : ℕᵉ} →
    ({lᵉ : ℕᵉ} →
      Idᵉ
        (diagonal-productᵉ {nᵉ = lᵉ} zeroᵉ)
        (add-vecᵉ addKᵉ (diagonal-productᵉ zeroᵉ) (diagonal-productᵉ zeroᵉ))) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → (Idᵉ (mulKᵉ (addKᵉ xᵉ yᵉ) zᵉ) (addKᵉ (mulKᵉ xᵉ zᵉ) (mulKᵉ yᵉ zᵉ)))) →
    ((xᵉ yᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ yᵉ) (addKᵉ yᵉ xᵉ)) →
    ((xᵉ yᵉ zᵉ : Kᵉ) → Idᵉ (addKᵉ xᵉ (addKᵉ yᵉ zᵉ)) (addKᵉ (addKᵉ xᵉ yᵉ) zᵉ)) →
    (bᵉ : Matᵉ Kᵉ nᵉ pᵉ) (cᵉ : Matᵉ Kᵉ nᵉ pᵉ) (dᵉ : Matᵉ Kᵉ pᵉ mᵉ) →
    Idᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ (add-Matᵉ addKᵉ bᵉ cᵉ) dᵉ)
       (add-Matᵉ addKᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ bᵉ dᵉ)
                     (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ cᵉ dᵉ))
  right-distributive-matricesᵉ _ _ _ _ empty-vecᵉ empty-vecᵉ _ = reflᵉ
  right-distributive-matricesᵉ
    {pᵉ = .zero-ℕᵉ}
    id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ (bᵉ ∷ᵉ bsᵉ) (cᵉ ∷ᵉ csᵉ) empty-vecᵉ =
    {!!ᵉ}
  right-distributive-matricesᵉ
    id-vecᵉ k-distrᵉ addK-commᵉ addK-associativeᵉ (bᵉ ∷ᵉ bsᵉ) (cᵉ ∷ᵉ csᵉ) (dᵉ ∷ᵉ dsᵉ) =
    {!!ᵉ}
  --ᵉ thisᵉ mightᵉ alsoᵉ needᵉ aᵉ proofᵉ thatᵉ zeroᵉ isᵉ theᵉ additiveᵉ identityᵉ

  TODOᵉ: associativityᵉ
  associative-mul-matricesᵉ :
  {lᵉ : Level} {Kᵉ : UUᵉ lᵉ} {nᵉ mᵉ pᵉ qᵉ : ℕᵉ} →
  {addKᵉ : Kᵉ → Kᵉ → Kᵉ} {mulKᵉ : Kᵉ → Kᵉ → Kᵉ} {zeroᵉ : Kᵉ} →
  (xᵉ : Matᵉ Kᵉ mᵉ nᵉ) → (yᵉ : Matᵉ Kᵉ nᵉ pᵉ) → (zᵉ : Matᵉ Kᵉ pᵉ qᵉ) →
  Idᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ xᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ yᵉ zᵉ))
  (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ (mul-Matᵉ mulKᵉ addKᵉ zeroᵉ xᵉ yᵉ) zᵉ)
  associative-mul-matricesᵉ xᵉ yᵉ zᵉ = {!!ᵉ}
-ᵉ}
```