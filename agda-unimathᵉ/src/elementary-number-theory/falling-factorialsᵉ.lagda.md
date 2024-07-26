# Falling factorials

```agda
module elementary-number-theory.falling-factorialsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Idea

Theᵉ fallingᵉ factorialᵉ (n)\_mᵉ isᵉ theᵉ numberᵉ n(n-1)⋯(n-m+1ᵉ)

## Definition

```agda
falling-factorial-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
falling-factorial-ℕᵉ zero-ℕᵉ zero-ℕᵉ = 1
falling-factorial-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) = 0
falling-factorial-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = 1
falling-factorial-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) =
  (succ-ℕᵉ nᵉ) *ℕᵉ (falling-factorial-ℕᵉ nᵉ mᵉ)

{-ᵉ
Fin-falling-factorial-ℕᵉ :
  (nᵉ mᵉ : ℕᵉ) → Finᵉ (falling-factorial-ℕᵉ nᵉ mᵉ) ≃ᵉ (Finᵉ mᵉ ↪ᵉ Finᵉ nᵉ)
Fin-falling-factorial-ℕᵉ nᵉ mᵉ = {!!ᵉ}
-ᵉ}

{-ᵉ
Fin-falling-factorial-ℕᵉ :
  (nᵉ mᵉ : ℕᵉ) → Finᵉ (falling-factorial-ℕᵉ nᵉ mᵉ) ≃ᵉ (Finᵉ mᵉ ↪ᵉ Finᵉ nᵉ)
Fin-falling-factorial-ℕᵉ zero-ℕᵉ zero-ℕᵉ =
  equiv-is-contrᵉ
    ( is-contr-Fin-one-ℕᵉ)
    ( is-contr-equivᵉ
      ( is-embᵉ idᵉ)
      ( left-unit-law-Σ-is-contrᵉ
        ( universal-property-empty'ᵉ emptyᵉ)
        ( idᵉ))
      ( dependent-universal-property-empty'ᵉ
        ( λ xᵉ → (yᵉ : emptyᵉ) → is-equivᵉ (apᵉ idᵉ))))
Fin-falling-factorial-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) =
  equiv-is-emptyᵉ idᵉ (λ fᵉ → map-embᵉ fᵉ (inrᵉ starᵉ))
Fin-falling-factorial-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ =
  equiv-is-contrᵉ
    ( is-contr-Fin-one-ℕᵉ)
    ( is-contr-equivᵉ
      ( is-embᵉ ex-falsoᵉ)
      ( left-unit-law-Σ-is-contrᵉ
        ( universal-property-empty'ᵉ (Finᵉ (succ-ℕᵉ nᵉ)))
        ( ex-falsoᵉ))
      ( dependent-universal-property-empty'ᵉ
        ( λ xᵉ → (yᵉ : emptyᵉ) → is-equivᵉ (apᵉ ex-falsoᵉ))))
Fin-falling-factorial-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) =
  ( ( ( right-unit-law-Σ-is-contrᵉ
        { Bᵉ = λ fᵉ → is-decidableᵉ (fiberᵉ (map-embᵉ fᵉ) (inrᵉ starᵉ))}
        ( λ fᵉ →
          is-proof-irrelevant-is-propᵉ
            ( is-prop-is-decidableᵉ
              ( is-prop-map-is-embᵉ (is-emb-map-embᵉ fᵉ) (inrᵉ starᵉ)))
            ( is-decidable-Σ-Finᵉ
              ( λ xᵉ →
                has-decidable-equality-Finᵉ (map-embᵉ fᵉ xᵉ) (inrᵉ starᵉ))))) ∘eᵉ
      ( ( inv-equivᵉ
          ( left-distributive-Σ-coproductᵉ
            ( Finᵉ (succ-ℕᵉ mᵉ) ↪ᵉ Finᵉ (succ-ℕᵉ nᵉ))
            ( λ fᵉ → fiberᵉ (map-embᵉ fᵉ) (inrᵉ starᵉ))
            ( λ fᵉ → ¬ᵉ (fiberᵉ (map-embᵉ fᵉ) (inrᵉ starᵉ))))) ∘eᵉ
        {!!ᵉ})) ∘eᵉ
    ( equiv-coproductᵉ
      ( Fin-falling-factorial-ℕᵉ nᵉ mᵉ)
      ( Fin-falling-factorial-ℕᵉ nᵉ (succ-ℕᵉ mᵉ)))) ∘eᵉ
  ( Fin-add-ℕᵉ (falling-factorial-ℕᵉ nᵉ mᵉ) (falling-factorial-ℕᵉ nᵉ (succ-ℕᵉ mᵉ)))
-ᵉ}
```