# Powers of two

```agda
module elementary-number-theory.powers-of-twoᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ
open import elementary-number-theory.strong-induction-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-typesᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
```

</details>

## Idea

Anyᵉ naturalᵉ numberᵉ `x`ᵉ canᵉ beᵉ writtenᵉ asᵉ `(2^u(2v-1))-1`ᵉ forᵉ someᵉ pairᵉ ofᵉ
naturalᵉ numbersᵉ `(uᵉ ,ᵉ v)`ᵉ

```agda
pair-expansionᵉ : ℕᵉ → UUᵉ lzero
pair-expansionᵉ nᵉ =
  Σᵉ (ℕᵉ ×ᵉ ℕᵉ)
    ( λ pᵉ →
      ( (exp-ℕᵉ 2 (pr1ᵉ pᵉ)) *ℕᵉ (succ-ℕᵉ ((pr2ᵉ pᵉ) *ℕᵉ 2ᵉ))) ＝ᵉ
        succ-ℕᵉ nᵉ)

is-nonzero-pair-expansionᵉ :
  (uᵉ vᵉ : ℕᵉ) →
  is-nonzero-ℕᵉ ((exp-ℕᵉ 2 uᵉ) *ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ)))
is-nonzero-pair-expansionᵉ uᵉ vᵉ =
  is-nonzero-mul-ℕᵉ _ _
    ( is-nonzero-exp-ℕᵉ 2 uᵉ is-nonzero-two-ℕᵉ)
    ( is-nonzero-succ-ℕᵉ _)

abstract
  has-pair-expansion-is-even-or-oddᵉ :
    (nᵉ : ℕᵉ) → is-even-ℕᵉ nᵉ +ᵉ is-odd-ℕᵉ nᵉ → pair-expansionᵉ nᵉ
  has-pair-expansion-is-even-or-oddᵉ nᵉ =
    strong-ind-ℕᵉ
    ( λ mᵉ → (is-even-ℕᵉ mᵉ +ᵉ is-odd-ℕᵉ mᵉ) → (pair-expansionᵉ mᵉ))
    ( λ xᵉ → (0ᵉ ,ᵉ 0ᵉ) ,ᵉ reflᵉ)
    ( λ kᵉ fᵉ →
      ( λ where
        ( inlᵉ xᵉ) →
          ( let sᵉ = has-odd-expansion-is-oddᵉ kᵉ (is-odd-is-even-succ-ℕᵉ kᵉ xᵉ)
            in
              pairᵉ
                ( 0 ,ᵉ (succ-ℕᵉ (pr1ᵉ sᵉ)))
                ( ( apᵉ ((succ-ℕᵉ ∘ᵉ succ-ℕᵉ) ∘ᵉ succ-ℕᵉ) (left-unit-law-add-ℕᵉ _)) ∙ᵉ
                  ( ( apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ) (pr2ᵉ sᵉ)))))
        ( inrᵉ xᵉ) →
          ( let eᵉ : is-even-ℕᵉ kᵉ
                eᵉ = is-even-is-odd-succ-ℕᵉ kᵉ xᵉ

                tᵉ : (pr1ᵉ eᵉ) ≤-ℕᵉ kᵉ
                tᵉ = leq-quotient-div-ℕ'ᵉ 2 kᵉ is-nonzero-two-ℕᵉ eᵉ

                sᵉ : (pair-expansionᵉ (pr1ᵉ eᵉ))
                sᵉ = fᵉ (pr1ᵉ eᵉ) tᵉ (is-decidable-is-even-ℕᵉ (pr1ᵉ eᵉ))
            in
              pairᵉ
                ( succ-ℕᵉ (pr1ᵉ (pr1ᵉ sᵉ)) ,ᵉ pr2ᵉ (pr1ᵉ sᵉ))
                ( ( apᵉ
                    ( _*ℕᵉ (succ-ℕᵉ ((pr2ᵉ (pr1ᵉ sᵉ)) *ℕᵉ 2ᵉ)))
                    ( commutative-mul-ℕᵉ (exp-ℕᵉ 2 (pr1ᵉ (pr1ᵉ sᵉ))) 2ᵉ)) ∙ᵉ
                  ( ( associative-mul-ℕᵉ 2
                      ( exp-ℕᵉ 2 (pr1ᵉ (pr1ᵉ sᵉ)))
                      ( succ-ℕᵉ ((pr2ᵉ (pr1ᵉ sᵉ)) *ℕᵉ 2ᵉ))) ∙ᵉ
                    ( ( apᵉ (2ᵉ *ℕᵉ_) (pr2ᵉ sᵉ)) ∙ᵉ
                      ( ( apᵉ succ-ℕᵉ
                          ( left-successor-law-add-ℕᵉ (0ᵉ +ℕᵉ (pr1ᵉ eᵉ)) (pr1ᵉ eᵉ))) ∙ᵉ
                        ( ( apᵉ
                            ( succ-ℕᵉ ∘ᵉ succ-ℕᵉ)
                            ( apᵉ (_+ℕᵉ (pr1ᵉ eᵉ)) (left-unit-law-add-ℕᵉ (pr1ᵉ eᵉ)))) ∙ᵉ
                          ( ( apᵉ
                              ( succ-ℕᵉ ∘ᵉ succ-ℕᵉ)
                              ( invᵉ (right-two-law-mul-ℕᵉ (pr1ᵉ eᵉ)))) ∙ᵉ
                              ( ( apᵉ (succ-ℕᵉ ∘ᵉ succ-ℕᵉ) (pr2ᵉ eᵉ))))))))))))
    ( nᵉ)

has-pair-expansionᵉ : (nᵉ : ℕᵉ) → pair-expansionᵉ nᵉ
has-pair-expansionᵉ nᵉ =
  has-pair-expansion-is-even-or-oddᵉ nᵉ (is-decidable-is-even-ℕᵉ nᵉ)
```

### If `(u , v)` and `(u' , v')` are the pairs corresponding the same number `x`, then `u ＝ u'` and `v ＝ v'`

```agda
is-pair-expansion-uniqueᵉ :
  (uᵉ u'ᵉ vᵉ v'ᵉ : ℕᵉ) →
  ((exp-ℕᵉ 2 uᵉ) *ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ))) ＝ᵉ
    ((exp-ℕᵉ 2 u'ᵉ) *ℕᵉ (succ-ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ))) →
  (uᵉ ＝ᵉ u'ᵉ) ×ᵉ (vᵉ ＝ᵉ v'ᵉ)
is-pair-expansion-uniqueᵉ zero-ℕᵉ zero-ℕᵉ vᵉ v'ᵉ pᵉ =
  ( pairᵉ reflᵉ
    ( is-injective-right-mul-ℕᵉ 2 is-nonzero-two-ℕᵉ
      ( is-injective-left-add-ℕᵉ 0 (is-injective-succ-ℕᵉ pᵉ))))
is-pair-expansion-uniqueᵉ zero-ℕᵉ (succ-ℕᵉ u'ᵉ) vᵉ v'ᵉ pᵉ =
  ex-falsoᵉ (sᵉ tᵉ)
  where
  sᵉ : is-odd-ℕᵉ (succ-ℕᵉ (0ᵉ +ℕᵉ (vᵉ *ℕᵉ 2ᵉ)))
  sᵉ = is-odd-has-odd-expansionᵉ _
    ( vᵉ ,ᵉ apᵉ succ-ℕᵉ (invᵉ (left-unit-law-add-ℕᵉ _)))
  tᵉ : is-even-ℕᵉ (succ-ℕᵉ (0ᵉ +ℕᵉ (vᵉ *ℕᵉ 2ᵉ)))
  tᵉ = trᵉ is-even-ℕᵉ (invᵉ pᵉ) (div-mul-ℕ'ᵉ _ 2 _ ((exp-ℕᵉ 2 u'ᵉ) ,ᵉ reflᵉ))
is-pair-expansion-uniqueᵉ (succ-ℕᵉ uᵉ) zero-ℕᵉ vᵉ v'ᵉ pᵉ =
  ex-falsoᵉ (sᵉ tᵉ)
  where
  sᵉ : is-odd-ℕᵉ (succ-ℕᵉ (0ᵉ +ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))
  sᵉ = is-odd-has-odd-expansionᵉ _
    ( v'ᵉ ,ᵉ apᵉ succ-ℕᵉ (invᵉ (left-unit-law-add-ℕᵉ _)))
  tᵉ : is-even-ℕᵉ (succ-ℕᵉ (0ᵉ +ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))
  tᵉ = trᵉ is-even-ℕᵉ pᵉ (div-mul-ℕ'ᵉ _ 2 _ ((exp-ℕᵉ 2 uᵉ) ,ᵉ reflᵉ))
is-pair-expansion-uniqueᵉ (succ-ℕᵉ uᵉ) (succ-ℕᵉ u'ᵉ) vᵉ v'ᵉ pᵉ =
  puᵉ ,ᵉ pvᵉ
  where
  qᵉ :
    ((exp-ℕᵉ 2 uᵉ) *ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ))) ＝ᵉ
      ((exp-ℕᵉ 2 u'ᵉ) *ℕᵉ (succ-ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))
  qᵉ = is-injective-left-mul-ℕᵉ 2 is-nonzero-two-ℕᵉ
    ( invᵉ (associative-mul-ℕᵉ 2 (exp-ℕᵉ 2 uᵉ) (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ))) ∙ᵉ
    ( ( apᵉ (_*ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ)))
      ( commutative-mul-ℕᵉ 2 (exp-ℕᵉ 2 uᵉ))) ∙ᵉ
    ( ( pᵉ) ∙ᵉ
    ( ( apᵉ (_*ℕᵉ (succ-ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))
      ( commutative-mul-ℕᵉ (exp-ℕᵉ 2 u'ᵉ) 2ᵉ)) ∙ᵉ
    ( associative-mul-ℕᵉ 2 (exp-ℕᵉ 2 u'ᵉ) (succ-ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))))))
  puᵉ : (succ-ℕᵉ uᵉ) ＝ᵉ (succ-ℕᵉ u'ᵉ)
  puᵉ = apᵉ succ-ℕᵉ (pr1ᵉ (is-pair-expansion-uniqueᵉ uᵉ u'ᵉ vᵉ v'ᵉ qᵉ))
  pvᵉ : vᵉ ＝ᵉ v'ᵉ
  pvᵉ = pr2ᵉ (is-pair-expansion-uniqueᵉ uᵉ u'ᵉ vᵉ v'ᵉ qᵉ)
```

Aᵉ pairingᵉ functionᵉ isᵉ aᵉ bijectionᵉ betweenᵉ `ℕᵉ ×ᵉ ℕ`ᵉ andᵉ `ℕ`.ᵉ

## Definition

```agda
pairing-mapᵉ : ℕᵉ ×ᵉ ℕᵉ → ℕᵉ
pairing-mapᵉ (uᵉ ,ᵉ vᵉ) =
  pr1ᵉ (is-successor-is-nonzero-ℕᵉ (is-nonzero-pair-expansionᵉ uᵉ vᵉ))
```

### Pairing function is split surjective

```agda
is-split-surjective-pairing-mapᵉ : is-split-surjectiveᵉ pairing-mapᵉ
is-split-surjective-pairing-mapᵉ nᵉ =
  (uᵉ ,ᵉ vᵉ) ,ᵉ is-injective-succ-ℕᵉ (qᵉ ∙ᵉ sᵉ)
  where
  uᵉ = pr1ᵉ (pr1ᵉ (has-pair-expansionᵉ nᵉ))
  vᵉ = pr2ᵉ (pr1ᵉ (has-pair-expansionᵉ nᵉ))
  sᵉ = pr2ᵉ (has-pair-expansionᵉ nᵉ)
  rᵉ = is-successor-is-nonzero-ℕᵉ (is-nonzero-pair-expansionᵉ uᵉ vᵉ)
  qᵉ :
    ( succ-ℕᵉ (pairing-mapᵉ (uᵉ ,ᵉ vᵉ))) ＝ᵉ
    ( (exp-ℕᵉ 2 uᵉ) *ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ)))
  qᵉ = invᵉ (pr2ᵉ rᵉ)
```

### Pairing function is injective

```agda
is-injective-pairing-mapᵉ : is-injectiveᵉ pairing-mapᵉ
is-injective-pairing-mapᵉ {uᵉ ,ᵉ vᵉ} {u'ᵉ ,ᵉ v'ᵉ} pᵉ =
  ( eq-pair'ᵉ (is-pair-expansion-uniqueᵉ uᵉ u'ᵉ vᵉ v'ᵉ qᵉ))
  where
  rᵉ = is-successor-is-nonzero-ℕᵉ (is-nonzero-pair-expansionᵉ uᵉ vᵉ)
  sᵉ = is-successor-is-nonzero-ℕᵉ (is-nonzero-pair-expansionᵉ u'ᵉ v'ᵉ)
  qᵉ :
    ( (exp-ℕᵉ 2 uᵉ) *ℕᵉ (succ-ℕᵉ (vᵉ *ℕᵉ 2ᵉ))) ＝ᵉ
    ( (exp-ℕᵉ 2 u'ᵉ) *ℕᵉ (succ-ℕᵉ (v'ᵉ *ℕᵉ 2ᵉ)))
  qᵉ = (pr2ᵉ rᵉ) ∙ᵉ (apᵉ succ-ℕᵉ pᵉ ∙ᵉ invᵉ (pr2ᵉ sᵉ))
```

### Pairing function is equivalence

```agda
is-equiv-pairing-mapᵉ : is-equivᵉ pairing-mapᵉ
is-equiv-pairing-mapᵉ =
  is-equiv-is-split-surjective-is-injectiveᵉ
    pairing-mapᵉ
    is-injective-pairing-mapᵉ
    is-split-surjective-pairing-mapᵉ
```