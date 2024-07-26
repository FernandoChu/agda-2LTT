# Counting the elements of dependent pair types

```agda
module univalent-combinatorics.counting-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.sums-of-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.double-countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`,ᵉ andᵉ considerᵉ theᵉ followingᵉ statementsᵉ

1.ᵉ Theᵉ elementsᵉ ofᵉ `A`ᵉ canᵉ beᵉ counted.ᵉ
2.ᵉ Forᵉ eachᵉ `xᵉ : A`,ᵉ theᵉ elementsᵉ ofᵉ `Bᵉ x`ᵉ canᵉ beᵉ countedᵉ
3.ᵉ Theᵉ elementsᵉ ofᵉ `Σᵉ Aᵉ B`ᵉ canᵉ beᵉ counted.ᵉ

Ifᵉ 1 holds,ᵉ thenᵉ 2 holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ 3 holds.ᵉ Furthermoreᵉ ifᵉ 2 andᵉ 3 hold,ᵉ
thenᵉ 1 holdsᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ elementsᵉ ofᵉ `Σᵉ (xᵉ : A),ᵉ ¬ᵉ (Bᵉ x)`ᵉ canᵉ beᵉ counted,ᵉ
i.e.,ᵉ ifᵉ theᵉ elementsᵉ in theᵉ complementᵉ ofᵉ `B`ᵉ canᵉ beᵉ counted.ᵉ

## Proofs

### `Σ A B` can be counted if `A` can be counted and if each `B x` can be counted

```agda
count-Σ'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  (kᵉ : ℕᵉ) (eᵉ : Finᵉ kᵉ ≃ᵉ Aᵉ) → ((xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) → countᵉ (Σᵉ Aᵉ Bᵉ)
count-Σ'ᵉ zero-ℕᵉ eᵉ fᵉ =
  count-is-emptyᵉ
    ( λ xᵉ →
      is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ (pr1ᵉ xᵉ))
count-Σ'ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} (succ-ℕᵉ kᵉ) eᵉ fᵉ =
  count-equivᵉ
    ( ( equiv-Σ-equiv-baseᵉ Bᵉ eᵉ) ∘eᵉ
      ( ( inv-equivᵉ
          ( right-distributive-Σ-coproductᵉ (Finᵉ kᵉ) unitᵉ (Bᵉ ∘ᵉ map-equivᵉ eᵉ))) ∘eᵉ
        ( equiv-coproductᵉ
          ( id-equivᵉ)
          ( inv-equivᵉ
            ( left-unit-law-Σᵉ (Bᵉ ∘ᵉ (map-equivᵉ eᵉ ∘ᵉ inrᵉ)))))))
    ( count-coproductᵉ
      ( count-Σ'ᵉ kᵉ id-equivᵉ (λ xᵉ → fᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ))))
      ( fᵉ (map-equivᵉ eᵉ (inrᵉ starᵉ))))

abstract
  equiv-count-Σ'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    (kᵉ : ℕᵉ) (eᵉ : Finᵉ kᵉ ≃ᵉ Aᵉ) (fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
    Finᵉ (number-of-elements-countᵉ (count-Σ'ᵉ kᵉ eᵉ fᵉ)) ≃ᵉ Σᵉ Aᵉ Bᵉ
  equiv-count-Σ'ᵉ kᵉ eᵉ fᵉ = pr2ᵉ (count-Σ'ᵉ kᵉ eᵉ fᵉ)

count-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  countᵉ Aᵉ → ((xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) → countᵉ (Σᵉ Aᵉ Bᵉ)
pr1ᵉ (count-Σᵉ (pairᵉ kᵉ eᵉ) fᵉ) = number-of-elements-countᵉ (count-Σ'ᵉ kᵉ eᵉ fᵉ)
pr2ᵉ (count-Σᵉ (pairᵉ kᵉ eᵉ) fᵉ) = equiv-count-Σ'ᵉ kᵉ eᵉ fᵉ
```

### We compute the number of elements of a Σ-type

```agda
abstract
  number-of-elements-count-Σ'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (kᵉ : ℕᵉ) (eᵉ : Finᵉ kᵉ ≃ᵉ Aᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
    Idᵉ ( number-of-elements-countᵉ (count-Σ'ᵉ kᵉ eᵉ fᵉ))
      ( sum-Fin-ℕᵉ kᵉ (λ xᵉ → number-of-elements-countᵉ (fᵉ (map-equivᵉ eᵉ xᵉ))))
  number-of-elements-count-Σ'ᵉ zero-ℕᵉ eᵉ fᵉ = reflᵉ
  number-of-elements-count-Σ'ᵉ (succ-ℕᵉ kᵉ) eᵉ fᵉ =
    ( number-of-elements-count-coproductᵉ
      ( count-Σ'ᵉ kᵉ id-equivᵉ (λ xᵉ → fᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ))))
      ( fᵉ (map-equivᵉ eᵉ (inrᵉ starᵉ)))) ∙ᵉ
    ( apᵉ
      ( _+ℕᵉ (number-of-elements-countᵉ (fᵉ (map-equivᵉ eᵉ (inrᵉ starᵉ)))))
      ( number-of-elements-count-Σ'ᵉ kᵉ id-equivᵉ (λ xᵉ → fᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)))))

abstract
  number-of-elements-count-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (eᵉ : countᵉ Aᵉ)
    (fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
    Idᵉ ( number-of-elements-countᵉ (count-Σᵉ eᵉ fᵉ))
      ( sum-count-ℕᵉ eᵉ (λ xᵉ → number-of-elements-countᵉ (fᵉ xᵉ)))
  number-of-elements-count-Σᵉ (pairᵉ kᵉ eᵉ) fᵉ = number-of-elements-count-Σ'ᵉ kᵉ eᵉ fᵉ
```

### If `A` and `Σ A B` can be counted, then each `B x` can be counted

```agda
count-fiber-count-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  has-decidable-equalityᵉ Aᵉ → countᵉ (Σᵉ Aᵉ Bᵉ) → (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)
count-fiber-count-Σᵉ {Bᵉ = Bᵉ} dᵉ fᵉ xᵉ =
  count-equivᵉ
    ( equiv-fiber-pr1ᵉ Bᵉ xᵉ)
    ( count-Σᵉ fᵉ
      ( λ zᵉ → count-eqᵉ dᵉ (pr1ᵉ zᵉ) xᵉ))

count-fiber-count-Σ-count-baseᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  countᵉ Aᵉ → countᵉ (Σᵉ Aᵉ Bᵉ) → (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)
count-fiber-count-Σ-count-baseᵉ eᵉ fᵉ xᵉ =
  count-fiber-count-Σᵉ (has-decidable-equality-countᵉ eᵉ) fᵉ xᵉ
```

### If `Σ A B` and each `B x` can be counted, and if `B` has a section, then `A` can be counted

```agda
count-fiber-map-section-familyᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
  countᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
  (tᵉ : Σᵉ Aᵉ Bᵉ) → countᵉ (fiberᵉ (map-section-familyᵉ bᵉ) tᵉ)
count-fiber-map-section-familyᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} bᵉ eᵉ fᵉ (pairᵉ yᵉ zᵉ) =
  count-equiv'ᵉ
    ( ( ( left-unit-law-Σ-is-contrᵉ
            ( is-torsorial-Id'ᵉ yᵉ)
            ( pairᵉ yᵉ reflᵉ)) ∘eᵉ
        ( inv-associative-Σᵉ Aᵉ
          ( λ xᵉ → Idᵉ xᵉ yᵉ)
          ( λ tᵉ → Idᵉ (trᵉ Bᵉ (pr2ᵉ tᵉ) (bᵉ (pr1ᵉ tᵉ))) zᵉ))) ∘eᵉ
      ( equiv-totᵉ (λ xᵉ → equiv-pair-eq-Σᵉ (pairᵉ xᵉ (bᵉ xᵉ)) (pairᵉ yᵉ zᵉ))))
    ( count-eqᵉ (has-decidable-equality-countᵉ (fᵉ yᵉ)) (bᵉ yᵉ) zᵉ)

count-base-count-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
  countᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) → countᵉ Aᵉ
count-base-count-Σᵉ bᵉ eᵉ fᵉ =
  count-equivᵉ
    ( equiv-total-fiberᵉ (map-section-familyᵉ bᵉ))
    ( count-Σᵉ eᵉ (count-fiber-map-section-familyᵉ bᵉ eᵉ fᵉ))
```

Moreᵉ generally,ᵉ ifᵉ `Σᵉ Aᵉ B`ᵉ andᵉ eachᵉ `Bᵉ x`ᵉ canᵉ beᵉ counted,ᵉ thenᵉ `A`ᵉ canᵉ beᵉ
countedᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ typeᵉ `Σᵉ (xᵉ : A),ᵉ ¬ᵉ (Bᵉ x)`ᵉ canᵉ beᵉ counted.ᵉ However,ᵉ to
avoidᵉ havingᵉ to invokeᵉ functionᵉ extensionality,ᵉ weᵉ showᵉ thatᵉ ifᵉ `Σᵉ Aᵉ B`ᵉ andᵉ eachᵉ
`Bᵉ x`ᵉ canᵉ beᵉ counted,ᵉ thenᵉ `A`ᵉ canᵉ beᵉ countedᵉ ifᵉ andᵉ onlyᵉ ifᵉ

```text
  countᵉ (Σᵉ Aᵉ (λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ x)))),ᵉ
```

where `fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ x)`.ᵉ Thus,ᵉ weᵉ haveᵉ aᵉ preciseᵉ characterizationᵉ ofᵉ
whenᵉ theᵉ elementsᵉ ofᵉ `A`ᵉ canᵉ beᵉ counted,ᵉ ifᵉ itᵉ isᵉ givenᵉ thatᵉ `Σᵉ Aᵉ B`ᵉ andᵉ eachᵉ
`Bᵉ x`ᵉ canᵉ beᵉ counted.ᵉ

```agda
section-count-base-count-Σ'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → countᵉ (Σᵉ Aᵉ Bᵉ) →
  (fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
  countᵉ (Σᵉ Aᵉ (λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ xᵉ)))) →
  (xᵉ : Aᵉ) → (Bᵉ xᵉ) +ᵉ (is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ xᵉ)))
section-count-base-count-Σ'ᵉ eᵉ fᵉ gᵉ xᵉ with
  is-decidable-is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ xᵉ))
... | inlᵉ pᵉ = inrᵉ pᵉ
... | inrᵉ Hᵉ with is-successor-is-nonzero-ℕᵉ Hᵉ
... | (pairᵉ kᵉ pᵉ) = inlᵉ (map-equiv-countᵉ (fᵉ xᵉ) (trᵉ Finᵉ (invᵉ pᵉ) (zero-Finᵉ kᵉ)))

count-base-count-Σ'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → countᵉ (Σᵉ Aᵉ Bᵉ) →
  (fᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
  countᵉ (Σᵉ Aᵉ (λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ xᵉ)))) → countᵉ Aᵉ
count-base-count-Σ'ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} eᵉ fᵉ gᵉ =
  count-base-count-Σᵉ
    ( section-count-base-count-Σ'ᵉ eᵉ fᵉ gᵉ)
    ( count-equiv'ᵉ
      ( left-distributive-Σ-coproductᵉ Aᵉ Bᵉ
        ( λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (fᵉ xᵉ))))
      ( count-coproductᵉ eᵉ gᵉ))
    ( λ xᵉ →
      count-coproductᵉ
        ( fᵉ xᵉ)
        ( count-eqᵉ has-decidable-equality-ℕᵉ
          ( number-of-elements-countᵉ (fᵉ xᵉ))
          ( zero-ℕᵉ)))
```

### If `A` can be counted and `Σ A P` can be counted for a subtype of `A`, then `P` is decidable

```agda
is-decidable-count-Σᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Pᵉ : Xᵉ → UUᵉ l2ᵉ} →
  countᵉ Xᵉ → countᵉ (Σᵉ Xᵉ Pᵉ) → (xᵉ : Xᵉ) → is-decidableᵉ (Pᵉ xᵉ)
is-decidable-count-Σᵉ eᵉ fᵉ xᵉ =
  is-decidable-countᵉ (count-fiber-count-Σ-count-baseᵉ eᵉ fᵉ xᵉ)
```

```agda
abstract
  double-counting-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    (count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) (count-Cᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) →
    Idᵉ
      ( number-of-elements-countᵉ count-Cᵉ)
      ( sum-count-ℕᵉ count-Aᵉ (λ xᵉ → number-of-elements-countᵉ (count-Bᵉ xᵉ)))
  double-counting-Σᵉ count-Aᵉ count-Bᵉ count-Cᵉ =
    ( double-countingᵉ count-Cᵉ (count-Σᵉ count-Aᵉ count-Bᵉ)) ∙ᵉ
    ( number-of-elements-count-Σᵉ count-Aᵉ count-Bᵉ)

abstract
  sum-number-of-elements-count-fiber-count-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (eᵉ : countᵉ Aᵉ)
    (fᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) →
    Idᵉ
      ( sum-count-ℕᵉ eᵉ
        ( λ xᵉ → number-of-elements-countᵉ
          (count-fiber-count-Σ-count-baseᵉ eᵉ fᵉ xᵉ)))
      ( number-of-elements-countᵉ fᵉ)
  sum-number-of-elements-count-fiber-count-Σᵉ eᵉ fᵉ =
    ( invᵉ
      ( number-of-elements-count-Σᵉ eᵉ (count-fiber-count-Σ-count-baseᵉ eᵉ fᵉ))) ∙ᵉ
    ( double-countingᵉ (count-Σᵉ eᵉ (count-fiber-count-Σ-count-baseᵉ eᵉ fᵉ)) fᵉ)

abstract
  double-counting-fiber-count-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    (count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) (count-Cᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) (xᵉ : Aᵉ) →
    Idᵉ
      ( number-of-elements-countᵉ (count-Bᵉ xᵉ))
      ( number-of-elements-countᵉ
        ( count-fiber-count-Σ-count-baseᵉ count-Aᵉ count-Cᵉ xᵉ))
  double-counting-fiber-count-Σᵉ count-Aᵉ count-Bᵉ count-Cᵉ xᵉ =
    double-countingᵉ
      ( count-Bᵉ xᵉ)
      ( count-fiber-count-Σ-count-baseᵉ count-Aᵉ count-Cᵉ xᵉ)

abstract
  sum-number-of-elements-count-base-count-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    (count-ΣABᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) (count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
    Idᵉ
      ( sum-count-ℕᵉ
        ( count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ)
        ( λ xᵉ → number-of-elements-countᵉ (count-Bᵉ xᵉ)))
      ( number-of-elements-countᵉ count-ΣABᵉ)
  sum-number-of-elements-count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ =
    ( invᵉ
      ( number-of-elements-count-Σᵉ
        ( count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ)
        ( count-Bᵉ))) ∙ᵉ
    ( double-countingᵉ
      ( count-Σᵉ (count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ) count-Bᵉ)
      ( count-ΣABᵉ))

abstract
  double-counting-base-count-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    (count-Aᵉ : countᵉ Aᵉ) (count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ))
    (count-ΣABᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) →
    Idᵉ
      ( number-of-elements-countᵉ (count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ))
      ( number-of-elements-countᵉ count-Aᵉ)
  double-counting-base-count-Σᵉ bᵉ count-Aᵉ count-Bᵉ count-ΣABᵉ =
    double-countingᵉ (count-base-count-Σᵉ bᵉ count-ΣABᵉ count-Bᵉ) count-Aᵉ

abstract
  sum-number-of-elements-count-base-count-Σ'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (count-ΣABᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) →
    ( count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) →
    ( count-nBᵉ :
      countᵉ (Σᵉ Aᵉ (λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (count-Bᵉ xᵉ))))) →
    Idᵉ
      ( sum-count-ℕᵉ
        ( count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ)
        ( λ xᵉ → number-of-elements-countᵉ (count-Bᵉ xᵉ)))
      ( number-of-elements-countᵉ count-ΣABᵉ)
  sum-number-of-elements-count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ =
    ( invᵉ
      ( number-of-elements-count-Σᵉ
        ( count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ)
        ( count-Bᵉ))) ∙ᵉ
    ( double-countingᵉ
      ( count-Σᵉ
        ( count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ)
        ( count-Bᵉ))
      ( count-ΣABᵉ))

abstract
  double-counting-base-count-Σ'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    ( count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) (count-ΣABᵉ : countᵉ (Σᵉ Aᵉ Bᵉ)) →
    ( count-nBᵉ :
      countᵉ (Σᵉ Aᵉ (λ xᵉ → is-zero-ℕᵉ (number-of-elements-countᵉ (count-Bᵉ xᵉ))))) →
    Idᵉ
      ( number-of-elements-countᵉ
        ( count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ))
      ( number-of-elements-countᵉ count-Aᵉ)
  double-counting-base-count-Σ'ᵉ count-Aᵉ count-Bᵉ count-ΣABᵉ count-nBᵉ =
    double-countingᵉ (count-base-count-Σ'ᵉ count-ΣABᵉ count-Bᵉ count-nBᵉ) count-Aᵉ
```