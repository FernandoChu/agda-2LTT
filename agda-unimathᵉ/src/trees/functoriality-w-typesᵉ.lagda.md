# Functoriality of W-types

```agda
module trees.functoriality-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.truncated-mapsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.universe-levelsᵉ

open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ W-typeᵉ constructor actsᵉ functoriallyᵉ onᵉ `A`ᵉ andᵉ `B`.ᵉ Itᵉ isᵉ covariantᵉ in `A`,ᵉ
andᵉ contravariantᵉ in `B`.ᵉ

## Definition

```agda
map-𝕎'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (gᵉ : (xᵉ : Aᵉ) → Dᵉ (fᵉ xᵉ) → Bᵉ xᵉ) →
  𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Cᵉ Dᵉ
map-𝕎'ᵉ Dᵉ fᵉ gᵉ (tree-𝕎ᵉ aᵉ αᵉ) = tree-𝕎ᵉ (fᵉ aᵉ) (λ dᵉ → map-𝕎'ᵉ Dᵉ fᵉ gᵉ (αᵉ (gᵉ aᵉ dᵉ)))

map-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
  𝕎ᵉ Aᵉ Bᵉ → 𝕎ᵉ Cᵉ Dᵉ
map-𝕎ᵉ Dᵉ fᵉ eᵉ = map-𝕎'ᵉ Dᵉ fᵉ (λ xᵉ → map-inv-equivᵉ (eᵉ xᵉ))
```

## Properties

### We compute the fibers of `map-𝕎`

```agda
fiber-map-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
  𝕎ᵉ Cᵉ Dᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
fiber-map-𝕎ᵉ Dᵉ fᵉ eᵉ (tree-𝕎ᵉ cᵉ γᵉ) =
  (fiberᵉ fᵉ cᵉ) ×ᵉ ((dᵉ : Dᵉ cᵉ) → fiberᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ) (γᵉ dᵉ))

abstract
  equiv-fiber-map-𝕎ᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    (Dᵉ : Cᵉ → UUᵉ l4ᵉ) (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
    (yᵉ : 𝕎ᵉ Cᵉ Dᵉ) → fiberᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ) yᵉ ≃ᵉ fiber-map-𝕎ᵉ Dᵉ fᵉ eᵉ yᵉ
  equiv-fiber-map-𝕎ᵉ {Aᵉ = Aᵉ} {Bᵉ} {Cᵉ} Dᵉ fᵉ eᵉ (tree-𝕎ᵉ cᵉ γᵉ) =
    ( ( ( inv-equivᵉ
          ( associative-Σᵉ Aᵉ
            ( λ aᵉ → fᵉ aᵉ ＝ᵉ cᵉ)
            ( λ tᵉ → (dᵉ : Dᵉ cᵉ) → fiberᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ) (γᵉ dᵉ)))) ∘eᵉ
        ( equiv-totᵉ
          ( λ aᵉ →
            ( ( equiv-totᵉ
                ( λ pᵉ →
                  ( ( equiv-Πᵉ
                      ( λ (dᵉ : Dᵉ cᵉ) → fiberᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ) (γᵉ dᵉ))
                      ( (equiv-trᵉ Dᵉ pᵉ) ∘eᵉ (eᵉ aᵉ))
                      ( λ bᵉ → id-equivᵉ)) ∘eᵉ
                    ( inv-distributive-Π-Σᵉ)) ∘eᵉ
                  ( equiv-totᵉ
                    ( λ αᵉ →
                      equiv-Πᵉ
                        ( λ (bᵉ : Bᵉ aᵉ) →
                          map-𝕎ᵉ Dᵉ fᵉ eᵉ (αᵉ bᵉ) ＝ᵉ γᵉ (trᵉ Dᵉ pᵉ (map-equivᵉ (eᵉ aᵉ) bᵉ)))
                        ( inv-equivᵉ (eᵉ aᵉ))
                        ( λ dᵉ →
                          ( equiv-concat'ᵉ
                            ( map-𝕎ᵉ Dᵉ fᵉ eᵉ
                              ( αᵉ (map-inv-equivᵉ (eᵉ aᵉ) dᵉ)))
                            ( apᵉ
                              ( γᵉ ∘ᵉ (trᵉ Dᵉ pᵉ))
                              ( invᵉ (is-section-map-inv-equivᵉ (eᵉ aᵉ) dᵉ)))) ∘eᵉ
                          ( inv-equivᵉ
                            ( equiv-Eq-𝕎-eqᵉ
                              ( map-𝕎ᵉ Dᵉ fᵉ eᵉ
                                ( αᵉ (map-inv-equivᵉ (eᵉ aᵉ) dᵉ)))
                              ( γᵉ (trᵉ Dᵉ pᵉ dᵉ))))))))) ∘eᵉ
              ( equiv-left-swap-Σᵉ)) ∘eᵉ
            ( equiv-totᵉ
              ( λ αᵉ →
                equiv-Eq-𝕎-eqᵉ
                  ( tree-𝕎ᵉ
                    ( fᵉ aᵉ)
                    ( ( map-𝕎ᵉ Dᵉ fᵉ eᵉ) ∘ᵉ
                      ( αᵉ ∘ᵉ map-inv-equivᵉ (eᵉ aᵉ)))) (tree-𝕎ᵉ cᵉ γᵉ)))))) ∘eᵉ
      ( associative-Σᵉ Aᵉ
        ( λ aᵉ → Bᵉ aᵉ → 𝕎ᵉ Aᵉ Bᵉ)
        ( λ tᵉ → map-𝕎ᵉ Dᵉ fᵉ eᵉ (structure-𝕎-Algᵉ tᵉ) ＝ᵉ tree-𝕎ᵉ cᵉ γᵉ))) ∘eᵉ
    ( equiv-Σᵉ
      ( λ tᵉ → map-𝕎ᵉ Dᵉ fᵉ eᵉ (structure-𝕎-Algᵉ tᵉ) ＝ᵉ tree-𝕎ᵉ cᵉ γᵉ)
      ( inv-equiv-structure-𝕎-Algᵉ)
      ( λ xᵉ →
        equiv-concatᵉ
          ( apᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ) (is-section-map-inv-structure-𝕎-Algᵉ xᵉ))
          ( tree-𝕎ᵉ cᵉ γᵉ)))
```

### For any family of equivalences `e` over `f`, if `f` is truncated then `map-𝕎 f e` is truncated

```agda
is-trunc-map-map-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (kᵉ : 𝕋ᵉ)
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
  is-trunc-mapᵉ kᵉ fᵉ → is-trunc-mapᵉ kᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ)
is-trunc-map-map-𝕎ᵉ kᵉ Dᵉ fᵉ eᵉ Hᵉ (tree-𝕎ᵉ cᵉ γᵉ) =
  is-trunc-equivᵉ kᵉ
    ( fiber-map-𝕎ᵉ Dᵉ fᵉ eᵉ (tree-𝕎ᵉ cᵉ γᵉ))
    ( equiv-fiber-map-𝕎ᵉ Dᵉ fᵉ eᵉ (tree-𝕎ᵉ cᵉ γᵉ))
    ( is-trunc-Σᵉ
      ( Hᵉ cᵉ)
      ( λ tᵉ → is-trunc-Πᵉ kᵉ (λ dᵉ → is-trunc-map-map-𝕎ᵉ kᵉ Dᵉ fᵉ eᵉ Hᵉ (γᵉ dᵉ))))
```

### For any family of equivalences `e` over `f`, if `f` is an equivalence then `map-𝕎 f e` is an equivalence

```agda
is-equiv-map-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
  is-equivᵉ fᵉ → is-equivᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ)
is-equiv-map-𝕎ᵉ Dᵉ fᵉ eᵉ Hᵉ =
  is-equiv-is-contr-mapᵉ
    ( is-trunc-map-map-𝕎ᵉ neg-two-𝕋ᵉ Dᵉ fᵉ eᵉ (is-contr-map-is-equivᵉ Hᵉ))

equiv-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ ≃ᵉ Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ fᵉ xᵉ)) →
  𝕎ᵉ Aᵉ Bᵉ ≃ᵉ 𝕎ᵉ Cᵉ Dᵉ
equiv-𝕎ᵉ Dᵉ fᵉ eᵉ =
  pairᵉ
    ( map-𝕎ᵉ Dᵉ (map-equivᵉ fᵉ) eᵉ)
    ( is-equiv-map-𝕎ᵉ Dᵉ (map-equivᵉ fᵉ) eᵉ (is-equiv-map-equivᵉ fᵉ))
```

### For any family of equivalences `e` over `f`, if `f` is an embedding, then `map-𝕎 f e` is an embedding

```agda
is-emb-map-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ → Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (fᵉ xᵉ)) →
  is-embᵉ fᵉ → is-embᵉ (map-𝕎ᵉ Dᵉ fᵉ eᵉ)
is-emb-map-𝕎ᵉ Dᵉ fᵉ eᵉ Hᵉ =
  is-emb-is-prop-mapᵉ
    (is-trunc-map-map-𝕎ᵉ neg-one-𝕋ᵉ Dᵉ fᵉ eᵉ (is-prop-map-is-embᵉ Hᵉ))

emb-𝕎ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (Dᵉ : Cᵉ → UUᵉ l4ᵉ)
  (fᵉ : Aᵉ ↪ᵉ Cᵉ) (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Dᵉ (map-embᵉ fᵉ xᵉ)) → 𝕎ᵉ Aᵉ Bᵉ ↪ᵉ 𝕎ᵉ Cᵉ Dᵉ
emb-𝕎ᵉ Dᵉ fᵉ eᵉ =
  pairᵉ
    ( map-𝕎ᵉ Dᵉ (map-embᵉ fᵉ) eᵉ)
    ( is-emb-map-𝕎ᵉ Dᵉ (map-embᵉ fᵉ) eᵉ (is-emb-map-embᵉ fᵉ))
```