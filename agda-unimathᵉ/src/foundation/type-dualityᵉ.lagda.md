# Type duality

```agda
module foundation.type-dualityᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.sliceᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import trees.polynomial-endofunctorsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [univalent](foundation.univalence.mdᵉ) universeᵉ `𝒰`,ᵉ weᵉ canᵉ defineᵉ twoᵉ
closelyᵉ relatedᵉ functorsᵉ actingᵉ onᵉ allᵉ types.ᵉ Firstᵉ thereᵉ isᵉ theᵉ covariantᵉ
functorᵉ givenᵉ byᵉ

```text
  P_𝒰(Aᵉ) :=ᵉ Σᵉ (Xᵉ : 𝒰),ᵉ Xᵉ → A.ᵉ
```

Thisᵉ isᵉ aᵉ [polynomialᵉ endofunctor](trees.polynomial-endofunctors.md).ᵉ Second,ᵉ
thereᵉ isᵉ theᵉ contravariantᵉ functorᵉ givenᵉ byᵉ

```text
  P^𝒰(Aᵉ) :=ᵉ Aᵉ → 𝒰.ᵉ
```

Ifᵉ theᵉ typeᵉ `A`ᵉ isᵉ [locallyᵉ `𝒰`-small](foundation.locally-small-types.md),ᵉ thenᵉ
thereᵉ isᵉ aᵉ mapᵉ `φ_Aᵉ : P_𝒰(Aᵉ) → P^𝒰(A)`.ᵉ Thisᵉ mapᵉ isᵉ naturalᵉ in `A`,ᵉ andᵉ itᵉ isᵉ
alwaysᵉ anᵉ [embedding](foundation-core.embeddings.md).ᵉ Furthermore,ᵉ theᵉ mapᵉ `φ_A`ᵉ
isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ `A`ᵉ isᵉ
[`𝒰`-small](foundation-core.small-types.md).ᵉ

## Definitions

### The polynomial endofunctor of a universe

```agda
type-polynomial-endofunctor-UUᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
type-polynomial-endofunctor-UUᵉ lᵉ = Sliceᵉ lᵉ

map-polynomial-endofunctor-UUᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ → type-polynomial-endofunctor-UUᵉ lᵉ Bᵉ
map-polynomial-endofunctor-UUᵉ lᵉ = map-polynomial-endofunctorᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ)
```

### Type families

```agda
type-exp-UUᵉ : (lᵉ : Level) {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
type-exp-UUᵉ lᵉ Aᵉ = Aᵉ → UUᵉ lᵉ

map-exp-UUᵉ :
  (lᵉ : Level) {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  type-exp-UUᵉ lᵉ Bᵉ → type-exp-UUᵉ lᵉ Aᵉ
map-exp-UUᵉ lᵉ fᵉ Pᵉ = Pᵉ ∘ᵉ fᵉ
```

## Properties

### If `A` is locally `l`-small, then we can construct an embedding `type-polynomial-endofunctor l A ↪ type-exp-UU A`

```agda
map-type-dualityᵉ :
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-locally-smallᵉ lᵉ Aᵉ →
  type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ → type-exp-UUᵉ lᵉ Aᵉ
map-type-dualityᵉ Hᵉ (Xᵉ ,ᵉ fᵉ) aᵉ =
  Σᵉ Xᵉ (λ xᵉ → type-is-smallᵉ (Hᵉ (fᵉ xᵉ) aᵉ))

is-emb-map-type-dualityᵉ :
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-locally-smallᵉ lᵉ Aᵉ) →
  is-embᵉ (map-type-dualityᵉ Hᵉ)
is-emb-map-type-dualityᵉ {lᵉ} {l1ᵉ} {Aᵉ} Hᵉ (Xᵉ ,ᵉ fᵉ) =
  fundamental-theorem-idᵉ
    ( is-contr-equivᵉ
      ( Σᵉ ( type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ) ((Xᵉ ,ᵉ fᵉ) ＝ᵉ_))
      ( equiv-totᵉ
        ( λ (Yᵉ ,ᵉ gᵉ) →
          ( inv-equivᵉ (extensionality-Sliceᵉ (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ))) ∘eᵉ
          ( inv-equivᵉ (equiv-fam-equiv-equiv-sliceᵉ fᵉ gᵉ)) ∘eᵉ
          ( equiv-Π-equiv-familyᵉ
            ( λ aᵉ →
              ( equiv-postcomp-equivᵉ
                ( equiv-totᵉ (λ yᵉ → inv-equivᵉ (equiv-is-smallᵉ (Hᵉ (gᵉ yᵉ) aᵉ))))
                ( fiberᵉ fᵉ aᵉ)) ∘eᵉ
              ( equiv-precomp-equivᵉ
                ( equiv-totᵉ (λ xᵉ → equiv-is-smallᵉ (Hᵉ (fᵉ xᵉ) aᵉ)))
                ( Σᵉ Yᵉ (λ yᵉ → type-is-smallᵉ (Hᵉ (gᵉ yᵉ) aᵉ)))) ∘eᵉ
              ( equiv-univalenceᵉ))) ∘eᵉ
          ( equiv-funextᵉ)))
      ( is-torsorial-Idᵉ (Xᵉ ,ᵉ fᵉ)))
    ( λ Yᵉ → apᵉ (map-type-dualityᵉ Hᵉ))

emb-type-dualityᵉ :
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → is-locally-smallᵉ lᵉ Aᵉ →
  type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ ↪ᵉ type-exp-UUᵉ lᵉ Aᵉ
pr1ᵉ (emb-type-dualityᵉ Hᵉ) = map-type-dualityᵉ Hᵉ
pr2ᵉ (emb-type-dualityᵉ Hᵉ) = is-emb-map-type-dualityᵉ Hᵉ
```

### A type `A` is small if and only if `P_𝒰(A) ↪ P^𝒰(A)` is an equivalence

#### The forward direction

```agda
module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-smallᵉ lᵉ Aᵉ)
  where

  map-inv-type-dualityᵉ :
    type-exp-UUᵉ lᵉ Aᵉ → type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ
  pr1ᵉ (map-inv-type-dualityᵉ Bᵉ) =
    type-is-smallᵉ (is-small-Σᵉ Hᵉ (λ aᵉ → is-small'ᵉ {lᵉ} {Bᵉ aᵉ}))
  pr2ᵉ (map-inv-type-dualityᵉ Bᵉ) =
    ( pr1ᵉ) ∘ᵉ
    ( map-inv-equivᵉ (equiv-is-smallᵉ (is-small-Σᵉ Hᵉ (λ aᵉ → is-small'ᵉ {lᵉ} {Bᵉ aᵉ}))))

  is-section-map-inv-type-dualityᵉ :
    map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ) ∘ᵉ map-inv-type-dualityᵉ ~ᵉ idᵉ
  is-section-map-inv-type-dualityᵉ Bᵉ =
    eq-equiv-famᵉ
      ( λ aᵉ →
        equivalence-reasoningᵉ
          map-type-dualityᵉ
            ( is-locally-small-is-smallᵉ Hᵉ)
            ( map-inv-type-dualityᵉ Bᵉ)
            ( aᵉ)
          ≃ᵉ fiberᵉ
            ( ( pr1ᵉ {Bᵉ = Bᵉ}) ∘ᵉ
              ( map-inv-equivᵉ
                ( equiv-is-smallᵉ
                  ( is-small-Σᵉ Hᵉ (λ aᵉ → is-small'ᵉ))))) aᵉ
            byᵉ
            equiv-totᵉ
              ( λ xᵉ →
                inv-equivᵉ
                  ( equiv-is-smallᵉ
                    ( is-locally-small-is-smallᵉ Hᵉ
                      ( pr2ᵉ (map-inv-type-dualityᵉ Bᵉ) xᵉ)
                      ( aᵉ))))
          ≃ᵉ Σᵉ ( fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ)
              ( λ bᵉ →
                fiberᵉ
                  ( map-inv-equivᵉ
                    ( equiv-is-smallᵉ
                      ( is-small-Σᵉ Hᵉ (λ aᵉ → is-small'ᵉ {lᵉ} {Bᵉ aᵉ}))))
                  ( pr1ᵉ bᵉ))
            byᵉ compute-fiber-compᵉ pr1ᵉ _ aᵉ
          ≃ᵉ fiberᵉ (pr1ᵉ {Bᵉ = Bᵉ}) aᵉ
            byᵉ
            right-unit-law-Σ-is-contrᵉ
              ( λ bᵉ →
                is-contr-map-is-equivᵉ
                  ( is-equiv-map-inv-equivᵉ
                    ( equiv-is-smallᵉ
                      ( is-small-Σᵉ Hᵉ (λ aᵉ → is-small'ᵉ {lᵉ} {Bᵉ aᵉ}))))
                  ( pr1ᵉ bᵉ))
          ≃ᵉ Bᵉ aᵉ
            byᵉ
            equiv-fiber-pr1ᵉ Bᵉ aᵉ)

  is-retraction-map-inv-type-dualityᵉ :
    map-inv-type-dualityᵉ ∘ᵉ map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-type-dualityᵉ Xᵉ =
    is-injective-is-embᵉ
      ( is-emb-map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ))
      ( is-section-map-inv-type-dualityᵉ
        ( map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ) Xᵉ))

  is-equiv-map-type-dualityᵉ :
    is-equivᵉ (map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ))
  is-equiv-map-type-dualityᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-type-dualityᵉ
      is-section-map-inv-type-dualityᵉ
      is-retraction-map-inv-type-dualityᵉ

  type-dualityᵉ : type-polynomial-endofunctor-UUᵉ lᵉ Aᵉ ≃ᵉ type-exp-UUᵉ lᵉ Aᵉ
  pr1ᵉ type-dualityᵉ = map-type-dualityᵉ (is-locally-small-is-smallᵉ Hᵉ)
  pr2ᵉ type-dualityᵉ = is-equiv-map-type-dualityᵉ
```

#### The converse direction

```agda
module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-locally-smallᵉ lᵉ Aᵉ)
  where

  is-small-is-equiv-map-type-dualityᵉ :
    is-equivᵉ (map-type-dualityᵉ Hᵉ) → is-smallᵉ lᵉ Aᵉ
  pr1ᵉ (is-small-is-equiv-map-type-dualityᵉ Eᵉ) =
    pr1ᵉ (map-inv-is-equivᵉ Eᵉ (λ _ → raise-unitᵉ lᵉ))
  pr2ᵉ (is-small-is-equiv-map-type-dualityᵉ Eᵉ) =
    inv-equivᵉ
      ( ( pr2ᵉ (map-inv-is-equivᵉ Eᵉ (λ _ → raise-unitᵉ lᵉ))) ,ᵉ
        ( is-equiv-is-contr-mapᵉ
          ( λ aᵉ →
            is-contr-equivᵉ
              ( raise-unitᵉ lᵉ)
              ( ( equiv-eq-famᵉ _ _
                  ( is-section-map-inv-is-equivᵉ Eᵉ (λ _ → raise-unitᵉ lᵉ))
                  ( aᵉ)) ∘eᵉ
                ( equiv-totᵉ
                  ( λ xᵉ →
                    equiv-is-smallᵉ
                      ( Hᵉ ( pr2ᵉ (map-inv-is-equivᵉ Eᵉ (λ _ → raise-unitᵉ lᵉ)) xᵉ)
                          ( aᵉ)))))
              ( is-contr-raise-unitᵉ))))
```

### Type duality formulated using `l1 ⊔ l2`

```agda
Fiberᵉ : {lᵉ l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → Sliceᵉ lᵉ Aᵉ → Aᵉ → UUᵉ (l1ᵉ ⊔ lᵉ)
Fiberᵉ Aᵉ fᵉ = fiberᵉ (pr2ᵉ fᵉ)

Pr1ᵉ : {lᵉ l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → (Aᵉ → UUᵉ lᵉ) → Sliceᵉ (l1ᵉ ⊔ lᵉ) Aᵉ
pr1ᵉ (Pr1ᵉ Aᵉ Bᵉ) = Σᵉ Aᵉ Bᵉ
pr2ᵉ (Pr1ᵉ Aᵉ Bᵉ) = pr1ᵉ

is-section-Pr1ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Fiberᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ ∘ᵉ Pr1ᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ) ~ᵉ idᵉ
is-section-Pr1ᵉ Bᵉ = eq-equiv-famᵉ (equiv-fiber-pr1ᵉ Bᵉ)

is-retraction-Pr1ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Pr1ᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ ∘ᵉ Fiberᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ) ~ᵉ idᵉ
is-retraction-Pr1ᵉ {Aᵉ = Aᵉ} (Xᵉ ,ᵉ fᵉ) =
  eq-equiv-sliceᵉ
    ( Pr1ᵉ Aᵉ (Fiberᵉ Aᵉ (Xᵉ ,ᵉ fᵉ)))
    ( Xᵉ ,ᵉ fᵉ)
    ( equiv-total-fiberᵉ fᵉ ,ᵉ triangle-map-equiv-total-fiberᵉ fᵉ)

is-equiv-Fiberᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → is-equivᵉ (Fiberᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ)
is-equiv-Fiberᵉ l2ᵉ Aᵉ =
  is-equiv-is-invertibleᵉ
    ( Pr1ᵉ Aᵉ)
    ( is-section-Pr1ᵉ {l2ᵉ = l2ᵉ})
    ( is-retraction-Pr1ᵉ {l2ᵉ = l2ᵉ})

equiv-Fiberᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → Sliceᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ ≃ᵉ (Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ))
pr1ᵉ (equiv-Fiberᵉ l2ᵉ Aᵉ) = Fiberᵉ Aᵉ
pr2ᵉ (equiv-Fiberᵉ l2ᵉ Aᵉ) = is-equiv-Fiberᵉ l2ᵉ Aᵉ

is-equiv-Pr1ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → is-equivᵉ (Pr1ᵉ {l1ᵉ ⊔ l2ᵉ} Aᵉ)
is-equiv-Pr1ᵉ {l1ᵉ} l2ᵉ Aᵉ =
  is-equiv-is-invertibleᵉ
    ( Fiberᵉ Aᵉ)
    ( is-retraction-Pr1ᵉ {l2ᵉ = l2ᵉ})
    ( is-section-Pr1ᵉ {l2ᵉ = l2ᵉ})

equiv-Pr1ᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → (Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)) ≃ᵉ Sliceᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
pr1ᵉ (equiv-Pr1ᵉ l2ᵉ Aᵉ) = Pr1ᵉ Aᵉ
pr2ᵉ (equiv-Pr1ᵉ l2ᵉ Aᵉ) = is-equiv-Pr1ᵉ l2ᵉ Aᵉ
```

Theᵉ typeᵉ ofᵉ allᵉ functionᵉ fromᵉ `Aᵉ → B`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ functionᵉ
`Yᵉ : Bᵉ → 𝒰`ᵉ with anᵉ equivalenceᵉ `Aᵉ ≃ᵉ Σᵉ Bᵉ Yᵉ `ᵉ

```agda
fiber-Σᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Aᵉ : UUᵉ l2ᵉ) →
  (Xᵉ → Aᵉ) ≃ᵉ Σᵉ (Aᵉ → UUᵉ (l2ᵉ ⊔ l1ᵉ)) (λ Yᵉ → Xᵉ ≃ᵉ Σᵉ Aᵉ Yᵉ)
fiber-Σᵉ {l1ᵉ} {l2ᵉ} Xᵉ Aᵉ =
  ( equiv-Σᵉ
    ( λ Zᵉ → Xᵉ ≃ᵉ Σᵉ Aᵉ Zᵉ)
    ( equiv-Fiberᵉ l1ᵉ Aᵉ)
    ( λ sᵉ → inv-equivᵉ ( equiv-postcomp-equivᵉ (equiv-total-fiberᵉ (pr2ᵉ sᵉ)) Xᵉ))) ∘eᵉ
  ( equiv-right-swap-Σᵉ) ∘eᵉ
  ( inv-left-unit-law-Σ-is-contrᵉ
    ( is-contr-is-small-lmaxᵉ l2ᵉ Xᵉ)
    ( is-small-lmaxᵉ l2ᵉ Xᵉ)) ∘eᵉ
  ( equiv-precompᵉ (inv-equivᵉ (equiv-is-smallᵉ (is-small-lmaxᵉ l2ᵉ Xᵉ))) Aᵉ)
```

## See also

-ᵉ Inᵉ [`foundation.binary-type-duality`](foundation.binary-type-duality.mdᵉ) weᵉ
  showᵉ thatᵉ [binaryᵉ relations](foundation.binary-relations.mdᵉ) areᵉ equivalentlyᵉ
  describedᵉ asᵉ [spansᵉ ofᵉ types](foundation.spans.md).ᵉ