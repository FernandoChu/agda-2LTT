# Set quotients of index `2`

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module univalent-combinatorics.set-quotients-of-index-twoᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  (Ufᵉ : is-set-quotientᵉ Rᵉ QRᵉ fᵉ)
  (eAᵉ : type-Setᵉ QRᵉ ≃ᵉ Finᵉ 2ᵉ) (hᵉ : Aᵉ → Aᵉ)
  (Hᵉ : {xᵉ yᵉ : Aᵉ} →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ ↔ᵉ sim-equivalence-relationᵉ Rᵉ (hᵉ xᵉ) (hᵉ yᵉ))
  (h'ᵉ : type-Setᵉ QRᵉ → type-Setᵉ QRᵉ)
  (xᵉ : Aᵉ)
  (Pᵉ :
    h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ) ＝ᵉ
    map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ (hᵉ xᵉ))
  where

  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ :
    is-embᵉ h'ᵉ →
    (yᵉ : Aᵉ) (kᵉ k'ᵉ k''ᵉ : Finᵉ 2ᵉ) →
    map-equivᵉ eAᵉ (h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ)) ＝ᵉ kᵉ →
    map-equivᵉ eAᵉ (h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ)) ＝ᵉ k'ᵉ →
    map-equivᵉ eAᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ (hᵉ yᵉ)) ＝ᵉ k''ᵉ →
    h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ) ＝ᵉ
    map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ (hᵉ yᵉ)
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inlᵉ (inrᵉ _)) (inlᵉ (inrᵉ _)) k''ᵉ pᵉ qᵉ rᵉ =
    ( is-injective-equivᵉ eAᵉ (qᵉ ∙ᵉ invᵉ pᵉ)) ∙ᵉ
      ( Pᵉ ∙ᵉ
        reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ
          ( pr1ᵉ Hᵉ
            ( map-equivᵉ
              ( is-effective-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ xᵉ yᵉ)
              ( map-inv-is-equivᵉ
                ( H'ᵉ
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ)
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ))
                ( is-injective-equivᵉ eAᵉ (pᵉ ∙ᵉ invᵉ qᵉ))))))
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inlᵉ (inrᵉ _)) (inrᵉ _) (inlᵉ (inrᵉ _)) pᵉ qᵉ rᵉ =
    ex-falsoᵉ
      ( neq-inl-inrᵉ
        ( invᵉ pᵉ ∙ᵉ
          ( ( apᵉ
            ( map-equivᵉ eAᵉ ∘ᵉ h'ᵉ)
            ( reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ
              ( pr2ᵉ Hᵉ
                (map-equivᵉ
                  ( is-effective-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ (hᵉ xᵉ) (hᵉ yᵉ))
                  ( invᵉ Pᵉ ∙ᵉ is-injective-equivᵉ eAᵉ (pᵉ ∙ᵉ invᵉ rᵉ)))))) ∙ᵉ
            ( qᵉ))))
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inlᵉ (inrᵉ _)) (inrᵉ _) (inrᵉ _) pᵉ qᵉ rᵉ =
    is-injective-equivᵉ eAᵉ (qᵉ ∙ᵉ invᵉ rᵉ)
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inrᵉ _) (inlᵉ (inrᵉ _)) (inlᵉ (inrᵉ _)) pᵉ qᵉ rᵉ =
    is-injective-equivᵉ eAᵉ (qᵉ ∙ᵉ invᵉ rᵉ)
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inrᵉ _) (inlᵉ (inrᵉ _)) (inrᵉ _) pᵉ qᵉ rᵉ =
    ex-falsoᵉ
      ( neq-inr-inlᵉ
        ( invᵉ pᵉ ∙ᵉ
          ( ( apᵉ
            ( map-equivᵉ eAᵉ ∘ᵉ h'ᵉ)
            ( reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ
              ( pr2ᵉ Hᵉ
                (map-equivᵉ
                  ( is-effective-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ (hᵉ xᵉ) (hᵉ yᵉ))
                  ( invᵉ Pᵉ ∙ᵉ is-injective-equivᵉ eAᵉ (pᵉ ∙ᵉ invᵉ rᵉ)))))) ∙ᵉ
            ( qᵉ))))
  cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
    ( inrᵉ _) (inrᵉ _) k''ᵉ pᵉ qᵉ rᵉ =
    ( is-injective-equivᵉ eAᵉ (qᵉ ∙ᵉ invᵉ pᵉ)) ∙ᵉ
      ( Pᵉ ∙ᵉ
        reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ
          ( pr1ᵉ Hᵉ
            ( map-equivᵉ
              ( is-effective-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Ufᵉ xᵉ yᵉ)
              ( map-inv-is-equivᵉ
                ( H'ᵉ
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ)
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ))
                ( is-injective-equivᵉ eAᵉ (pᵉ ∙ᵉ invᵉ qᵉ))))))

  coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ :
    is-embᵉ h'ᵉ →
    coherence-square-mapsᵉ
      ( hᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
      ( h'ᵉ)
  coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ =
    cases-coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ H'ᵉ yᵉ
      ( map-equivᵉ eAᵉ (h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ)))
      ( map-equivᵉ eAᵉ (h'ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ)))
      ( map-equivᵉ eAᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ (hᵉ yᵉ)))
      ( reflᵉ)
      ( reflᵉ)
      ( reflᵉ)

  eq-equiv-eq-one-value-equiv-is-set-quotientᵉ :
    (Pᵉ : is-equivᵉ hᵉ) (Qᵉ : is-equivᵉ h'ᵉ) →
    pairᵉ h'ᵉ Qᵉ ＝ᵉ equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ ((hᵉ ,ᵉ Pᵉ) ,ᵉ Hᵉ)
  eq-equiv-eq-one-value-equiv-is-set-quotientᵉ Pᵉ Qᵉ =
    apᵉ pr1ᵉ
      { xᵉ =
        pairᵉ
          ( pairᵉ h'ᵉ Qᵉ)
          ( coherence-square-maps-eq-one-value-emb-is-set-quotientᵉ
            ( is-emb-is-equivᵉ Qᵉ))}
      { yᵉ =
        centerᵉ
          ( unique-equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ ((hᵉ ,ᵉ Pᵉ) ,ᵉ Hᵉ))}
      ( eq-is-contrᵉ
        ( unique-equiv-is-set-quotientᵉ Rᵉ QRᵉ fᵉ Rᵉ QRᵉ fᵉ Ufᵉ Ufᵉ ((hᵉ ,ᵉ Pᵉ) ,ᵉ Hᵉ)))
```