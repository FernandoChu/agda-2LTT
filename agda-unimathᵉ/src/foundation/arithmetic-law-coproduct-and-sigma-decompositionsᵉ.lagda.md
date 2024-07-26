# Arithmetic law for coproduct decomposition and Σ-decomposition

```agda
module foundation.arithmetic-law-coproduct-and-sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-decompositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.relaxed-sigma-decompositionsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Letᵉ `X`ᵉ beᵉ aᵉ type,ᵉ weᵉ haveᵉ theᵉ followingᵉ equivalenceᵉ :

```text
  Σᵉ ( (Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) : Relaxed-Σ-Decompositionᵉ Xᵉ)
    ( binary-coproduct-Decompositionᵉ Uᵉ) ≃ᵉ
  Σᵉ ( (Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) : binary-coproduct-Decompositionᵉ Xᵉ)
    ( Relaxed-Σ-Decompositionᵉ Aᵉ ×ᵉ
      Relaxed-Σ-Decompositionᵉ Bᵉ )
```

Weᵉ alsoᵉ showᵉ aᵉ computationalᵉ ruleᵉ to simplifyᵉ theᵉ useᵉ ofᵉ thisᵉ equivalence.ᵉ

## Propositions

### Coproduct decomposition of the indexing type of a relaxed Σ-decomposition are equivalent to relaxed Σ-decomposition of the left and right summand of a coproduct decomposition

```agda
module _
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ}
  where

  private
    reassociateᵉ :
      Σᵉ (Relaxed-Σ-Decompositionᵉ lᵉ lᵉ Xᵉ)
        ( λ dᵉ → binary-coproduct-Decompositionᵉ lᵉ lᵉ
          ( indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ)) ≃ᵉ
        Σᵉ ( UUᵉ lᵉ)
          ( λ Aᵉ →
            Σᵉ ( UUᵉ lᵉ)
              ( λ Bᵉ →
                Σᵉ ( Σᵉ ( UUᵉ lᵉ) λ Uᵉ → ( Uᵉ ≃ᵉ (Aᵉ +ᵉ Bᵉ)))
                  ( λ Uᵉ → Σᵉ (pr1ᵉ Uᵉ → UUᵉ lᵉ) (λ Yᵉ → Xᵉ ≃ᵉ Σᵉ (pr1ᵉ Uᵉ) Yᵉ))))
    pr1ᵉ reassociateᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ fᵉ) ,ᵉ Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) = (Aᵉ ,ᵉ Bᵉ ,ᵉ (Uᵉ ,ᵉ eᵉ) ,ᵉ Vᵉ ,ᵉ fᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (Aᵉ ,ᵉ Bᵉ ,ᵉ (Uᵉ ,ᵉ eᵉ) ,ᵉ Vᵉ ,ᵉ fᵉ) → ((Uᵉ ,ᵉ Vᵉ ,ᵉ fᵉ) ,ᵉ Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( UUᵉ lᵉ)
        ( λ Aᵉ →
          Σᵉ ( UUᵉ lᵉ)
            ( λ Bᵉ →
              Σᵉ ( (Aᵉ → UUᵉ lᵉ) ×ᵉ (Bᵉ → UUᵉ lᵉ))
                ( λ (YAᵉ ,ᵉ YBᵉ) →
                  Σᵉ ( Σᵉ (UUᵉ lᵉ) (λ A'ᵉ → A'ᵉ ≃ᵉ Σᵉ Aᵉ YAᵉ))
                    ( λ A'ᵉ →
                      Σᵉ ( Σᵉ (UUᵉ lᵉ) (λ B'ᵉ → B'ᵉ ≃ᵉ Σᵉ Bᵉ YBᵉ))
                        ( λ B'ᵉ → Xᵉ ≃ᵉ (pr1ᵉ A'ᵉ +ᵉ pr1ᵉ B'ᵉ)))))) ≃ᵉ
      Σᵉ ( binary-coproduct-Decompositionᵉ lᵉ lᵉ Xᵉ)
      ( λ dᵉ →
        Relaxed-Σ-Decompositionᵉ lᵉ lᵉ
          ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) ×ᵉ
        Relaxed-Σ-Decompositionᵉ lᵉ lᵉ
          ( right-summand-binary-coproduct-Decompositionᵉ dᵉ))
    pr1ᵉ reassociate'ᵉ (Aᵉ ,ᵉ Bᵉ ,ᵉ (YAᵉ ,ᵉ YBᵉ) ,ᵉ (A'ᵉ ,ᵉ eAᵉ) ,ᵉ (B'ᵉ ,ᵉ eBᵉ) ,ᵉ eᵉ) =
      (A'ᵉ ,ᵉ B'ᵉ ,ᵉ eᵉ) ,ᵉ ((Aᵉ ,ᵉ YAᵉ ,ᵉ eAᵉ) ,ᵉ Bᵉ ,ᵉ YBᵉ ,ᵉ eBᵉ)
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ((A'ᵉ ,ᵉ B'ᵉ ,ᵉ eᵉ) ,ᵉ ((Aᵉ ,ᵉ YAᵉ ,ᵉ eAᵉ) ,ᵉ Bᵉ ,ᵉ YBᵉ ,ᵉ eBᵉ)) →
          (Aᵉ ,ᵉ Bᵉ ,ᵉ (YAᵉ ,ᵉ YBᵉ) ,ᵉ (A'ᵉ ,ᵉ eAᵉ) ,ᵉ (B'ᵉ ,ᵉ eBᵉ) ,ᵉ eᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ :
    Σᵉ ( Relaxed-Σ-Decompositionᵉ lᵉ lᵉ Xᵉ)
      ( λ dᵉ →
        binary-coproduct-Decompositionᵉ lᵉ lᵉ
          ( indexing-type-Relaxed-Σ-Decompositionᵉ dᵉ)) ≃ᵉ
    Σᵉ ( binary-coproduct-Decompositionᵉ lᵉ lᵉ Xᵉ)
      ( λ dᵉ →
        Relaxed-Σ-Decompositionᵉ lᵉ lᵉ
          ( left-summand-binary-coproduct-Decompositionᵉ dᵉ) ×ᵉ
        Relaxed-Σ-Decompositionᵉ lᵉ lᵉ
          ( right-summand-binary-coproduct-Decompositionᵉ dᵉ))

  equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ =
    ( ( reassociate'ᵉ) ∘eᵉ
      ( ( equiv-totᵉ
            ( λ Aᵉ →
              equiv-totᵉ
                ( λ Bᵉ →
                  ( ( equiv-totᵉ
                        ( λ ( YAᵉ ,ᵉ YBᵉ) →
                          ( ( equiv-totᵉ
                              ( λ A'ᵉ →
                                equiv-totᵉ
                                  ( λ B'ᵉ →
                                    equiv-postcomp-equivᵉ
                                      ( equiv-coproductᵉ
                                        ( inv-equivᵉ (pr2ᵉ A'ᵉ))
                                        ( inv-equivᵉ (pr2ᵉ B'ᵉ)))
                                      ( Xᵉ))) ∘eᵉ
                            ( ( inv-left-unit-law-Σ-is-contrᵉ
                                  ( is-torsorial-equiv'ᵉ (Σᵉ Aᵉ YAᵉ))
                                  ( Σᵉ Aᵉ YAᵉ ,ᵉ id-equivᵉ)) ∘eᵉ
                              ( inv-left-unit-law-Σ-is-contrᵉ
                                  ( is-torsorial-equiv'ᵉ (Σᵉ Bᵉ YBᵉ))
                                  ( Σᵉ Bᵉ YBᵉ ,ᵉ id-equivᵉ)))))) ∘eᵉ
                    ( ( equiv-Σ-equiv-baseᵉ
                          ( λ (YAᵉ ,ᵉ YBᵉ) → Xᵉ ≃ᵉ (Σᵉ Aᵉ YAᵉ +ᵉ Σᵉ Bᵉ YBᵉ))
                          ( equiv-universal-property-coproductᵉ (UUᵉ lᵉ))) ∘eᵉ
                      ( ( equiv-totᵉ
                            ( λ Yᵉ →
                              equiv-postcomp-equivᵉ
                                ( right-distributive-Σ-coproductᵉ Aᵉ Bᵉ Yᵉ)
                                ( Xᵉ))) ∘eᵉ
                          ( left-unit-law-Σ-is-contrᵉ
                              ( is-torsorial-equiv'ᵉ (Aᵉ +ᵉ Bᵉ))
                              ((Aᵉ +ᵉ Bᵉ) ,ᵉ id-equivᵉ))))))))) ∘eᵉ
      ( reassociateᵉ)))

  module _
    ( Dᵉ : Σᵉ ( Relaxed-Σ-Decompositionᵉ lᵉ lᵉ Xᵉ)
            ( λ Dᵉ →
              binary-coproduct-Decompositionᵉ
                lᵉ lᵉ
                ( indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ)))
    where

    private
      tr-total-equivᵉ :
        {l1ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ Yᵉ : UUᵉ l1ᵉ} (eᵉ : Yᵉ ≃ᵉ Xᵉ) →
        (hᵉ : Idᵉ {Aᵉ = Σᵉ (UUᵉ l1ᵉ) λ Yᵉ → Yᵉ ≃ᵉ Xᵉ} (Xᵉ ,ᵉ id-equivᵉ) (Yᵉ ,ᵉ eᵉ)) →
        {Cᵉ : (Xᵉ : UUᵉ l1ᵉ) → (Xᵉ → UUᵉ l3ᵉ) → UUᵉ l4ᵉ} →
        {fᵉ : Σᵉ (Yᵉ → UUᵉ l3ᵉ) (λ Zᵉ → Cᵉ Yᵉ Zᵉ)} →
        (xᵉ : Xᵉ) →
        pr1ᵉ
          ( trᵉ
            ( λ Yᵉ →
              ( Σᵉ ( pr1ᵉ Yᵉ → UUᵉ l3ᵉ)
                  ( λ Zᵉ → Cᵉ (pr1ᵉ Yᵉ) Zᵉ) →
                Σᵉ ( Xᵉ → UUᵉ l3ᵉ)
                  ( λ Zᵉ → Cᵉ Xᵉ Zᵉ)))
            ( hᵉ)
            ( idᵉ)
            ( fᵉ))
          ( xᵉ) ＝ᵉ
        pr1ᵉ fᵉ (map-inv-equivᵉ eᵉ xᵉ)
      tr-total-equivᵉ eᵉ reflᵉ xᵉ = reflᵉ

    compute-left-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ :
      ( aᵉ : left-summand-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ)) →
      cotype-Relaxed-Σ-Decompositionᵉ
        ( pr1ᵉ
          ( pr2ᵉ
            ( map-equivᵉ equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ
              ( Dᵉ))))
        ( aᵉ) ＝ᵉ
      cotype-Relaxed-Σ-Decompositionᵉ
        ( pr1ᵉ Dᵉ)
        ( map-inv-equivᵉ
          ( matching-correspondence-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ))
          ( inlᵉ aᵉ))
    compute-left-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ aᵉ =
      tr-total-equivᵉ
        ( matching-correspondence-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ))
        ( invᵉ
            ( contractionᵉ
                ( is-torsorial-equiv'ᵉ (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
                ( (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) ,ᵉ id-equivᵉ)) ∙ᵉ
          contractionᵉ
            ( is-torsorial-equiv'ᵉ (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
                ( pr1ᵉ (pr1ᵉ Dᵉ) ,ᵉ pr2ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
        ( inlᵉ aᵉ)

    compute-right-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ :
      ( bᵉ : right-summand-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ)) →
      cotype-Relaxed-Σ-Decompositionᵉ
        ( pr2ᵉ
          ( pr2ᵉ
            ( map-equivᵉ equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ
              ( Dᵉ))))
        ( bᵉ) ＝ᵉ
      cotype-Relaxed-Σ-Decompositionᵉ (pr1ᵉ Dᵉ)
        ( map-inv-equivᵉ
          ( matching-correspondence-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ))
          ( inrᵉ bᵉ))
    compute-right-equiv-binary-coproduct-Decomposition-Σ-Decompositionᵉ bᵉ =
      tr-total-equivᵉ
          ( matching-correspondence-binary-coproduct-Decompositionᵉ (pr2ᵉ Dᵉ))
          ( invᵉ
              ( contractionᵉ
                  ( is-torsorial-equiv'ᵉ (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
                  ( (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))) ,ᵉ id-equivᵉ)) ∙ᵉ
            contractionᵉ
              ( is-torsorial-equiv'ᵉ (pr1ᵉ (pr2ᵉ Dᵉ) +ᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
                  ( pr1ᵉ (pr1ᵉ Dᵉ) ,ᵉ pr2ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))))
          ( inrᵉ bᵉ)
```