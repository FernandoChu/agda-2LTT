# The Cantor–Schröder–Bernstein–Escardó theorem

```agda
module foundation.cantor-schroder-bernstein-escardoᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.law-of-excluded-middleᵉ
open import foundation.perfect-imagesᵉ
open import foundation.split-surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.negationᵉ
```

</details>

## Idea

Theᵉ classicalᵉ Cantor–Schröder–Bernsteinᵉ theoremᵉ assertsᵉ thatᵉ fromᵉ anyᵉ pairᵉ ofᵉ
[injectiveᵉ maps](foundation-core.injective-maps.mdᵉ) `fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Bᵉ → A`ᵉ
weᵉ canᵉ constructᵉ aᵉ bijectionᵉ betweenᵉ `A`ᵉ andᵉ `B`.ᵉ Inᵉ aᵉ recentᵉ generalization,ᵉ
Escardóᵉ provedᵉ thatᵉ aᵉ Cantor–Schröder–Bernsteinᵉ theoremᵉ alsoᵉ holdsᵉ forᵉ
∞-groupoids.ᵉ Hisᵉ generalizationᵉ assertsᵉ thatᵉ givenᵉ twoᵉ typesᵉ thatᵉ
[embed](foundation-core.embeddings.mdᵉ) intoᵉ eachᵉ other,ᵉ thenᵉ theᵉ typesᵉ areᵉ
[equivalent](foundation-core.equivalences.md).ᵉ {{#citeᵉ Esc21ᵉ}}

## Statement

```agda
type-Cantor-Schröder-Bernstein-Escardóᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc (l1ᵉ ⊔ l2ᵉ))
type-Cantor-Schröder-Bernstein-Escardóᵉ l1ᵉ l2ᵉ =
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → (Xᵉ ↪ᵉ Yᵉ) → (Yᵉ ↪ᵉ Xᵉ) → Xᵉ ≃ᵉ Yᵉ
```

## Proof

### The law of excluded middle implies Cantor-Schröder-Bernstein-Escardó

```agda
module _
  {l1ᵉ l2ᵉ : Level} (lemᵉ : LEMᵉ (l1ᵉ ⊔ l2ᵉ))
  where

  module _
    {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ ↪ᵉ Yᵉ) (gᵉ : Yᵉ ↪ᵉ Xᵉ)
    where

    map-Cantor-Schröder-Bernstein-Escardó'ᵉ :
      (xᵉ : Xᵉ) → is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) xᵉ) → Yᵉ
    map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ (inlᵉ yᵉ) =
      inverse-of-perfect-imageᵉ xᵉ yᵉ
    map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ (inrᵉ yᵉ) =
      map-embᵉ fᵉ xᵉ

    map-Cantor-Schröder-Bernstein-Escardóᵉ :
      Xᵉ → Yᵉ
    map-Cantor-Schröder-Bernstein-Escardóᵉ xᵉ =
      map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ
        ( is-decidable-is-perfect-image-is-embᵉ (is-emb-map-embᵉ gᵉ) lemᵉ xᵉ)

    is-injective-map-Cantor-Schröder-Bernstein-Escardóᵉ :
      is-injectiveᵉ map-Cantor-Schröder-Bernstein-Escardóᵉ
    is-injective-map-Cantor-Schröder-Bernstein-Escardóᵉ {xᵉ} {x'ᵉ} =
      lᵉ (is-decidable-is-perfect-image-is-embᵉ (is-emb-map-embᵉ gᵉ) lemᵉ xᵉ)
      (is-decidable-is-perfect-image-is-embᵉ (is-emb-map-embᵉ gᵉ) lemᵉ x'ᵉ)
      where
      lᵉ :
        (dᵉ : is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) xᵉ))
        (d'ᵉ : is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) x'ᵉ)) →
        ( map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ dᵉ) ＝ᵉ
        ( map-Cantor-Schröder-Bernstein-Escardó'ᵉ x'ᵉ d'ᵉ) →
        xᵉ ＝ᵉ x'ᵉ
      lᵉ (inlᵉ ρᵉ) (inlᵉ ρ'ᵉ) pᵉ =
        invᵉ (is-section-inverse-of-perfect-imageᵉ xᵉ ρᵉ) ∙ᵉ
          (apᵉ (map-embᵉ gᵉ) pᵉ ∙ᵉ is-section-inverse-of-perfect-imageᵉ x'ᵉ ρ'ᵉ)
      lᵉ (inlᵉ ρᵉ) (inrᵉ nρ'ᵉ) pᵉ =
        ex-falsoᵉ (perfect-image-has-distinct-imageᵉ x'ᵉ xᵉ nρ'ᵉ ρᵉ (invᵉ pᵉ))
      lᵉ (inrᵉ nρᵉ) (inlᵉ ρ'ᵉ) pᵉ =
        ex-falsoᵉ (perfect-image-has-distinct-imageᵉ xᵉ x'ᵉ nρᵉ ρ'ᵉ pᵉ)
      lᵉ (inrᵉ nρᵉ) (inrᵉ nρ'ᵉ) pᵉ =
        is-injective-is-embᵉ (is-emb-map-embᵉ fᵉ) pᵉ

    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardóᵉ :
      is-split-surjectiveᵉ map-Cantor-Schröder-Bernstein-Escardóᵉ
    is-split-surjective-map-Cantor-Schröder-Bernstein-Escardóᵉ yᵉ =
      pairᵉ xᵉ pᵉ
      where
      aᵉ :
        is-decidableᵉ
          ( is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) (map-embᵉ gᵉ yᵉ)) →
        Σᵉ ( Xᵉ)
          ( λ xᵉ →
            ( (dᵉ : is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) xᵉ)) →
              map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ dᵉ ＝ᵉ yᵉ))
      aᵉ (inlᵉ γᵉ) =
        pairᵉ (map-embᵉ gᵉ yᵉ) ψᵉ
        where
        ψᵉ :
          ( dᵉ :
            is-decidableᵉ
              ( is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) (map-embᵉ gᵉ yᵉ))) →
          map-Cantor-Schröder-Bernstein-Escardó'ᵉ (map-embᵉ gᵉ yᵉ) dᵉ ＝ᵉ yᵉ
        ψᵉ (inlᵉ v'ᵉ) =
          is-retraction-inverse-of-perfect-imageᵉ
            { is-emb-gᵉ = is-emb-map-embᵉ gᵉ}
            ( yᵉ)
            ( v'ᵉ)
        ψᵉ (inrᵉ vᵉ) = ex-falsoᵉ (vᵉ γᵉ)
      aᵉ (inrᵉ γᵉ) =
        pairᵉ xᵉ ψᵉ
        where
        wᵉ :
          Σᵉ ( fiberᵉ (map-embᵉ fᵉ) yᵉ)
            ( λ sᵉ → ¬ᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) (pr1ᵉ sᵉ)))
        wᵉ =
          not-perfect-image-has-not-perfect-fiberᵉ
            ( is-emb-map-embᵉ fᵉ)
            ( is-emb-map-embᵉ gᵉ)
            ( lemᵉ)
            ( yᵉ)
            ( γᵉ)
        xᵉ : Xᵉ
        xᵉ = pr1ᵉ (pr1ᵉ wᵉ)
        pᵉ : map-embᵉ fᵉ xᵉ ＝ᵉ yᵉ
        pᵉ = pr2ᵉ (pr1ᵉ wᵉ)
        ψᵉ :
          ( dᵉ : is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) xᵉ)) →
          map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ dᵉ ＝ᵉ yᵉ
        ψᵉ (inlᵉ vᵉ) = ex-falsoᵉ ((pr2ᵉ wᵉ) vᵉ)
        ψᵉ (inrᵉ vᵉ) = pᵉ
      bᵉ :
        Σᵉ ( Xᵉ)
          ( λ xᵉ →
            ( (dᵉ : is-decidableᵉ (is-perfect-imageᵉ (map-embᵉ fᵉ) (map-embᵉ gᵉ) xᵉ)) →
              map-Cantor-Schröder-Bernstein-Escardó'ᵉ xᵉ dᵉ ＝ᵉ yᵉ))
      bᵉ =
        aᵉ ( is-decidable-is-perfect-image-is-embᵉ
            ( is-emb-map-embᵉ gᵉ)
            ( lemᵉ)
            ( map-embᵉ gᵉ yᵉ))
      xᵉ : Xᵉ
      xᵉ = pr1ᵉ bᵉ
      pᵉ : map-Cantor-Schröder-Bernstein-Escardóᵉ xᵉ ＝ᵉ yᵉ
      pᵉ = pr2ᵉ bᵉ (is-decidable-is-perfect-image-is-embᵉ (is-emb-map-embᵉ gᵉ) lemᵉ xᵉ)

    is-equiv-map-Cantor-Schröder-Bernstein-Escardóᵉ :
      is-equivᵉ map-Cantor-Schröder-Bernstein-Escardóᵉ
    is-equiv-map-Cantor-Schröder-Bernstein-Escardóᵉ =
      is-equiv-is-split-surjective-is-injectiveᵉ
        map-Cantor-Schröder-Bernstein-Escardóᵉ
        is-injective-map-Cantor-Schröder-Bernstein-Escardóᵉ
        is-split-surjective-map-Cantor-Schröder-Bernstein-Escardóᵉ

  Cantor-Schröder-Bernstein-Escardóᵉ :
    type-Cantor-Schröder-Bernstein-Escardóᵉ l1ᵉ l2ᵉ
  pr1ᵉ (Cantor-Schröder-Bernstein-Escardóᵉ fᵉ gᵉ) =
    map-Cantor-Schröder-Bernstein-Escardóᵉ fᵉ gᵉ
  pr2ᵉ (Cantor-Schröder-Bernstein-Escardóᵉ fᵉ gᵉ) =
    is-equiv-map-Cantor-Schröder-Bernstein-Escardóᵉ fᵉ gᵉ
```

## References

-ᵉ Escardó'sᵉ formalizationsᵉ regardingᵉ thisᵉ theoremᵉ canᵉ beᵉ foundᵉ atᵉ
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.index.html>.ᵉ
  {{#citeᵉ TypeTopologyᵉ}}

{{#bibliographyᵉ}}