# Perfect images

```agda
module foundation.perfect-imagesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.law-of-excluded-middleᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ mapsᵉ `fᵉ : Aᵉ → B`ᵉ andᵉ `gᵉ : Bᵉ → A`.ᵉ Forᵉ `(gᵉ ◦ᵉ f)ⁿ(a₀ᵉ) ＝ᵉ a`,ᵉ considerᵉ
alsoᵉ theᵉ followingᵉ chainᵉ

```text
      fᵉ          gᵉ            fᵉ               gᵉ       gᵉ
  a₀ᵉ -->ᵉ fᵉ (a₀ᵉ) -->ᵉ g(f(a₀ᵉ)) -->ᵉ f(g(f(a₀ᵉ))) -->ᵉ ... -->ᵉ (gᵉ ◦ᵉ f)ⁿ(a₀ᵉ) ＝ᵉ aᵉ
```

Weᵉ sayᵉ `a₀`ᵉ isᵉ anᵉ {{#conceptᵉ "origin"ᵉ}} forᵉ `a`,ᵉ andᵉ `a`ᵉ isᵉ aᵉ
{{#conceptᵉ "perfectᵉ image"ᵉ Agda=is-perfect-imageᵉ}} forᵉ `g`ᵉ ifᵉ anyᵉ originᵉ ofᵉ `a`ᵉ
isᵉ in theᵉ [image](foundation.images.mdᵉ) ofᵉ `g`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Bᵉ → Aᵉ)
  where

  is-perfect-imageᵉ : (aᵉ : Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-perfect-imageᵉ aᵉ =
    (a₀ᵉ : Aᵉ) (nᵉ : ℕᵉ) → (iterateᵉ nᵉ (gᵉ ∘ᵉ fᵉ)) a₀ᵉ ＝ᵉ aᵉ → fiberᵉ gᵉ a₀ᵉ
```

## Properties

Ifᵉ `g`ᵉ isᵉ anᵉ [embedding](foundation-core.embeddings.md),ᵉ thenᵉ
`is-perfect-imageᵉ a`ᵉ isᵉ aᵉ [proposition](foundation-core.propositions.md).ᵉ Inᵉ
thisᵉ case,ᵉ ifᵉ weᵉ assumeᵉ theᵉ
[lawᵉ ofᵉ exludedᵉ middle](foundation.law-of-excluded-middle.md),ᵉ weᵉ canᵉ showᵉ
`is-perfect-imageᵉ a`ᵉ isᵉ aᵉ [decidableᵉ type](foundation.decidable-types.mdᵉ) forᵉ
anyᵉ `aᵉ : A`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} (is-emb-gᵉ : is-embᵉ gᵉ)
  where

  is-prop-is-perfect-image-is-embᵉ :
    (aᵉ : Aᵉ) → is-propᵉ (is-perfect-imageᵉ fᵉ gᵉ aᵉ)
  is-prop-is-perfect-image-is-embᵉ aᵉ =
    is-prop-iterated-Πᵉ 3 (λ a₀ᵉ nᵉ pᵉ → is-prop-map-is-embᵉ is-emb-gᵉ a₀ᵉ)

  is-perfect-image-Propᵉ : Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-perfect-image-Propᵉ aᵉ) = is-perfect-imageᵉ fᵉ gᵉ aᵉ
  pr2ᵉ (is-perfect-image-Propᵉ aᵉ) = is-prop-is-perfect-image-is-embᵉ aᵉ

  is-decidable-is-perfect-image-is-embᵉ :
    LEMᵉ (l1ᵉ ⊔ l2ᵉ) → (aᵉ : Aᵉ) → is-decidableᵉ (is-perfect-imageᵉ fᵉ gᵉ aᵉ)
  is-decidable-is-perfect-image-is-embᵉ lemᵉ aᵉ =
    lemᵉ (is-perfect-image-Propᵉ aᵉ)
```

Ifᵉ `a`ᵉ isᵉ aᵉ perfectᵉ imageᵉ forᵉ `g`,ᵉ thenᵉ `a`ᵉ hasᵉ aᵉ preimageᵉ underᵉ `g`.ᵉ Justᵉ takeᵉ
`nᵉ = zero`ᵉ in theᵉ definition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-perfect-image-is-fiberᵉ :
    {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} → (aᵉ : Aᵉ) →
    is-perfect-imageᵉ fᵉ gᵉ aᵉ → fiberᵉ gᵉ aᵉ
  is-perfect-image-is-fiberᵉ aᵉ ρᵉ = ρᵉ aᵉ 0 reflᵉ
```

Oneᵉ canᵉ defineᵉ aᵉ mapᵉ fromᵉ `A`ᵉ to `B`ᵉ restrictingᵉ theᵉ domainᵉ to theᵉ perfectᵉ
imagesᵉ ofᵉ `g`.ᵉ Thisᵉ givesᵉ aᵉ kindᵉ ofᵉ [section](foundation-core.sections.mdᵉ) ofᵉ g.ᵉ
Whenᵉ gᵉ isᵉ alsoᵉ anᵉ embedding,ᵉ theᵉ mapᵉ givesᵉ aᵉ kindᵉ ofᵉ
[retraction](foundation-core.retractions.mdᵉ) ofᵉ g.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  where

  inverse-of-perfect-imageᵉ :
    (aᵉ : Aᵉ) → (is-perfect-imageᵉ fᵉ gᵉ aᵉ) → Bᵉ
  inverse-of-perfect-imageᵉ aᵉ ρᵉ =
    pr1ᵉ (is-perfect-image-is-fiberᵉ aᵉ ρᵉ)

  is-section-inverse-of-perfect-imageᵉ :
    (aᵉ : Aᵉ) (ρᵉ : is-perfect-imageᵉ fᵉ gᵉ aᵉ) →
    gᵉ (inverse-of-perfect-imageᵉ aᵉ ρᵉ) ＝ᵉ aᵉ
  is-section-inverse-of-perfect-imageᵉ aᵉ ρᵉ =
    pr2ᵉ (is-perfect-image-is-fiberᵉ aᵉ ρᵉ)
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} {is-emb-gᵉ : is-embᵉ gᵉ}
  where

  is-retraction-inverse-of-perfect-imageᵉ :
    (bᵉ : Bᵉ) (ρᵉ : is-perfect-imageᵉ fᵉ gᵉ (gᵉ bᵉ)) →
    inverse-of-perfect-imageᵉ (gᵉ bᵉ) ρᵉ ＝ᵉ bᵉ
  is-retraction-inverse-of-perfect-imageᵉ bᵉ ρᵉ =
    is-injective-is-embᵉ
      is-emb-gᵉ
      (is-section-inverse-of-perfect-imageᵉ (gᵉ bᵉ) ρᵉ)
```

Ifᵉ `g(f(a))`ᵉ isᵉ aᵉ perfectᵉ imageᵉ forᵉ `g`,ᵉ soᵉ isᵉ `a`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  where

  previous-perfect-imageᵉ :
    (aᵉ : Aᵉ) →
    is-perfect-imageᵉ fᵉ gᵉ (gᵉ (fᵉ (aᵉ))) →
    is-perfect-imageᵉ fᵉ gᵉ aᵉ
  previous-perfect-imageᵉ aᵉ γᵉ a₀ᵉ nᵉ pᵉ = γᵉ a₀ᵉ (succ-ℕᵉ nᵉ) (apᵉ (gᵉ ∘ᵉ fᵉ) pᵉ)
```

Perfectᵉ imagesᵉ goesᵉ to aᵉ disjointᵉ placeᵉ underᵉ `inverse-of-perfect-image`ᵉ thanᵉ
`f`ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  where

  perfect-image-has-distinct-imageᵉ :
    (aᵉ a₀ᵉ : Aᵉ) → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ aᵉ) → (ρᵉ : is-perfect-imageᵉ fᵉ gᵉ a₀ᵉ) →
    fᵉ aᵉ ≠ᵉ inverse-of-perfect-imageᵉ a₀ᵉ ρᵉ
  perfect-image-has-distinct-imageᵉ aᵉ a₀ᵉ nρᵉ ρᵉ pᵉ =
    vᵉ ρᵉ
    where
    qᵉ : gᵉ (fᵉ aᵉ) ＝ᵉ a₀ᵉ
    qᵉ = apᵉ gᵉ pᵉ ∙ᵉ is-section-inverse-of-perfect-imageᵉ a₀ᵉ ρᵉ

    sᵉ : ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (gᵉ (fᵉ aᵉ)))
    sᵉ = λ ηᵉ → nρᵉ (previous-perfect-imageᵉ aᵉ ηᵉ)

    vᵉ : ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ a₀ᵉ)
    vᵉ = trᵉ (λ _ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ _)) qᵉ sᵉ
```

Usingᵉ theᵉ propertyᵉ above,ᵉ weᵉ canᵉ talkᵉ aboutᵉ originsᵉ ofᵉ `a`ᵉ whichᵉ areᵉ notᵉ imagesᵉ
ofᵉ `g`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  where

  is-not-perfect-imageᵉ : (aᵉ : Aᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-not-perfect-imageᵉ aᵉ =
    Σᵉ Aᵉ (λ a₀ᵉ → (Σᵉ ℕᵉ (λ nᵉ → ((iterateᵉ nᵉ (gᵉ ∘ᵉ fᵉ)) a₀ᵉ ＝ᵉ aᵉ) ×ᵉ ¬ᵉ (fiberᵉ gᵉ a₀ᵉ))))
```

Ifᵉ weᵉ assumeᵉ theᵉ lawᵉ ofᵉ excludedᵉ middleᵉ andᵉ `g`ᵉ isᵉ anᵉ embedding,ᵉ weᵉ canᵉ proveᵉ
thatᵉ ifᵉ `is-not-perfect-imageᵉ a`ᵉ doesᵉ notᵉ hold,ᵉ weᵉ haveᵉ `is-perfect-imageᵉ a`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ} (is-emb-gᵉ : is-embᵉ gᵉ)
  (lemᵉ : LEMᵉ (l1ᵉ ⊔ l2ᵉ))
  where

  is-perfect-not-not-is-perfect-imageᵉ :
    (aᵉ : Aᵉ) → ¬ᵉ (is-not-perfect-imageᵉ aᵉ) → is-perfect-imageᵉ fᵉ gᵉ aᵉ
  is-perfect-not-not-is-perfect-imageᵉ aᵉ nρᵉ a₀ᵉ nᵉ pᵉ =
    rec-coproductᵉ
      ( idᵉ)
      ( λ a₁ᵉ → ex-falsoᵉ (nρᵉ (a₀ᵉ ,ᵉ nᵉ ,ᵉ pᵉ ,ᵉ a₁ᵉ)))
      ( lemᵉ (fiberᵉ gᵉ a₀ᵉ ,ᵉ is-prop-map-is-embᵉ is-emb-gᵉ a₀ᵉ))
```

Theᵉ followingᵉ propertyᵉ statesᵉ thatᵉ ifᵉ `gᵉ (b)`ᵉ isᵉ notᵉ aᵉ perfectᵉ image,ᵉ thenᵉ `b`ᵉ
hasᵉ anᵉ `f`ᵉ fiberᵉ `a`ᵉ thatᵉ isᵉ notᵉ aᵉ perfectᵉ imageᵉ forᵉ `g`.ᵉ Again,ᵉ weᵉ needᵉ to
assumeᵉ lawᵉ ofᵉ excludedᵉ middleᵉ andᵉ thatᵉ bothᵉ `g`ᵉ andᵉ `f`ᵉ areᵉ embedding.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Bᵉ → Aᵉ}
  (is-emb-fᵉ : is-embᵉ fᵉ) (is-emb-gᵉ : is-embᵉ gᵉ)
  (lemᵉ : LEMᵉ (l1ᵉ ⊔ l2ᵉ))
  where

  not-perfect-image-has-not-perfect-fiberᵉ :
      (bᵉ : Bᵉ) →
      ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (gᵉ bᵉ)) →
      Σᵉ (fiberᵉ fᵉ bᵉ) (λ sᵉ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ)))
  not-perfect-image-has-not-perfect-fiberᵉ bᵉ nρᵉ = vᵉ
      where
      iᵉ : ¬¬ᵉ (is-not-perfect-imageᵉ {fᵉ = fᵉ} (gᵉ bᵉ))
      iᵉ = λ nμᵉ → nρᵉ (is-perfect-not-not-is-perfect-imageᵉ is-emb-gᵉ lemᵉ (gᵉ bᵉ) nμᵉ)

      iiᵉ :
        is-not-perfect-imageᵉ (gᵉ bᵉ) →
        Σᵉ (fiberᵉ fᵉ bᵉ) (λ sᵉ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ)))
      iiᵉ (x₀ᵉ ,ᵉ 0 ,ᵉ uᵉ) =
        ex-falsoᵉ (pr2ᵉ uᵉ (bᵉ ,ᵉ invᵉ (pr1ᵉ uᵉ)))
      iiᵉ (x₀ᵉ ,ᵉ succ-ℕᵉ nᵉ ,ᵉ uᵉ) =
        aᵉ ,ᵉ wᵉ
        where
        qᵉ : fᵉ (iterateᵉ nᵉ (gᵉ ∘ᵉ fᵉ) x₀ᵉ) ＝ᵉ bᵉ
        qᵉ = is-injective-is-embᵉ is-emb-gᵉ (pr1ᵉ uᵉ)

        aᵉ : fiberᵉ fᵉ bᵉ
        aᵉ = iterateᵉ nᵉ (gᵉ ∘ᵉ fᵉ) x₀ᵉ ,ᵉ qᵉ

        wᵉ : ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ ((iterateᵉ nᵉ (gᵉ ∘ᵉ fᵉ)) x₀ᵉ))
        wᵉ = λ sᵉ → pr2ᵉ uᵉ (sᵉ x₀ᵉ nᵉ reflᵉ)

      iiiᵉ : ¬¬ᵉ (Σᵉ (fiberᵉ fᵉ bᵉ) (λ sᵉ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ))))
      iiiᵉ = λ tᵉ → iᵉ (λ sᵉ → tᵉ (iiᵉ sᵉ))

      ivᵉ : is-propᵉ (Σᵉ (fiberᵉ fᵉ bᵉ) (λ sᵉ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ))))
      ivᵉ =
        is-prop-Σᵉ
          (is-prop-map-is-embᵉ is-emb-fᵉ bᵉ)
          (λ sᵉ → is-prop-negᵉ {Aᵉ = is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ)})

      vᵉ : Σᵉ (fiberᵉ fᵉ bᵉ) (λ sᵉ → ¬ᵉ (is-perfect-imageᵉ fᵉ gᵉ (pr1ᵉ sᵉ)))
      vᵉ = double-negation-elim-is-decidableᵉ (lemᵉ (ᵉ_ ,ᵉ ivᵉ)) iiiᵉ
```