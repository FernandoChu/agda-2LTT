# Equality in the fibers of a map

```agda
module foundation.equality-fibers-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Inᵉ theᵉ fileᵉ
[`foundation-core.fibers-of-maps`](foundation-core.fibers-of-maps.mdᵉ) weᵉ alreadyᵉ
gaveᵉ oneᵉ characterizationᵉ ofᵉ theᵉ identityᵉ typeᵉ ofᵉ `fiberᵉ fᵉ b`,ᵉ forᵉ anᵉ arbitraryᵉ
mapᵉ `fᵉ : Aᵉ → B`.ᵉ Hereᵉ weᵉ giveᵉ aᵉ secondᵉ characterization,ᵉ using theᵉ fibersᵉ ofᵉ theᵉ
actionᵉ onᵉ identificationsᵉ ofᵉ `f`.ᵉ

## Theorem

Forᵉ anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ anyᵉ `bᵉ : B`ᵉ andᵉ anyᵉ `xᵉ yᵉ : fiberᵉ fᵉ b`,ᵉ thereᵉ isᵉ anᵉ
equivalenceᵉ

```text
(xᵉ ＝ᵉ yᵉ) ≃ᵉ fiberᵉ (apᵉ fᵉ) (pr2ᵉ xᵉ ∙ᵉ invᵉ (pr2ᵉ yᵉ))
```

### Proof

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) {bᵉ : Bᵉ}
  where

  fiber-ap-eq-fiber-fiberwiseᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) (pᵉ : pr1ᵉ sᵉ ＝ᵉ pr1ᵉ tᵉ) →
    trᵉ (λ (aᵉ : Aᵉ) → fᵉ aᵉ ＝ᵉ bᵉ) pᵉ (pr2ᵉ sᵉ) ＝ᵉ pr2ᵉ tᵉ →
    apᵉ fᵉ pᵉ ＝ᵉ pr2ᵉ sᵉ ∙ᵉ invᵉ (pr2ᵉ tᵉ)
  fiber-ap-eq-fiber-fiberwiseᵉ (.x'ᵉ ,ᵉ pᵉ) (x'ᵉ ,ᵉ reflᵉ) reflᵉ =
    invᵉ ∘ᵉ concatᵉ right-unitᵉ reflᵉ

  abstract
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwiseᵉ :
      (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) → is-fiberwise-equivᵉ (fiber-ap-eq-fiber-fiberwiseᵉ sᵉ tᵉ)
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwiseᵉ (xᵉ ,ᵉ yᵉ) (.xᵉ ,ᵉ reflᵉ) reflᵉ =
      is-equiv-compᵉ
        ( invᵉ)
        ( concatᵉ right-unitᵉ reflᵉ)
        ( is-equiv-concatᵉ right-unitᵉ reflᵉ)
        ( is-equiv-invᵉ (yᵉ ∙ᵉ reflᵉ) reflᵉ)

  fiber-ap-eq-fiberᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) → sᵉ ＝ᵉ tᵉ →
    fiberᵉ (apᵉ fᵉ {xᵉ = pr1ᵉ sᵉ} {yᵉ = pr1ᵉ tᵉ}) (pr2ᵉ sᵉ ∙ᵉ invᵉ (pr2ᵉ tᵉ))
  pr1ᵉ (fiber-ap-eq-fiberᵉ sᵉ .sᵉ reflᵉ) = reflᵉ
  pr2ᵉ (fiber-ap-eq-fiberᵉ sᵉ .sᵉ reflᵉ) = invᵉ (right-invᵉ (pr2ᵉ sᵉ))

  triangle-fiber-ap-eq-fiberᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) →
    fiber-ap-eq-fiberᵉ sᵉ tᵉ ~ᵉ
    totᵉ (fiber-ap-eq-fiber-fiberwiseᵉ sᵉ tᵉ) ∘ᵉ pair-eq-Σᵉ {sᵉ = sᵉ} {tᵉ}
  triangle-fiber-ap-eq-fiberᵉ (xᵉ ,ᵉ reflᵉ) .(xᵉ ,ᵉ reflᵉ) reflᵉ = reflᵉ

  abstract
    is-equiv-fiber-ap-eq-fiberᵉ :
      (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) → is-equivᵉ (fiber-ap-eq-fiberᵉ sᵉ tᵉ)
    is-equiv-fiber-ap-eq-fiberᵉ sᵉ tᵉ =
      is-equiv-left-map-triangleᵉ
        ( fiber-ap-eq-fiberᵉ sᵉ tᵉ)
        ( totᵉ (fiber-ap-eq-fiber-fiberwiseᵉ sᵉ tᵉ))
        ( pair-eq-Σᵉ {sᵉ = sᵉ} {tᵉ})
        ( triangle-fiber-ap-eq-fiberᵉ sᵉ tᵉ)
        ( is-equiv-pair-eq-Σᵉ sᵉ tᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwiseᵉ sᵉ tᵉ))

  equiv-fiber-ap-eq-fiberᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) →
    (sᵉ ＝ᵉ tᵉ) ≃ᵉ fiberᵉ (apᵉ fᵉ {xᵉ = pr1ᵉ sᵉ} {yᵉ = pr1ᵉ tᵉ}) (pr2ᵉ sᵉ ∙ᵉ invᵉ (pr2ᵉ tᵉ))
  pr1ᵉ (equiv-fiber-ap-eq-fiberᵉ sᵉ tᵉ) = fiber-ap-eq-fiberᵉ sᵉ tᵉ
  pr2ᵉ (equiv-fiber-ap-eq-fiberᵉ sᵉ tᵉ) = is-equiv-fiber-ap-eq-fiberᵉ sᵉ tᵉ

  map-inv-fiber-ap-eq-fiberᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) →
    fiberᵉ (apᵉ fᵉ {xᵉ = pr1ᵉ sᵉ} {yᵉ = pr1ᵉ tᵉ}) (pr2ᵉ sᵉ ∙ᵉ invᵉ (pr2ᵉ tᵉ)) →
    sᵉ ＝ᵉ tᵉ
  map-inv-fiber-ap-eq-fiberᵉ (xᵉ ,ᵉ reflᵉ) (.xᵉ ,ᵉ pᵉ) (reflᵉ ,ᵉ uᵉ) =
    eq-pair-eq-fiberᵉ (apᵉ invᵉ uᵉ ∙ᵉ inv-invᵉ pᵉ)

  ap-pr1-map-inv-fiber-ap-eq-fiberᵉ :
    (sᵉ tᵉ : fiberᵉ fᵉ bᵉ) →
    (vᵉ : fiberᵉ (apᵉ fᵉ {xᵉ = pr1ᵉ sᵉ} {yᵉ = pr1ᵉ tᵉ}) (pr2ᵉ sᵉ ∙ᵉ invᵉ (pr2ᵉ tᵉ))) →
    apᵉ pr1ᵉ (map-inv-fiber-ap-eq-fiberᵉ sᵉ tᵉ vᵉ) ＝ᵉ pr1ᵉ vᵉ
  ap-pr1-map-inv-fiber-ap-eq-fiberᵉ (xᵉ ,ᵉ reflᵉ) (.xᵉ ,ᵉ pᵉ) (reflᵉ ,ᵉ uᵉ) =
    ap-pr1-eq-pair-eq-fiberᵉ (apᵉ invᵉ uᵉ ∙ᵉ inv-invᵉ pᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (xᵉ yᵉ : Aᵉ)
  where

  eq-fiber-fiber-apᵉ :
    (qᵉ : fᵉ xᵉ ＝ᵉ fᵉ yᵉ) → (xᵉ ,ᵉ qᵉ) ＝ᵉ (yᵉ ,ᵉ reflᵉ) → fiberᵉ (apᵉ fᵉ {xᵉ} {yᵉ}) qᵉ
  eq-fiber-fiber-apᵉ qᵉ =
    trᵉ (fiberᵉ (apᵉ fᵉ)) right-unitᵉ ∘ᵉ fiber-ap-eq-fiberᵉ fᵉ (xᵉ ,ᵉ qᵉ) (yᵉ ,ᵉ reflᵉ)

  abstract
    is-equiv-eq-fiber-fiber-apᵉ :
      (qᵉ : (fᵉ xᵉ) ＝ᵉ fᵉ yᵉ) → is-equivᵉ (eq-fiber-fiber-apᵉ qᵉ)
    is-equiv-eq-fiber-fiber-apᵉ qᵉ =
      is-equiv-compᵉ
        ( trᵉ (fiberᵉ (apᵉ fᵉ)) right-unitᵉ)
        ( fiber-ap-eq-fiberᵉ fᵉ (xᵉ ,ᵉ qᵉ) (yᵉ ,ᵉ reflᵉ))
        ( is-equiv-fiber-ap-eq-fiberᵉ fᵉ (xᵉ ,ᵉ qᵉ) (yᵉ ,ᵉ reflᵉ))
        ( is-equiv-trᵉ (fiberᵉ (apᵉ fᵉ)) right-unitᵉ)
```

## Table of files about fibers of maps

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ fibersᵉ ofᵉ mapsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/fibers-of-maps.mdᵉ}}

## See also

-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ