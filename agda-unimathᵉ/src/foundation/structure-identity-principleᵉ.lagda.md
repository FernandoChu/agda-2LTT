# The structure identity principle

```agda
module foundation.structure-identity-principleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

[Structure](foundation.structure.mdᵉ) isᵉ presentedᵉ in typeᵉ theoryᵉ byᵉ
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ Theᵉ **structureᵉ
identityᵉ principle**ᵉ isᵉ aᵉ wayᵉ to characterizeᵉ theᵉ
[identityᵉ type](foundation-core.identity-types.mdᵉ) ofᵉ aᵉ structure,ᵉ using
characterizationsᵉ ofᵉ theᵉ identityᵉ typesᵉ ofᵉ itsᵉ components.ᵉ

## Lemma

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  { Dᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ → UUᵉ l4ᵉ}
  where

  abstract
    is-torsorial-Eq-structureᵉ :
      (is-contr-ACᵉ : is-torsorialᵉ Cᵉ) (tᵉ : Σᵉ Aᵉ Cᵉ) →
      is-torsorialᵉ (λ yᵉ → Dᵉ (pr1ᵉ tᵉ) yᵉ (pr2ᵉ tᵉ)) →
      is-torsorialᵉ (λ tᵉ → Σᵉ (Cᵉ (pr1ᵉ tᵉ)) (Dᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ)))
    is-torsorial-Eq-structureᵉ is-contr-ACᵉ tᵉ is-contr-BDᵉ =
      is-contr-equivᵉ
        ( Σᵉ (Σᵉ Aᵉ Cᵉ) (λ tᵉ → Σᵉ (Bᵉ (pr1ᵉ tᵉ)) (λ yᵉ → Dᵉ (pr1ᵉ tᵉ) yᵉ (pr2ᵉ tᵉ))))
        ( interchange-Σ-Σᵉ Dᵉ)
        ( is-contr-Σᵉ is-contr-ACᵉ tᵉ is-contr-BDᵉ)
```

## Theorem

### The structure identity principle

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Eq-Aᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Eq-Bᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Eq-Aᵉ xᵉ → UUᵉ l4ᵉ)
  {aᵉ : Aᵉ} {bᵉ : Bᵉ aᵉ} (refl-Aᵉ : Eq-Aᵉ aᵉ) (refl-Bᵉ : Eq-Bᵉ bᵉ refl-Aᵉ)
  where

  abstract
    structure-identity-principleᵉ :
      {fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Eq-Aᵉ xᵉ}
      {gᵉ : (yᵉ : Bᵉ aᵉ) → bᵉ ＝ᵉ yᵉ → Eq-Bᵉ yᵉ refl-Aᵉ} →
      (hᵉ : (zᵉ : Σᵉ Aᵉ Bᵉ) → (pairᵉ aᵉ bᵉ) ＝ᵉ zᵉ → Σᵉ (Eq-Aᵉ (pr1ᵉ zᵉ)) (Eq-Bᵉ (pr2ᵉ zᵉ))) →
      ((xᵉ : Aᵉ) → is-equivᵉ (fᵉ xᵉ)) → ((yᵉ : Bᵉ aᵉ) → is-equivᵉ (gᵉ yᵉ)) →
      (zᵉ : Σᵉ Aᵉ Bᵉ) → is-equivᵉ (hᵉ zᵉ)
    structure-identity-principleᵉ {fᵉ} {gᵉ} hᵉ Hᵉ Kᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-structureᵉ
          ( fundamental-theorem-id'ᵉ fᵉ Hᵉ)
          ( pairᵉ aᵉ refl-Aᵉ)
          ( fundamental-theorem-id'ᵉ gᵉ Kᵉ))
        ( hᵉ)

  map-extensionality-Σᵉ :
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-Aᵉ xᵉ)
    (gᵉ : (yᵉ : Bᵉ aᵉ) → (bᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-Bᵉ yᵉ refl-Aᵉ) →
    (zᵉ : Σᵉ Aᵉ Bᵉ) → pairᵉ aᵉ bᵉ ＝ᵉ zᵉ → Σᵉ (Eq-Aᵉ (pr1ᵉ zᵉ)) (Eq-Bᵉ (pr2ᵉ zᵉ))
  pr1ᵉ (map-extensionality-Σᵉ fᵉ gᵉ .(pairᵉ aᵉ bᵉ) reflᵉ) = refl-Aᵉ
  pr2ᵉ (map-extensionality-Σᵉ fᵉ gᵉ .(pairᵉ aᵉ bᵉ) reflᵉ) = refl-Bᵉ

  extensionality-Σᵉ :
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-Aᵉ xᵉ)
    (gᵉ : (yᵉ : Bᵉ aᵉ) → (bᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-Bᵉ yᵉ refl-Aᵉ) →
    (zᵉ : Σᵉ Aᵉ Bᵉ) → (pairᵉ aᵉ bᵉ ＝ᵉ zᵉ) ≃ᵉ Σᵉ (Eq-Aᵉ (pr1ᵉ zᵉ)) (Eq-Bᵉ (pr2ᵉ zᵉ))
  pr1ᵉ (extensionality-Σᵉ fᵉ gᵉ zᵉ) = map-extensionality-Σᵉ fᵉ gᵉ zᵉ
  pr2ᵉ (extensionality-Σᵉ fᵉ gᵉ zᵉ) =
    structure-identity-principleᵉ
      ( map-extensionality-Σᵉ fᵉ gᵉ)
      ( λ xᵉ → is-equiv-map-equivᵉ (fᵉ xᵉ))
      ( λ yᵉ → is-equiv-map-equivᵉ (gᵉ yᵉ))
      ( zᵉ)
```