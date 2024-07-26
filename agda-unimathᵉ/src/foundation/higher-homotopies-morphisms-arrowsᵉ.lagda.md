# Higher homotopies of morphisms of arrows

```agda
module foundation.higher-homotopies-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-concatenationᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)
`αᵉ :=ᵉ (iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ andᵉ `α'ᵉ :=ᵉ (i'ᵉ ,ᵉ j'ᵉ ,ᵉ H')`ᵉ andᵉ twoᵉ
[homotopiesᵉ ofᵉ morphismsᵉ ofᵉ arrows](foundation.homotopies-morphisms-arrows.mdᵉ)
`βᵉ :=ᵉ (Iᵉ ,ᵉ Jᵉ ,ᵉ K)`ᵉ andᵉ `β'ᵉ : (I'ᵉ ,ᵉ J'ᵉ ,ᵉ K')`ᵉ betweenᵉ them.ᵉ Aᵉ
{{#conceptᵉ "`2`-homotopyᵉ ofᵉ morphismsᵉ ofᵉ arrows"ᵉ Agda=htpy-htpy-hom-arrowᵉ}} isᵉ aᵉ
tripleᵉ `(γ₀,ᵉ γ₁ᵉ ,ᵉ γ₂)`ᵉ consistingᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ)

```text
  γ₀ᵉ : Iᵉ ~ᵉ I'ᵉ
  γ₁ᵉ : Jᵉ ~ᵉ J'ᵉ
```

andᵉ aᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ squareᵉ ofᵉ homotopiesᵉ

```text
                 left-whisker-concat-htpyᵉ Hᵉ (gᵉ ·ᵉ γ₀ᵉ)
  Hᵉ ∙ᵉ (gᵉ ·lᵉ Iᵉ) --------------------------------------->ᵉ Hᵉ ∙ᵉ (gᵉ ·ᵉ I'ᵉ)
       |                                                     |
     Kᵉ |                                                     | K'ᵉ
       ∨ᵉ                                                     ∨ᵉ
  (Jᵉ ·ᵉ fᵉ) ∙ᵉ H'ᵉ --------------------------------------->ᵉ (J'ᵉ ·ᵉ fᵉ) ∙ᵉ H'ᵉ
                right-whisker-concat-htpyᵉ (γ₁ᵉ ·ᵉ fᵉ) H'ᵉ
```

[commutes](foundation.commuting-squares-of-homotopies.md).ᵉ

## Definitions

### Homotopies of homotopies of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ α'ᵉ : hom-arrowᵉ fᵉ gᵉ)
  (βᵉ β'ᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ)
  where

  coherence-htpy-htpy-hom-arrowᵉ :
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ →
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-htpy-hom-arrowᵉ γ₀ᵉ γ₁ᵉ =
    coherence-square-homotopiesᵉ
      ( left-whisker-concat-htpyᵉ
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( left-whisker-comp²ᵉ gᵉ γ₀ᵉ))
      ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ)
      ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ)
      ( right-whisker-concat-htpyᵉ
        ( right-whisker-comp²ᵉ γ₁ᵉ fᵉ)
        ( coh-hom-arrowᵉ fᵉ gᵉ α'ᵉ))

  htpy-htpy-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-htpy-hom-arrowᵉ =
    Σᵉ ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
        htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ)
      ( λ γ₀ᵉ →
        Σᵉ ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
            htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ)
          ( coherence-htpy-htpy-hom-arrowᵉ γ₀ᵉ))

  module _
    (γᵉ : htpy-htpy-hom-arrowᵉ)
    where

    htpy-domain-htpy-htpy-hom-arrowᵉ :
      htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
      htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ
    htpy-domain-htpy-htpy-hom-arrowᵉ = pr1ᵉ γᵉ

    htpy-codomain-htpy-htpy-hom-arrowᵉ :
      htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
      htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ β'ᵉ
    htpy-codomain-htpy-htpy-hom-arrowᵉ = pr1ᵉ (pr2ᵉ γᵉ)

    coh-htpy-htpy-hom-arrowᵉ :
      coherence-htpy-htpy-hom-arrowᵉ
        ( htpy-domain-htpy-htpy-hom-arrowᵉ)
        ( htpy-codomain-htpy-htpy-hom-arrowᵉ)
    coh-htpy-htpy-hom-arrowᵉ = pr2ᵉ (pr2ᵉ γᵉ)
```

### The reflexivity homotopy of homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ α'ᵉ : hom-arrowᵉ fᵉ gᵉ)
  (βᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ)
  where

  htpy-domain-refl-htpy-htpy-hom-arrowᵉ :
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-domain-refl-htpy-htpy-hom-arrowᵉ = refl-htpyᵉ

  htpy-codomain-refl-htpy-htpy-hom-arrowᵉ :
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ~ᵉ
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-codomain-refl-htpy-htpy-hom-arrowᵉ = refl-htpyᵉ

  coh-refl-htpy-htpy-hom-arrowᵉ :
    coherence-htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ βᵉ
      ( htpy-domain-refl-htpy-htpy-hom-arrowᵉ)
      ( htpy-codomain-refl-htpy-htpy-hom-arrowᵉ)
  coh-refl-htpy-htpy-hom-arrowᵉ = right-unit-htpyᵉ

  refl-htpy-htpy-hom-arrowᵉ : htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ βᵉ
  pr1ᵉ refl-htpy-htpy-hom-arrowᵉ = htpy-domain-refl-htpy-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-htpy-hom-arrowᵉ) = htpy-codomain-refl-htpy-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-htpy-hom-arrowᵉ) = coh-refl-htpy-htpy-hom-arrowᵉ
```

## Properties

### Homotopies of homotopies of morphisms of arrows characterize equality of homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ α'ᵉ : hom-arrowᵉ fᵉ gᵉ)
  (βᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ)
  where

  htpy-eq-htpy-hom-arrowᵉ :
    (β'ᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ) → βᵉ ＝ᵉ β'ᵉ → htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ β'ᵉ
  htpy-eq-htpy-hom-arrowᵉ .βᵉ reflᵉ = refl-htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ

  is-torsorial-htpy-htpy-hom-arrowᵉ :
    is-torsorialᵉ (htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ)
  is-torsorial-htpy-htpy-hom-arrowᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ _)
      ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ _)
        ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ _))

  is-equiv-htpy-eq-htpy-hom-arrowᵉ :
    (β'ᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ) → is-equivᵉ (htpy-eq-htpy-hom-arrowᵉ β'ᵉ)
  is-equiv-htpy-eq-htpy-hom-arrowᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-htpy-hom-arrowᵉ)
      ( htpy-eq-htpy-hom-arrowᵉ)

  extensionality-htpy-hom-arrowᵉ :
    (β'ᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ) →
    (βᵉ ＝ᵉ β'ᵉ) ≃ᵉ htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ β'ᵉ
  pr1ᵉ (extensionality-htpy-hom-arrowᵉ β'ᵉ) = htpy-eq-htpy-hom-arrowᵉ β'ᵉ
  pr2ᵉ (extensionality-htpy-hom-arrowᵉ β'ᵉ) = is-equiv-htpy-eq-htpy-hom-arrowᵉ β'ᵉ

  eq-htpy-htpy-hom-arrowᵉ :
    (β'ᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ) →
    htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ β'ᵉ → βᵉ ＝ᵉ β'ᵉ
  eq-htpy-htpy-hom-arrowᵉ β'ᵉ = map-inv-equivᵉ (extensionality-htpy-hom-arrowᵉ β'ᵉ)
```

### The left unit law for concatenation of homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ α'ᵉ : hom-arrowᵉ fᵉ gᵉ)
  (βᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ)
  where

  htpy-domain-left-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-domain-concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ αᵉ α'ᵉ (refl-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ) βᵉ ~ᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-domain-left-unit-law-concat-htpy-hom-arrowᵉ = refl-htpyᵉ

  htpy-codomain-left-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-codomain-concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ αᵉ α'ᵉ
      ( refl-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( βᵉ) ~ᵉ
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-codomain-left-unit-law-concat-htpy-hom-arrowᵉ = refl-htpyᵉ

  coh-left-unit-law-concat-htpy-hom-arrowᵉ :
    coherence-htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ
      ( concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ αᵉ α'ᵉ (refl-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ) βᵉ)
      ( βᵉ)
      ( htpy-domain-left-unit-law-concat-htpy-hom-arrowᵉ)
      ( htpy-codomain-left-unit-law-concat-htpy-hom-arrowᵉ)
  coh-left-unit-law-concat-htpy-hom-arrowᵉ aᵉ =
    ( right-unitᵉ) ∙ᵉ
    ( right-whisker-concatᵉ
      ( right-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
        ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ)))
      ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ))

  left-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ
      ( concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ αᵉ α'ᵉ (refl-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ) βᵉ)
      ( βᵉ)
  pr1ᵉ left-unit-law-concat-htpy-hom-arrowᵉ =
    htpy-domain-left-unit-law-concat-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ left-unit-law-concat-htpy-hom-arrowᵉ) =
    htpy-codomain-left-unit-law-concat-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ left-unit-law-concat-htpy-hom-arrowᵉ) =
    coh-left-unit-law-concat-htpy-hom-arrowᵉ
```

### The right unit law for concatenation of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ α'ᵉ : hom-arrowᵉ fᵉ gᵉ)
  (βᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ)
  where

  htpy-domain-right-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-domain-concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ α'ᵉ βᵉ
      ( refl-htpy-hom-arrowᵉ fᵉ gᵉ α'ᵉ) ~ᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-domain-right-unit-law-concat-htpy-hom-arrowᵉ = right-unit-htpyᵉ

  htpy-codomain-right-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-codomain-concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ α'ᵉ βᵉ
      ( refl-htpy-hom-arrowᵉ fᵉ gᵉ α'ᵉ) ~ᵉ
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ
  htpy-codomain-right-unit-law-concat-htpy-hom-arrowᵉ = right-unit-htpyᵉ

  coh-right-unit-law-concat-htpy-hom-arrowᵉ :
    coherence-htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ
      ( concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ α'ᵉ βᵉ (refl-htpy-hom-arrowᵉ fᵉ gᵉ α'ᵉ))
      ( βᵉ)
      ( htpy-domain-right-unit-law-concat-htpy-hom-arrowᵉ)
      ( htpy-codomain-right-unit-law-concat-htpy-hom-arrowᵉ)
  coh-right-unit-law-concat-htpy-hom-arrowᵉ aᵉ =
    ( assocᵉ
      ( left-whisker-concatᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) (ap-concatᵉ gᵉ _ reflᵉ))
      ( _)
      ( right-whisker-concatᵉ right-unitᵉ (coh-hom-arrowᵉ fᵉ gᵉ α'ᵉ aᵉ))) ∙ᵉ
    ( horizontal-concat-Id²ᵉ
      ( ( apᵉ
          ( left-whisker-concatᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
          ( compute-right-refl-ap-concatᵉ gᵉ
            ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ))) ∙ᵉ
        ( distributive-left-whisker-concat-concatᵉ
          ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
          ( apᵉ (apᵉ gᵉ) right-unitᵉ)
          ( invᵉ right-unitᵉ)))
      ( right-unit-law-horizontal-pasting-coherence-square-identificationsᵉ
        ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ (fᵉ aᵉ))
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
        ( coh-hom-arrowᵉ fᵉ gᵉ α'ᵉ aᵉ)
        ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ))
        ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ)) ∙ᵉ
      ( unsplice-concat'ᵉ
        ( left-whisker-concatᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) (apᵉ (apᵉ gᵉ) right-unitᵉ))
        ( compute-inv-left-whisker-concatᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) right-unitᵉ)
        ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ βᵉ aᵉ)))

  right-unit-law-concat-htpy-hom-arrowᵉ :
    htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ
      ( concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ α'ᵉ α'ᵉ βᵉ (refl-htpy-hom-arrowᵉ fᵉ gᵉ α'ᵉ))
      ( βᵉ)
  pr1ᵉ right-unit-law-concat-htpy-hom-arrowᵉ =
    htpy-domain-right-unit-law-concat-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ right-unit-law-concat-htpy-hom-arrowᵉ) =
    htpy-codomain-right-unit-law-concat-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ right-unit-law-concat-htpy-hom-arrowᵉ) =
    coh-right-unit-law-concat-htpy-hom-arrowᵉ
```