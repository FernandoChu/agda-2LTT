# Sections of dependent type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module type-theories.sections-dependent-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import type-theories.dependent-type-theoriesᵉ
open import type-theories.fibered-dependent-type-theoriesᵉ
```

</details>

```agda
open dependentᵉ
open fiberedᵉ

module sections-dttᵉ where

  precomp-fibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    (Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Bᵉ) (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ
  fibered-system.typeᵉ (precomp-fibered-systemᵉ Cᵉ fᵉ) Xᵉ =
    fibered-system.typeᵉ Cᵉ (section-system.typeᵉ fᵉ Xᵉ)
  fibered-system.elementᵉ (precomp-fibered-systemᵉ Cᵉ fᵉ) Yᵉ xᵉ =
    fibered-system.elementᵉ Cᵉ Yᵉ (section-system.elementᵉ fᵉ xᵉ)
  fibered-system.sliceᵉ (precomp-fibered-systemᵉ Cᵉ fᵉ) {Xᵉ} Yᵉ =
    precomp-fibered-systemᵉ
      ( fibered-system.sliceᵉ Cᵉ Yᵉ)
      ( section-system.sliceᵉ fᵉ Xᵉ)

  precomp-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : systemᵉ l3ᵉ l4ᵉ}
    {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Bᵉ}
    (gᵉ : section-systemᵉ Cᵉ) (fᵉ : hom-systemᵉ Aᵉ Bᵉ) →
    section-systemᵉ (precomp-fibered-systemᵉ Cᵉ fᵉ)
  section-system.typeᵉ (precomp-section-systemᵉ gᵉ fᵉ) Xᵉ =
    section-system.typeᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ)
  section-system.elementᵉ (precomp-section-systemᵉ gᵉ fᵉ) xᵉ =
    section-system.elementᵉ gᵉ (section-system.elementᵉ fᵉ xᵉ)
  section-system.sliceᵉ (precomp-section-systemᵉ gᵉ fᵉ) Xᵉ =
    precomp-section-systemᵉ
      ( section-system.sliceᵉ gᵉ (section-system.typeᵉ fᵉ Xᵉ))
      ( section-system.sliceᵉ fᵉ Xᵉ)

  transpose-bifibered-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ}
    {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ} {Cᵉ : fibered-systemᵉ l5ᵉ l6ᵉ Aᵉ}
    (Dᵉ : bifibered-systemᵉ l7ᵉ l8ᵉ Bᵉ Cᵉ) →
    bifibered-systemᵉ l7ᵉ l8ᵉ Cᵉ Bᵉ
  bifibered-system.typeᵉ (transpose-bifibered-systemᵉ Dᵉ) Zᵉ Yᵉ =
    bifibered-system.typeᵉ Dᵉ Yᵉ Zᵉ
  bifibered-system.elementᵉ (transpose-bifibered-systemᵉ Dᵉ) Wᵉ zᵉ yᵉ =
    bifibered-system.elementᵉ Dᵉ Wᵉ yᵉ zᵉ
  bifibered-system.sliceᵉ (transpose-bifibered-systemᵉ Dᵉ) Wᵉ =
    transpose-bifibered-systemᵉ (bifibered-system.sliceᵉ Dᵉ Wᵉ)

  postcomp-section-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {Cᵉ : systemᵉ l5ᵉ l6ᵉ} {Dᵉ : fibered-systemᵉ l7ᵉ l8ᵉ Cᵉ}
    {fᵉ : hom-systemᵉ Aᵉ Cᵉ} (gᵉ : hom-fibered-systemᵉ fᵉ Bᵉ Dᵉ)
    (hᵉ : section-systemᵉ Bᵉ) → section-systemᵉ (precomp-fibered-systemᵉ Dᵉ fᵉ)
  section-system.typeᵉ (postcomp-section-systemᵉ gᵉ hᵉ) Xᵉ =
    section-fibered-system.typeᵉ gᵉ (section-system.typeᵉ hᵉ Xᵉ)
  section-system.elementᵉ (postcomp-section-systemᵉ gᵉ hᵉ) xᵉ =
    section-fibered-system.elementᵉ gᵉ (section-system.elementᵉ hᵉ xᵉ)
  section-system.sliceᵉ (postcomp-section-systemᵉ gᵉ hᵉ) Xᵉ =
    postcomp-section-systemᵉ
      ( section-fibered-system.sliceᵉ gᵉ (section-system.typeᵉ hᵉ Xᵉ))
      ( section-system.sliceᵉ hᵉ Xᵉ)

  record preserves-weakening-section-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} (WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ)
    (fᵉ : section-systemᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        htpy-section-systemᵉ
          ( precomp-section-systemᵉ
            ( section-system.sliceᵉ fᵉ Xᵉ)
            ( weakening.typeᵉ WAᵉ Xᵉ))
          ( postcomp-section-systemᵉ
            ( fibered-weakening.typeᵉ WBᵉ (section-system.typeᵉ fᵉ Xᵉ))
            ( fᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-weakening-section-systemᵉ
          ( fibered-weakening.sliceᵉ WBᵉ (section-system.typeᵉ fᵉ Xᵉ))
          ( section-system.sliceᵉ fᵉ Xᵉ)

  record preserves-substitution-section-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {SAᵉ : substitutionᵉ Aᵉ} (SBᵉ : fibered-substitutionᵉ Bᵉ SAᵉ)
    (fᵉ : section-systemᵉ Bᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        {Xᵉ : system.typeᵉ Aᵉ} (xᵉ : system.elementᵉ Aᵉ Xᵉ) →
        htpy-section-systemᵉ
          ( precomp-section-systemᵉ fᵉ (substitution.typeᵉ SAᵉ xᵉ))
          ( postcomp-section-systemᵉ
            ( fibered-substitution.typeᵉ SBᵉ (section-system.elementᵉ fᵉ xᵉ))
            ( section-system.sliceᵉ fᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-substitution-section-systemᵉ
          ( fibered-substitution.sliceᵉ SBᵉ (section-system.typeᵉ fᵉ Xᵉ))
          ( section-system.sliceᵉ fᵉ Xᵉ)

  record preserves-generic-element-section-systemᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : systemᵉ l1ᵉ l2ᵉ} {Bᵉ : fibered-systemᵉ l3ᵉ l4ᵉ Aᵉ}
    {WAᵉ : weakeningᵉ Aᵉ} {δAᵉ : generic-elementᵉ WAᵉ}
    {WBᵉ : fibered-weakeningᵉ Bᵉ WAᵉ} (δBᵉ : fibered-generic-elementᵉ WBᵉ δAᵉ)
    {fᵉ : section-systemᵉ Bᵉ} (Wfᵉ : preserves-weakening-section-systemᵉ WBᵉ fᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    coinductiveᵉ
    field
      typeᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        Idᵉ
          ( trᵉ
            ( λ tᵉ →
              fibered-system.elementᵉ
                ( fibered-system.sliceᵉ Bᵉ (section-system.typeᵉ fᵉ Xᵉ))
                ( tᵉ)
                ( generic-element.typeᵉ δAᵉ Xᵉ))
            ( section-system.typeᵉ
              ( preserves-weakening-section-system.typeᵉ Wfᵉ Xᵉ)
              ( Xᵉ))
            ( section-system.elementᵉ
              ( section-system.sliceᵉ fᵉ Xᵉ)
              ( generic-element.typeᵉ δAᵉ Xᵉ)))
            ( fibered-generic-element.typeᵉ δBᵉ (section-system.typeᵉ fᵉ Xᵉ))
      sliceᵉ :
        (Xᵉ : system.typeᵉ Aᵉ) →
        preserves-generic-element-section-systemᵉ
          ( fibered-generic-element.sliceᵉ δBᵉ (section-system.typeᵉ fᵉ Xᵉ))
          ( preserves-weakening-section-system.sliceᵉ Wfᵉ Xᵉ)

  record section-type-theoryᵉ
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Aᵉ : type-theoryᵉ l1ᵉ l2ᵉ}
    (Bᵉ : fibered-type-theoryᵉ l3ᵉ l4ᵉ Aᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    where
    field
      sysᵉ : section-systemᵉ (fibered-type-theory.sysᵉ Bᵉ)
      Wᵉ :
        preserves-weakening-section-systemᵉ
          ( fibered-type-theory.Wᵉ Bᵉ)
          ( sysᵉ)
      Sᵉ :
        preserves-substitution-section-systemᵉ
          ( fibered-type-theory.Sᵉ Bᵉ)
          ( sysᵉ)
      δᵉ :
        preserves-generic-element-section-systemᵉ
          ( fibered-type-theory.δᵉ Bᵉ)
          ( Wᵉ)
```