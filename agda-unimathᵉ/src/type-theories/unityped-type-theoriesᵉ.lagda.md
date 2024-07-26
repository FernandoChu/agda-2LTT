# Unityped type theories

```agda
{-# OPTIONSᵉ --guardednessᵉ --allow-unsolved-metasᵉ #-}

module type-theories.unityped-type-theoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Unitypedᵉ typeᵉ theoriesᵉ areᵉ typeᵉ theoriesᵉ in whichᵉ allᵉ termsᵉ haveᵉ theᵉ sameᵉ type.ᵉ
Theyᵉ areᵉ sometimesᵉ calledᵉ untypedᵉ typeᵉ theories.ᵉ Theᵉ categoryᵉ ofᵉ unitypedᵉ typeᵉ
theoriesᵉ isᵉ equivalentᵉ to theᵉ categoryᵉ ofᵉ singleᵉ sortedᵉ algebraicᵉ theories.ᵉ

## Definitions

```agda
module unitypedᵉ where

  record systemᵉ (lᵉ : Level) : UUᵉ (lsuc lᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : UUᵉ lᵉ
      sliceᵉ : systemᵉ lᵉ

  record system-Setᵉ (lᵉ : Level) : UUᵉ (lsuc lᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : Setᵉ lᵉ
      sliceᵉ : system-Setᵉ lᵉ

  record hom-systemᵉ
    {l1ᵉ l2ᵉ : Level} (σᵉ : systemᵉ l1ᵉ) (Tᵉ : systemᵉ l2ᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : system.elementᵉ σᵉ → system.elementᵉ Tᵉ
      sliceᵉ : hom-systemᵉ (system.sliceᵉ σᵉ) (system.sliceᵉ Tᵉ)

  id-hom-systemᵉ :
    {lᵉ : Level} (σᵉ : systemᵉ lᵉ) → hom-systemᵉ σᵉ σᵉ
  hom-system.elementᵉ (id-hom-systemᵉ σᵉ) = idᵉ
  hom-system.sliceᵉ (id-hom-systemᵉ σᵉ) = id-hom-systemᵉ (system.sliceᵉ σᵉ)

  comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {σᵉ : systemᵉ l1ᵉ} {τᵉ : systemᵉ l2ᵉ} {υᵉ : systemᵉ l3ᵉ}
    (βᵉ : hom-systemᵉ τᵉ υᵉ) (αᵉ : hom-systemᵉ σᵉ τᵉ) → hom-systemᵉ σᵉ υᵉ
  hom-system.elementᵉ (comp-hom-systemᵉ βᵉ αᵉ) =
    hom-system.elementᵉ βᵉ ∘ᵉ hom-system.elementᵉ αᵉ
  hom-system.sliceᵉ (comp-hom-systemᵉ βᵉ αᵉ) =
    comp-hom-systemᵉ (hom-system.sliceᵉ βᵉ) (hom-system.sliceᵉ αᵉ)

  record htpy-hom-systemᵉ
    {l1ᵉ l2ᵉ : Level}
    {σᵉ : systemᵉ l1ᵉ} {τᵉ : systemᵉ l2ᵉ} (gᵉ hᵉ : hom-systemᵉ σᵉ τᵉ) :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ : hom-system.elementᵉ gᵉ ~ᵉ hom-system.elementᵉ hᵉ
      sliceᵉ : htpy-hom-systemᵉ (hom-system.sliceᵉ gᵉ) (hom-system.sliceᵉ hᵉ)

  record weakeningᵉ
    {lᵉ : Level} (σᵉ : systemᵉ lᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ : hom-systemᵉ σᵉ (system.sliceᵉ σᵉ)
      sliceᵉ : weakeningᵉ (system.sliceᵉ σᵉ)

  record preserves-weakeningᵉ
    {l1ᵉ l2ᵉ : Level}
    {σᵉ : systemᵉ l1ᵉ} {τᵉ : systemᵉ l2ᵉ}
    (Wσᵉ : weakeningᵉ σᵉ) (Wτᵉ : weakeningᵉ τᵉ)
    (hᵉ : hom-systemᵉ σᵉ τᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( hom-system.sliceᵉ hᵉ)
            ( weakening.elementᵉ Wσᵉ))
          ( comp-hom-systemᵉ
            ( weakening.elementᵉ Wτᵉ)
            ( hᵉ))
      sliceᵉ :
        preserves-weakeningᵉ
          ( weakening.sliceᵉ Wσᵉ)
          ( weakening.sliceᵉ Wτᵉ)
          ( hom-system.sliceᵉ hᵉ)

  record substitutionᵉ
    {lᵉ : Level} (σᵉ : systemᵉ lᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        system.elementᵉ σᵉ → hom-systemᵉ (system.sliceᵉ σᵉ) σᵉ
      sliceᵉ : substitutionᵉ (system.sliceᵉ σᵉ)

  record preserves-substitutionᵉ
    {l1ᵉ l2ᵉ : Level}
    {σᵉ : systemᵉ l1ᵉ} {τᵉ : systemᵉ l2ᵉ}
    (Sσᵉ : substitutionᵉ σᵉ) (Sτᵉ : substitutionᵉ τᵉ)
    (hᵉ : hom-systemᵉ σᵉ τᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( hᵉ)
            ( substitution.elementᵉ Sσᵉ xᵉ))
          ( comp-hom-systemᵉ
            ( substitution.elementᵉ Sτᵉ
              ( hom-system.elementᵉ hᵉ xᵉ))
            ( hom-system.sliceᵉ hᵉ))
      sliceᵉ :
        preserves-substitutionᵉ
          ( substitution.sliceᵉ Sσᵉ)
          ( substitution.sliceᵉ Sτᵉ)
          ( hom-system.sliceᵉ hᵉ)

  record generic-elementᵉ
    {lᵉ : Level} (σᵉ : systemᵉ lᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ : system.elementᵉ (system.sliceᵉ σᵉ)
      sliceᵉ : generic-elementᵉ (system.sliceᵉ σᵉ)

  record preserves-generic-elementᵉ
    {l1ᵉ l2ᵉ : Level} {σᵉ : systemᵉ l1ᵉ} {τᵉ : systemᵉ l2ᵉ}
    (δσᵉ : generic-elementᵉ σᵉ) (δτᵉ : generic-elementᵉ τᵉ)
    (hᵉ : hom-systemᵉ σᵉ τᵉ) : UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    coinductiveᵉ
    field
      elementᵉ :
        Idᵉ
          ( hom-system.elementᵉ
            ( hom-system.sliceᵉ hᵉ)
            ( generic-element.elementᵉ δσᵉ))
          ( generic-element.elementᵉ δτᵉ)
      sliceᵉ :
        preserves-generic-elementᵉ
          ( generic-element.sliceᵉ δσᵉ)
          ( generic-element.sliceᵉ δτᵉ)
          ( hom-system.sliceᵉ hᵉ)

  record weakening-preserves-weakeningᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Wᵉ : weakeningᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        preserves-weakeningᵉ
          ( Wᵉ)
          ( weakening.sliceᵉ Wᵉ)
          ( weakening.elementᵉ Wᵉ)
      sliceᵉ :
        weakening-preserves-weakeningᵉ (weakening.sliceᵉ Wᵉ)

  record substitution-preserves-substitutionᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Sᵉ : substitutionᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        preserves-substitutionᵉ
          ( substitution.sliceᵉ Sᵉ)
          ( Sᵉ)
          ( substitution.elementᵉ Sᵉ xᵉ)
      sliceᵉ :
        substitution-preserves-substitutionᵉ (substitution.sliceᵉ Sᵉ)

  record weakening-preserves-substitutionᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ}
    (Wᵉ : weakeningᵉ σᵉ) (Sᵉ : substitutionᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        preserves-substitutionᵉ
          ( Sᵉ)
          ( substitution.sliceᵉ Sᵉ)
          ( weakening.elementᵉ Wᵉ)
      sliceᵉ :
        weakening-preserves-substitutionᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( substitution.sliceᵉ Sᵉ)

  record substitution-preserves-weakeningᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Wᵉ : weakeningᵉ σᵉ) (Sᵉ : substitutionᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        preserves-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( Wᵉ)
          ( substitution.elementᵉ Sᵉ xᵉ)
      sliceᵉ :
        substitution-preserves-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( substitution.sliceᵉ Sᵉ)

  record weakening-preserves-generic-elementᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Wᵉ : weakeningᵉ σᵉ) (δᵉ : generic-elementᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        preserves-generic-elementᵉ
          ( δᵉ)
          ( generic-element.sliceᵉ δᵉ)
          ( weakening.elementᵉ Wᵉ)
      sliceᵉ :
        weakening-preserves-generic-elementᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( generic-element.sliceᵉ δᵉ)

  record substitution-preserves-generic-elementᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Sᵉ : substitutionᵉ σᵉ) (δᵉ : generic-elementᵉ σᵉ) :
    UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        preserves-generic-elementᵉ
          ( generic-element.sliceᵉ δᵉ)
          ( δᵉ)
          ( substitution.elementᵉ Sᵉ xᵉ)
      sliceᵉ :
        substitution-preserves-generic-elementᵉ
          ( substitution.sliceᵉ Sᵉ)
          ( generic-element.sliceᵉ δᵉ)

  record substitution-cancels-weakeningᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Wᵉ : weakeningᵉ σᵉ) (Sᵉ : substitutionᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( substitution.elementᵉ Sᵉ xᵉ)
            ( weakening.elementᵉ Wᵉ))
          ( id-hom-systemᵉ σᵉ)
      sliceᵉ :
        substitution-cancels-weakeningᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( substitution.sliceᵉ Sᵉ)

  record generic-element-is-identityᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Sᵉ : substitutionᵉ σᵉ) (δᵉ : generic-elementᵉ σᵉ) :
    UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        (xᵉ : system.elementᵉ σᵉ) →
        Idᵉ ( hom-system.elementᵉ
              ( substitution.elementᵉ Sᵉ xᵉ)
              ( generic-element.elementᵉ δᵉ))
            ( xᵉ)
      sliceᵉ :
        generic-element-is-identityᵉ
          ( substitution.sliceᵉ Sᵉ)
          ( generic-element.sliceᵉ δᵉ)

  record substitution-by-generic-elementᵉ
    {lᵉ : Level} {σᵉ : systemᵉ lᵉ} (Wᵉ : weakeningᵉ σᵉ) (Sᵉ : substitutionᵉ σᵉ)
    (δᵉ : generic-elementᵉ σᵉ) : UUᵉ lᵉ
    where
    coinductiveᵉ
    field
      elementᵉ :
        htpy-hom-systemᵉ
          ( comp-hom-systemᵉ
            ( substitution.elementᵉ
              ( substitution.sliceᵉ Sᵉ)
              ( generic-element.elementᵉ δᵉ))
            ( weakening.elementᵉ (weakening.sliceᵉ Wᵉ)))
          ( id-hom-systemᵉ (system.sliceᵉ σᵉ))
      sliceᵉ :
        substitution-by-generic-elementᵉ
          ( weakening.sliceᵉ Wᵉ)
          ( substitution.sliceᵉ Sᵉ)
          ( generic-element.sliceᵉ δᵉ)

  record type-theoryᵉ
    (lᵉ : Level) : UUᵉ (lsuc lᵉ)
    where
    field
      sysᵉ : systemᵉ lᵉ
      Wᵉ : weakeningᵉ sysᵉ
      Sᵉ : substitutionᵉ sysᵉ
      δᵉ : generic-elementᵉ sysᵉ
      WWᵉ : weakening-preserves-weakeningᵉ Wᵉ
      SSᵉ : substitution-preserves-substitutionᵉ Sᵉ
      WSᵉ : weakening-preserves-substitutionᵉ Wᵉ Sᵉ
      SWᵉ : substitution-preserves-weakeningᵉ Wᵉ Sᵉ
      Wδᵉ : weakening-preserves-generic-elementᵉ Wᵉ δᵉ
      Sδᵉ : substitution-preserves-generic-elementᵉ Sᵉ δᵉ
      S!Wᵉ : substitution-cancels-weakeningᵉ Wᵉ Sᵉ
      δidᵉ : generic-element-is-identityᵉ Sᵉ δᵉ
      Sδ!ᵉ : substitution-by-generic-elementᵉ Wᵉ Sᵉ δᵉ

  slice-type-theoryᵉ :
    {lᵉ : Level} (Tᵉ : type-theoryᵉ lᵉ) → type-theoryᵉ lᵉ
  type-theory.sysᵉ (slice-type-theoryᵉ Tᵉ) =
    system.sliceᵉ (type-theory.sysᵉ Tᵉ)
  type-theory.Wᵉ (slice-type-theoryᵉ Tᵉ) =
    weakening.sliceᵉ (type-theory.Wᵉ Tᵉ)
  type-theory.Sᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution.sliceᵉ (type-theory.Sᵉ Tᵉ)
  type-theory.δᵉ (slice-type-theoryᵉ Tᵉ) =
    generic-element.sliceᵉ (type-theory.δᵉ Tᵉ)
  type-theory.WWᵉ (slice-type-theoryᵉ Tᵉ) =
    weakening-preserves-weakening.sliceᵉ (type-theory.WWᵉ Tᵉ)
  type-theory.SSᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution-preserves-substitution.sliceᵉ (type-theory.SSᵉ Tᵉ)
  type-theory.WSᵉ (slice-type-theoryᵉ Tᵉ) =
    weakening-preserves-substitution.sliceᵉ (type-theory.WSᵉ Tᵉ)
  type-theory.SWᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution-preserves-weakening.sliceᵉ (type-theory.SWᵉ Tᵉ)
  type-theory.Wδᵉ (slice-type-theoryᵉ Tᵉ) =
    weakening-preserves-generic-element.sliceᵉ (type-theory.Wδᵉ Tᵉ)
  type-theory.Sδᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution-preserves-generic-element.sliceᵉ (type-theory.Sδᵉ Tᵉ)
  type-theory.S!Wᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution-cancels-weakening.sliceᵉ (type-theory.S!Wᵉ Tᵉ)
  type-theory.δidᵉ (slice-type-theoryᵉ Tᵉ) =
    generic-element-is-identity.sliceᵉ (type-theory.δidᵉ Tᵉ)
  type-theory.Sδ!ᵉ (slice-type-theoryᵉ Tᵉ) =
    substitution-by-generic-element.sliceᵉ (type-theory.Sδ!ᵉ Tᵉ)
```

---ᵉ

```agda
  module C-systemᵉ where

    Elᵉ : {lᵉ : Level} (Aᵉ : type-theoryᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
    Elᵉ Aᵉ zero-ℕᵉ = system.elementᵉ (type-theory.sysᵉ Aᵉ)
    Elᵉ Aᵉ (succ-ℕᵉ nᵉ) = Elᵉ (slice-type-theoryᵉ Aᵉ) nᵉ

    iterated-weakeningᵉ :
      {lᵉ : Level} {Aᵉ : type-theoryᵉ lᵉ} {mᵉ nᵉ : ℕᵉ} →
      Elᵉ Aᵉ nᵉ → Elᵉ Aᵉ (succ-ℕᵉ (mᵉ +ℕᵉ nᵉ))
    iterated-weakeningᵉ {lᵉ} {Aᵉ} {zero-ℕᵉ} {nᵉ} xᵉ =
      {!hom-system.elementᵉ (weakening.elementᵉ (type-theory.Wᵉ Aᵉ)) !ᵉ}
    iterated-weakeningᵉ {lᵉ} {Aᵉ} {succ-ℕᵉ mᵉ} {nᵉ} xᵉ = {!!ᵉ}
```

`hom(X,Yᵉ) :=ᵉ Tm(W(X,Y))`ᵉ

```agda
    homᵉ : {lᵉ : Level} (Aᵉ : type-theoryᵉ lᵉ) → ℕᵉ → ℕᵉ → UUᵉ lᵉ
    homᵉ Aᵉ mᵉ nᵉ = Elᵉ Aᵉ (succ-ℕᵉ (mᵉ +ℕᵉ nᵉ))

    id-homᵉ : {lᵉ : Level} (Aᵉ : type-theoryᵉ lᵉ) (nᵉ : ℕᵉ) → homᵉ Aᵉ nᵉ nᵉ
    id-homᵉ Aᵉ zero-ℕᵉ = generic-element.elementᵉ (type-theory.δᵉ Aᵉ)
    id-homᵉ Aᵉ (succ-ℕᵉ nᵉ) = {!!ᵉ}
```

### The forgetful functor from unityped type theories to simple type theories

```agda
module simple-unitypedᵉ where

{-ᵉ
  systemᵉ :
    {lᵉ : Level} → unityped.systemᵉ lᵉ → simple.systemᵉ lᵉ unitᵉ
  simple.system.elementᵉ (systemᵉ Aᵉ) xᵉ = unityped.system.elementᵉ Aᵉ
  simple.system.sliceᵉ (systemᵉ Aᵉ) xᵉ = systemᵉ (unityped.system.sliceᵉ Aᵉ)

  hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : unityped.systemᵉ l1ᵉ} {Bᵉ : unityped.systemᵉ l2ᵉ} →
    unityped.hom-systemᵉ Aᵉ Bᵉ →
    simple.hom-systemᵉ idᵉ
      ( systemᵉ Aᵉ)
      ( systemᵉ Bᵉ)
  simple.hom-system.elementᵉ (hom-systemᵉ fᵉ) = unityped.hom-system.elementᵉ fᵉ
  simple.hom-system.sliceᵉ (hom-systemᵉ fᵉ) xᵉ =
    hom-systemᵉ (unityped.hom-system.sliceᵉ fᵉ)

  id-hom-systemᵉ :
    {lᵉ : Level} (Aᵉ : unityped.systemᵉ lᵉ) →
    simple.htpy-hom-systemᵉ
      ( hom-systemᵉ (unityped.id-hom-systemᵉ Aᵉ))
      ( simple.id-hom-systemᵉ (systemᵉ Aᵉ))
  simple.htpy-hom-system.elementᵉ (id-hom-systemᵉ Aᵉ) xᵉ = refl-htpyᵉ
  simple.htpy-hom-system.sliceᵉ (id-hom-systemᵉ Aᵉ) xᵉ =
    id-hom-systemᵉ (unityped.system.sliceᵉ Aᵉ)

  comp-hom-systemᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : unityped.systemᵉ l1ᵉ} {Bᵉ : unityped.systemᵉ l2ᵉ}
    {Cᵉ : unityped.systemᵉ l3ᵉ} (gᵉ : unityped.hom-systemᵉ Bᵉ Cᵉ)
    (fᵉ : unityped.hom-systemᵉ Aᵉ Bᵉ) →
    simple.htpy-hom-systemᵉ
      ( hom-systemᵉ (unityped.comp-hom-systemᵉ gᵉ fᵉ))
      ( simple.comp-hom-systemᵉ
        ( hom-systemᵉ gᵉ)
        ( hom-systemᵉ fᵉ))
  simple.htpy-hom-system.elementᵉ (comp-hom-systemᵉ gᵉ fᵉ) xᵉ = refl-htpyᵉ
  simple.htpy-hom-system.sliceᵉ (comp-hom-systemᵉ gᵉ fᵉ) xᵉ =
    comp-hom-systemᵉ
      ( unityped.hom-system.sliceᵉ gᵉ)
      ( unityped.hom-system.sliceᵉ fᵉ)

  htpy-hom-systemᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : unityped.systemᵉ l1ᵉ} {Bᵉ : unityped.systemᵉ l2ᵉ}
    {fᵉ gᵉ : unityped.hom-systemᵉ Aᵉ Bᵉ} →
    unityped.htpy-hom-systemᵉ fᵉ gᵉ →
    simple.htpy-hom-systemᵉ (hom-systemᵉ fᵉ) (hom-systemᵉ gᵉ)
  simple.htpy-hom-system.elementᵉ (htpy-hom-systemᵉ Hᵉ) xᵉ =
    unityped.htpy-hom-system.elementᵉ Hᵉ
  simple.htpy-hom-system.sliceᵉ (htpy-hom-systemᵉ Hᵉ) xᵉ =
    htpy-hom-systemᵉ (unityped.htpy-hom-system.sliceᵉ Hᵉ)

  weakeningᵉ :
    {lᵉ : Level} {Aᵉ : unityped.systemᵉ lᵉ} → unityped.weakeningᵉ Aᵉ →
    simple.weakeningᵉ (systemᵉ Aᵉ)
  simple.weakening.elementᵉ (weakeningᵉ Wᵉ) xᵉ =
    hom-systemᵉ (unityped.weakening.elementᵉ Wᵉ)
  simple.weakening.sliceᵉ (weakeningᵉ Wᵉ) xᵉ =
    weakeningᵉ (unityped.weakening.sliceᵉ Wᵉ)

  preserves-weakeningᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : unityped.systemᵉ l1ᵉ} {Bᵉ : unityped.systemᵉ l2ᵉ}
    {WAᵉ : unityped.weakeningᵉ Aᵉ} {WBᵉ : unityped.weakeningᵉ Bᵉ}
    {fᵉ : unityped.hom-systemᵉ Aᵉ Bᵉ} →
    unityped.preserves-weakeningᵉ WAᵉ WBᵉ fᵉ →
    simple.preserves-weakeningᵉ (weakeningᵉ WAᵉ) (weakeningᵉ WBᵉ) (hom-systemᵉ fᵉ)
  simple.preserves-weakening.elementᵉ (preserves-weakeningᵉ Wfᵉ) xᵉ =
    {!simple.concat-htpy-hom-system!ᵉ}
  simple.preserves-weakening.sliceᵉ (preserves-weakeningᵉ Wfᵉ) = {!!ᵉ}

  substitutionᵉ :
    {lᵉ : Level} {Aᵉ : unityped.systemᵉ lᵉ} → unityped.substitutionᵉ Aᵉ →
    simple.substitutionᵉ (systemᵉ Aᵉ)
  simple.substitution.elementᵉ (substitutionᵉ Sᵉ) xᵉ =
    hom-systemᵉ (unityped.substitution.elementᵉ Sᵉ xᵉ)
  simple.substitution.sliceᵉ (substitutionᵉ Sᵉ) xᵉ =
    substitutionᵉ (unityped.substitution.sliceᵉ Sᵉ)

  generic-elementᵉ :
    {lᵉ : Level} {Aᵉ : unityped.systemᵉ lᵉ} → unityped.generic-elementᵉ Aᵉ →
    simple.generic-elementᵉ (systemᵉ Aᵉ)
  simple.generic-element.elementᵉ (generic-elementᵉ δᵉ) xᵉ =
    unityped.generic-element.elementᵉ δᵉ
  simple.generic-element.sliceᵉ (generic-elementᵉ δᵉ) xᵉ =
    generic-elementᵉ (unityped.generic-element.sliceᵉ δᵉ)
-ᵉ}
```