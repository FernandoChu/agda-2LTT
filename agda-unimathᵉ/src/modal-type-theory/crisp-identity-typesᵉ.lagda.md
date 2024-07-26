# Crisp identity types

```agda
{-# OPTIONSᵉ --cohesionᵉ --flat-splitᵉ #-}

module modal-type-theory.crisp-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Weᵉ record hereᵉ someᵉ basicᵉ factsᵉ aboutᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) in crispᵉ contexts.ᵉ

## Properties

```agda
ind-path-crispᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {@♭ᵉ aᵉ : Aᵉ} →
  (Cᵉ : (@♭ᵉ yᵉ : Aᵉ) (pᵉ : aᵉ ＝ᵉ yᵉ) → UUᵉ l2ᵉ) →
  Cᵉ aᵉ reflᵉ →
  (@♭ᵉ yᵉ : Aᵉ) (@♭ᵉ pᵉ : aᵉ ＝ᵉ yᵉ) → Cᵉ yᵉ pᵉ
ind-path-crispᵉ Cᵉ bᵉ _ reflᵉ = bᵉ

ap-crispᵉ :
  {@♭ᵉ l1ᵉ : Level} {l2ᵉ : Level} {@♭ᵉ Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {@♭ᵉ xᵉ yᵉ : Aᵉ}
  (fᵉ : (@♭ᵉ xᵉ : Aᵉ) → Bᵉ) → @♭ᵉ (xᵉ ＝ᵉ yᵉ) → (fᵉ xᵉ) ＝ᵉ (fᵉ yᵉ)
ap-crispᵉ fᵉ reflᵉ = reflᵉ
```