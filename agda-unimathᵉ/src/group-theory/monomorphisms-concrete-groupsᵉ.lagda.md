# Monomorphisms of concrete groups

```agda
module group-theory.monomorphisms-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.homomorphisms-concrete-groupsᵉ
```

</details>

## Idea

Aᵉ monomorphismᵉ ofᵉ concreteᵉ groupsᵉ fromᵉ `G`ᵉ to `H`ᵉ isᵉ aᵉ faithfulᵉ pointedᵉ mapᵉ BHᵉ
→∗ᵉ BG.ᵉ Recallᵉ thatᵉ aᵉ mapᵉ isᵉ saidᵉ to beᵉ faithfulᵉ ifᵉ itᵉ inducesᵉ embeddingsᵉ onᵉ
identityᵉ types.ᵉ Inᵉ particular,ᵉ anyᵉ faithfulᵉ pointedᵉ mapᵉ BHᵉ →∗ᵉ BGᵉ inducesᵉ anᵉ
embeddingᵉ ΩBHᵉ → ΩBG,ᵉ i.e.,ᵉ anᵉ inclusionᵉ ofᵉ theᵉ underlyingᵉ groupsᵉ ofᵉ aᵉ concreteᵉ
group.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Hᵉ : Concrete-Groupᵉ l2ᵉ)
  (fᵉ : hom-Concrete-Groupᵉ Gᵉ Hᵉ)
  where

  is-mono-prop-hom-Concrete-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-mono-prop-hom-Concrete-Groupᵉ =
    Π-Propᵉ
      ( Concrete-Groupᵉ l3ᵉ)
      ( λ Fᵉ → is-emb-Propᵉ (comp-hom-Concrete-Groupᵉ Fᵉ Gᵉ Hᵉ fᵉ))

  is-mono-hom-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-mono-hom-Concrete-Groupᵉ = type-Propᵉ is-mono-prop-hom-Concrete-Groupᵉ

  is-prop-is-mono-hom-Concrete-Groupᵉ : is-propᵉ is-mono-hom-Concrete-Groupᵉ
  is-prop-is-mono-hom-Concrete-Groupᵉ =
    is-prop-type-Propᵉ is-mono-prop-hom-Concrete-Groupᵉ

module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  where

  mono-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  mono-Concrete-Groupᵉ =
    Σᵉ ( Concrete-Groupᵉ l2ᵉ)
      ( λ Hᵉ →
        Σᵉ (hom-Concrete-Groupᵉ Hᵉ Gᵉ) λ fᵉ → is-mono-hom-Concrete-Groupᵉ l2ᵉ Hᵉ Gᵉ fᵉ)
```