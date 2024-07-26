# The preunivalence axiom

```agda
module foundation.preunivalenceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.setsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.subtypesᵉ
```

</details>

## Idea

**Theᵉ preunivalenceᵉ axiom**,ᵉ orᵉ **axiomᵉ L**,ᵉ whichᵉ isᵉ dueᵉ to Peterᵉ Lumsdaine,ᵉ
assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ typesᵉ `X`ᵉ andᵉ `Y`ᵉ in aᵉ commonᵉ universe,ᵉ theᵉ mapᵉ
`Xᵉ ＝ᵉ Yᵉ → Xᵉ ≃ᵉ Y`ᵉ isᵉ anᵉ [embedding](foundation-core.embeddings.md).ᵉ Thisᵉ axiomᵉ isᵉ
aᵉ commonᵉ generalizationᵉ ofᵉ theᵉ [univalenceᵉ axiom](foundation.univalence.mdᵉ) andᵉ
[axiomᵉ K](foundation-core.sets.md).ᵉ

## Definition

```agda
instance-preunivalenceᵉ : {lᵉ : Level} (Xᵉ Yᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lᵉ)
instance-preunivalenceᵉ Xᵉ Yᵉ = is-embᵉ (equiv-eqᵉ {Aᵉ = Xᵉ} {Bᵉ = Yᵉ})

based-preunivalence-axiomᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → UUᵉ (lsuc lᵉ)
based-preunivalence-axiomᵉ {lᵉ} Xᵉ = (Yᵉ : UUᵉ lᵉ) → instance-preunivalenceᵉ Xᵉ Yᵉ

preunivalence-axiom-Levelᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
preunivalence-axiom-Levelᵉ lᵉ = (Xᵉ Yᵉ : UUᵉ lᵉ) → instance-preunivalenceᵉ Xᵉ Yᵉ

preunivalence-axiomᵉ : UUωᵉ
preunivalence-axiomᵉ = {lᵉ : Level} → preunivalence-axiom-Levelᵉ lᵉ

emb-preunivalenceᵉ :
  preunivalence-axiomᵉ → {lᵉ : Level} (Xᵉ Yᵉ : UUᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) ↪ᵉ (Xᵉ ≃ᵉ Yᵉ)
pr1ᵉ (emb-preunivalenceᵉ Lᵉ Xᵉ Yᵉ) = equiv-eqᵉ
pr2ᵉ (emb-preunivalenceᵉ Lᵉ Xᵉ Yᵉ) = Lᵉ Xᵉ Yᵉ

emb-map-preunivalenceᵉ :
  preunivalence-axiomᵉ → {lᵉ : Level} (Xᵉ Yᵉ : UUᵉ lᵉ) → (Xᵉ ＝ᵉ Yᵉ) ↪ᵉ (Xᵉ → Yᵉ)
emb-map-preunivalenceᵉ Lᵉ Xᵉ Yᵉ =
  comp-embᵉ (emb-subtypeᵉ is-equiv-Propᵉ) (emb-preunivalenceᵉ Lᵉ Xᵉ Yᵉ)
```

## Properties

### Preunivalence generalizes axiom K

Toᵉ showᵉ thatᵉ preunivalenceᵉ generalizesᵉ axiomᵉ K,ᵉ weᵉ assumeᵉ axiomᵉ Kᵉ forᵉ theᵉ typesᵉ
in questionᵉ andᵉ forᵉ theᵉ universeᵉ itself.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ Bᵉ : UUᵉ lᵉ)
  where

  instance-preunivalence-instance-axiom-Kᵉ :
    instance-axiom-Kᵉ (UUᵉ lᵉ) → instance-axiom-Kᵉ Aᵉ → instance-axiom-Kᵉ Bᵉ →
    instance-preunivalenceᵉ Aᵉ Bᵉ
  instance-preunivalence-instance-axiom-Kᵉ K-Typeᵉ K-Aᵉ K-Bᵉ =
    is-emb-is-prop-is-setᵉ
      ( is-set-axiom-Kᵉ K-Typeᵉ Aᵉ Bᵉ)
      ( is-set-equiv-is-setᵉ (is-set-axiom-Kᵉ K-Aᵉ) (is-set-axiom-Kᵉ K-Bᵉ))

preunivalence-axiom-axiom-Kᵉ : axiom-Kᵉ → preunivalence-axiomᵉ
preunivalence-axiom-axiom-Kᵉ Kᵉ {lᵉ} Xᵉ Yᵉ =
  instance-preunivalence-instance-axiom-Kᵉ Xᵉ Yᵉ (Kᵉ (UUᵉ lᵉ)) (Kᵉ Xᵉ) (Kᵉ Yᵉ)
```

### Preunivalence generalizes univalence

```agda
module _
  {lᵉ : Level} (Aᵉ Bᵉ : UUᵉ lᵉ)
  where

  instance-preunivalence-instance-univalenceᵉ :
    instance-univalenceᵉ Aᵉ Bᵉ → instance-preunivalenceᵉ Aᵉ Bᵉ
  instance-preunivalence-instance-univalenceᵉ = is-emb-is-equivᵉ

preunivalence-axiom-univalence-axiomᵉ : univalence-axiomᵉ → preunivalence-axiomᵉ
preunivalence-axiom-univalence-axiomᵉ UAᵉ Xᵉ Yᵉ =
  instance-preunivalence-instance-univalenceᵉ Xᵉ Yᵉ (UAᵉ Xᵉ Yᵉ)
```

### Preunivalence holds in univalent foundations

```agda
preunivalenceᵉ : preunivalence-axiomᵉ
preunivalenceᵉ = preunivalence-axiom-univalence-axiomᵉ univalenceᵉ
```

## See also

-ᵉ Preunivalenceᵉ isᵉ sufficientᵉ to proveᵉ thatᵉ `Idᵉ : Aᵉ → (Aᵉ → 𝒰)`ᵉ isᵉ anᵉ embedding.ᵉ
  Thisᵉ factᵉ isᵉ provenᵉ in
  [`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.mdᵉ)
-ᵉ [Preunivalentᵉ typeᵉ families](foundation.preunivalent-type-families.mdᵉ)
-ᵉ [Preunivalentᵉ categories](category-theory.preunivalent-categories.mdᵉ)