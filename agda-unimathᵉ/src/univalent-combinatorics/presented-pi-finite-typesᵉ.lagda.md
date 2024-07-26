# Finitely π-presented types

```agda
module univalent-combinatorics.presented-pi-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ finitelyᵉ `π_0`-presentedᵉ ifᵉ thereᵉ isᵉ aᵉ standardᵉ prunedᵉ
treeᵉ `T`ᵉ ofᵉ heightᵉ 1 soᵉ thatᵉ `A`ᵉ hasᵉ aᵉ presentationᵉ ofᵉ cardinalityᵉ `widthᵉ T`,ᵉ
andᵉ `A`ᵉ isᵉ saidᵉ to beᵉ finitelyᵉ `π_{n+1}`-presentedᵉ ifᵉ thereᵉ isᵉ aᵉ standardᵉ prunedᵉ
treeᵉ `T`ᵉ ofᵉ heightᵉ `n+2`ᵉ andᵉ aᵉ mapᵉ `fᵉ : Finᵉ (widthᵉ Tᵉ) → A`ᵉ soᵉ thatᵉ
`ηᵉ ∘ᵉ fᵉ : Finᵉ (widthᵉ Tᵉ) → ∥A∥_0`ᵉ isᵉ anᵉ equivalence,ᵉ andᵉ forᵉ eachᵉ
`xᵉ : Finᵉ (widthᵉ T)`ᵉ theᵉ typeᵉ `Ωᵉ (A,ᵉ fᵉ x)`ᵉ isᵉ