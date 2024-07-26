# Regular cd-structures

```agda
module orthogonal-factorization-systems.regular-cd-structuresᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Aᵉ {{#conceptᵉ "regularᵉ cd-structure"ᵉ}} isᵉ aᵉ
[cd-structure](orthogonal-factorization-systems.cd-structures.mdᵉ) whichᵉ
satisfiesᵉ theᵉ followingᵉ threeᵉ axiomsᵉ:

1.ᵉ Everyᵉ distinguishedᵉ squareᵉ isᵉ [cartesian](foundation.pullbacks.md).ᵉ
2.ᵉ Theᵉ codomainᵉ ofᵉ everyᵉ distinguishedᵉ squareᵉ isᵉ anᵉ
   [embedding](foundation.embeddings.md).ᵉ
3.ᵉ Theᵉ [diagonal](foundation.diagonals-of-morphisms-arrows.mdᵉ) ofᵉ everyᵉ
   distinguishedᵉ squareᵉ
   ```text
         Δᵉ iᵉ
      Aᵉ ----->ᵉ Aᵉ ×_Xᵉ Aᵉ
      |           |
    fᵉ |           | functorialityᵉ Δᵉ gᵉ
      ∨ᵉ           ∨ᵉ
      Bᵉ ----->ᵉ Bᵉ ×_Yᵉ B.ᵉ
         Δᵉ jᵉ
   ```
   isᵉ againᵉ aᵉ distinguishedᵉ square.ᵉ