# Commuting triangles of morphisms in set-magmoids

<pre class="Agda"><a id="61" class="Keyword">module</a> <a id="68" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.commuting-triangles-of-morphisms-in-set-magmoidsᵉ</a> <a id="134" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="category-theory.set-magmoids%25E1%25B5%2589.html" class="Module">category-theory.set-magmoidsᵉ</a>

<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A triangle of morphisms

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

in a [set-magmoid](category-theory.set-magmoids.md) `C` is said to **commute**
if there is an [identification](foundation-core.identity-types.md) between:

```text
  left ＝ right ∘ top.
```

Such a identification is called the
{{#concept "coherence" Disambiguation="commuting triangle of morphisms in set-magmaoids" Agda=coherence-triangle-hom-Set-Magmoid}}
of the commuting triangle.

## Definitions

<pre class="Agda"><a id="coherence-triangle-hom-Set-Magmoidᵉ"></a><a id="869" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#869" class="Function">coherence-triangle-hom-Set-Magmoidᵉ</a> <a id="905" class="Symbol">:</a>
  <a id="909" class="Symbol">{</a><a id="910" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#910" class="Bound">l1ᵉ</a> <a id="914" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#914" class="Bound">l2ᵉ</a> <a id="918" class="Symbol">:</a> <a id="920" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="925" class="Symbol">}</a> <a id="927" class="Symbol">(</a><a id="928" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="931" class="Symbol">:</a> <a id="933" href="category-theory.set-magmoids%25E1%25B5%2589.html#1566" class="Function">Set-Magmoidᵉ</a> <a id="946" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#910" class="Bound">l1ᵉ</a> <a id="950" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#914" class="Bound">l2ᵉ</a><a id="953" class="Symbol">)</a>
  <a id="957" class="Symbol">{</a><a id="958" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#958" class="Bound">xᵉ</a> <a id="961" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#961" class="Bound">yᵉ</a> <a id="964" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#964" class="Bound">zᵉ</a> <a id="967" class="Symbol">:</a> <a id="969" href="category-theory.set-magmoids%25E1%25B5%2589.html#1834" class="Function">obj-Set-Magmoidᵉ</a> <a id="986" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a><a id="988" class="Symbol">}</a>
  <a id="992" class="Symbol">(</a><a id="993" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#993" class="Bound">topᵉ</a> <a id="998" class="Symbol">:</a> <a id="1000" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="1017" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1020" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#958" class="Bound">xᵉ</a> <a id="1023" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#961" class="Bound">yᵉ</a><a id="1025" class="Symbol">)</a>
  <a id="1029" class="Symbol">(</a><a id="1030" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1030" class="Bound">leftᵉ</a> <a id="1036" class="Symbol">:</a> <a id="1038" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="1055" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1058" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#958" class="Bound">xᵉ</a> <a id="1061" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#964" class="Bound">zᵉ</a><a id="1063" class="Symbol">)</a>
  <a id="1067" class="Symbol">(</a><a id="1068" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1068" class="Bound">rightᵉ</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="category-theory.set-magmoids%25E1%25B5%2589.html#1997" class="Function">hom-Set-Magmoidᵉ</a> <a id="1094" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#928" class="Bound">Cᵉ</a> <a id="1097" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#961" class="Bound">yᵉ</a> <a id="1100" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#964" class="Bound">zᵉ</a><a id="1102" class="Symbol">)</a> <a id="1104" class="Symbol">→</a>
  <a id="1108" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1112" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#914" class="Bound">l2ᵉ</a>
<a id="1116" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#869" class="Function">coherence-triangle-hom-Set-Magmoidᵉ</a> <a id="1152" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1152" class="Bound">Cᵉ</a> <a id="1155" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1155" class="Bound">topᵉ</a> <a id="1160" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1160" class="Bound">leftᵉ</a> <a id="1166" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1166" class="Bound">rightᵉ</a> <a id="1173" class="Symbol">=</a>
  <a id="1177" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1160" class="Bound">leftᵉ</a> <a id="1183" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1186" href="category-theory.set-magmoids%25E1%25B5%2589.html#2301" class="Function">comp-hom-Set-Magmoidᵉ</a> <a id="1208" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1152" class="Bound">Cᵉ</a> <a id="1211" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1166" class="Bound">rightᵉ</a> <a id="1218" href="category-theory.commuting-triangles-of-morphisms-in-set-magmoids%25E1%25B5%2589.html#1155" class="Bound">topᵉ</a>
</pre>