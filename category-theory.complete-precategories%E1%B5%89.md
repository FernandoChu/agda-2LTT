# Complete precategories

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="category-theory.complete-precategories%25E1%25B5%2589.html" class="Module">category-theory.complete-precategoriesᵉ</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="category-theory.cones-precategories%25E1%25B5%2589.html" class="Module">category-theory.cones-precategoriesᵉ</a>
<a id="187" class="Keyword">open</a> <a id="192" class="Keyword">import</a> <a id="199" href="category-theory.functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.functors-precategoriesᵉ</a>
<a id="239" class="Keyword">open</a> <a id="244" class="Keyword">import</a> <a id="251" href="category-theory.limits-precategories%25E1%25B5%2589.html" class="Module">category-theory.limits-precategoriesᵉ</a>
<a id="289" class="Keyword">open</a> <a id="294" class="Keyword">import</a> <a id="301" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="category-theory.terminal-objects-precategories%25E1%25B5%2589.html" class="Module">category-theory.terminal-objects-precategoriesᵉ</a>

<a id="393" class="Keyword">open</a> <a id="398" class="Keyword">import</a> <a id="405" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A {{#concept "complete precategory" Agda=is-complete-Precategory}} is a
[precategory](category-theory.precategories.md) that has all
[limits](category-theory.limits-precategories.md) for diagrams from a specified
universe.

More precisely, we say that a precategory `D` is `(l1 , l2)`-complete if for any
`C : Precategory l1 l2` and any
[functor](category-theory.functors-precategories.md) `F : C → D` the type of
limits of `F` is inhabited.

## Definition

<pre class="Agda"><a id="is-complete-Precategoryᵉ"></a><a id="925" href="category-theory.complete-precategories%25E1%25B5%2589.html#925" class="Function">is-complete-Precategoryᵉ</a> <a id="950" class="Symbol">:</a>
  <a id="954" class="Symbol">(</a><a id="955" href="category-theory.complete-precategories%25E1%25B5%2589.html#955" class="Bound">l1ᵉ</a> <a id="959" href="category-theory.complete-precategories%25E1%25B5%2589.html#959" class="Bound">l2ᵉ</a> <a id="963" class="Symbol">:</a> <a id="965" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="970" class="Symbol">)</a> <a id="972" class="Symbol">{</a><a id="973" href="category-theory.complete-precategories%25E1%25B5%2589.html#973" class="Bound">l3ᵉ</a> <a id="977" href="category-theory.complete-precategories%25E1%25B5%2589.html#977" class="Bound">l4ᵉ</a> <a id="981" class="Symbol">:</a> <a id="983" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="988" class="Symbol">}</a>
  <a id="992" class="Symbol">(</a><a id="993" href="category-theory.complete-precategories%25E1%25B5%2589.html#993" class="Bound">Dᵉ</a> <a id="996" class="Symbol">:</a> <a id="998" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1011" href="category-theory.complete-precategories%25E1%25B5%2589.html#973" class="Bound">l3ᵉ</a> <a id="1015" href="category-theory.complete-precategories%25E1%25B5%2589.html#977" class="Bound">l4ᵉ</a><a id="1018" class="Symbol">)</a> <a id="1020" class="Symbol">→</a>
  <a id="1024" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1028" class="Symbol">(</a><a id="1029" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1034" href="category-theory.complete-precategories%25E1%25B5%2589.html#955" class="Bound">l1ᵉ</a> <a id="1038" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1040" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1045" href="category-theory.complete-precategories%25E1%25B5%2589.html#959" class="Bound">l2ᵉ</a> <a id="1049" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1051" href="category-theory.complete-precategories%25E1%25B5%2589.html#973" class="Bound">l3ᵉ</a> <a id="1055" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1057" href="category-theory.complete-precategories%25E1%25B5%2589.html#977" class="Bound">l4ᵉ</a><a id="1060" class="Symbol">)</a>
<a id="1062" href="category-theory.complete-precategories%25E1%25B5%2589.html#925" class="Function">is-complete-Precategoryᵉ</a> <a id="1087" href="category-theory.complete-precategories%25E1%25B5%2589.html#1087" class="Bound">l1ᵉ</a> <a id="1091" href="category-theory.complete-precategories%25E1%25B5%2589.html#1091" class="Bound">l2ᵉ</a> <a id="1095" href="category-theory.complete-precategories%25E1%25B5%2589.html#1095" class="Bound">Dᵉ</a> <a id="1098" class="Symbol">=</a>
  <a id="1102" class="Symbol">(</a><a id="1103" href="category-theory.complete-precategories%25E1%25B5%2589.html#1103" class="Bound">Cᵉ</a> <a id="1106" class="Symbol">:</a> <a id="1108" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1121" href="category-theory.complete-precategories%25E1%25B5%2589.html#1087" class="Bound">l1ᵉ</a> <a id="1125" href="category-theory.complete-precategories%25E1%25B5%2589.html#1091" class="Bound">l2ᵉ</a><a id="1128" class="Symbol">)</a> <a id="1130" class="Symbol">(</a><a id="1131" href="category-theory.complete-precategories%25E1%25B5%2589.html#1131" class="Bound">Fᵉ</a> <a id="1134" class="Symbol">:</a> <a id="1136" href="category-theory.functors-precategories%25E1%25B5%2589.html#3980" class="Function">functor-Precategoryᵉ</a> <a id="1157" href="category-theory.complete-precategories%25E1%25B5%2589.html#1103" class="Bound">Cᵉ</a> <a id="1160" href="category-theory.complete-precategories%25E1%25B5%2589.html#1095" class="Bound">Dᵉ</a><a id="1162" class="Symbol">)</a> <a id="1164" class="Symbol">→</a>
  <a id="1168" href="category-theory.limits-precategories%25E1%25B5%2589.html#2367" class="Function">limit-Precategoryᵉ</a> <a id="1187" href="category-theory.complete-precategories%25E1%25B5%2589.html#1103" class="Bound">Cᵉ</a> <a id="1190" href="category-theory.complete-precategories%25E1%25B5%2589.html#1095" class="Bound">Dᵉ</a> <a id="1193" href="category-theory.complete-precategories%25E1%25B5%2589.html#1131" class="Bound">Fᵉ</a>
</pre>