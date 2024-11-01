# Rigid objects in a category

<pre class="Agda"><a id="40" class="Keyword">module</a> <a id="47" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html" class="Module">category-theory.rigid-objects-categoriesᵉ</a> <a id="89" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="145" class="Keyword">open</a> <a id="150" class="Keyword">import</a> <a id="157" href="category-theory.categories%25E1%25B5%2589.html" class="Module">category-theory.categoriesᵉ</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="category-theory.rigid-objects-precategories%25E1%25B5%2589.html" class="Module">category-theory.rigid-objects-precategoriesᵉ</a>

<a id="243" class="Keyword">open</a> <a id="248" class="Keyword">import</a> <a id="255" href="foundation.propositions%25E1%25B5%2589.html" class="Module">foundation.propositionsᵉ</a>
<a id="280" class="Keyword">open</a> <a id="285" class="Keyword">import</a> <a id="292" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A **rigid object** in a [category](category-theory.categories.md) is an object
whose [automorphism group](group-theory.automorphism-groups.md) is
[trivial](group-theory.trivial-groups.md).

## Definitions

### The predicate of being rigid

<pre class="Agda"><a id="594" class="Keyword">module</a> <a id="601" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#601" class="Module">_</a>
  <a id="605" class="Symbol">{</a><a id="606" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#606" class="Bound">l1ᵉ</a> <a id="610" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#610" class="Bound">l2ᵉ</a> <a id="614" class="Symbol">:</a> <a id="616" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="621" class="Symbol">}</a> <a id="623" class="Symbol">(</a><a id="624" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#624" class="Bound">Cᵉ</a> <a id="627" class="Symbol">:</a> <a id="629" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="639" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#606" class="Bound">l1ᵉ</a> <a id="643" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#610" class="Bound">l2ᵉ</a><a id="646" class="Symbol">)</a> <a id="648" class="Symbol">(</a><a id="649" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#649" class="Bound">xᵉ</a> <a id="652" class="Symbol">:</a> <a id="654" href="category-theory.categories%25E1%25B5%2589.html#2501" class="Function">obj-Categoryᵉ</a> <a id="668" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#624" class="Bound">Cᵉ</a><a id="670" class="Symbol">)</a>
  <a id="674" class="Keyword">where</a>

  <a id="683" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#683" class="Function">is-rigid-obj-prop-Categoryᵉ</a> <a id="711" class="Symbol">:</a> <a id="713" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="719" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#610" class="Bound">l2ᵉ</a>
  <a id="725" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#683" class="Function">is-rigid-obj-prop-Categoryᵉ</a> <a id="753" class="Symbol">=</a>
    <a id="759" href="category-theory.rigid-objects-precategories%25E1%25B5%2589.html#794" class="Function">is-rigid-obj-prop-Precategoryᵉ</a> <a id="790" class="Symbol">(</a><a id="791" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="813" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#624" class="Bound">Cᵉ</a><a id="815" class="Symbol">)</a> <a id="817" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#649" class="Bound">xᵉ</a>

  <a id="823" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#823" class="Function">is-rigid-obj-Categoryᵉ</a> <a id="846" class="Symbol">:</a> <a id="848" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="852" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#610" class="Bound">l2ᵉ</a>
  <a id="858" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#823" class="Function">is-rigid-obj-Categoryᵉ</a> <a id="881" class="Symbol">=</a> <a id="883" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="894" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#683" class="Function">is-rigid-obj-prop-Categoryᵉ</a>

  <a id="925" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#925" class="Function">is-prop-is-rigid-obj-Categoryᵉ</a> <a id="956" class="Symbol">:</a> <a id="958" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="967" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#823" class="Function">is-rigid-obj-Categoryᵉ</a>
  <a id="992" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#925" class="Function">is-prop-is-rigid-obj-Categoryᵉ</a> <a id="1023" class="Symbol">=</a>
    <a id="1029" href="foundation-core.propositions%25E1%25B5%2589.html#1361" class="Function">is-prop-type-Propᵉ</a> <a id="1048" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#683" class="Function">is-rigid-obj-prop-Categoryᵉ</a>
</pre>
### The type of rigid objects in a category

<pre class="Agda"><a id="rigid-obj-Categoryᵉ"></a><a id="1134" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1134" class="Function">rigid-obj-Categoryᵉ</a> <a id="1154" class="Symbol">:</a> <a id="1156" class="Symbol">{</a><a id="1157" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1157" class="Bound">l1ᵉ</a> <a id="1161" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1161" class="Bound">l2ᵉ</a> <a id="1165" class="Symbol">:</a> <a id="1167" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1172" class="Symbol">}</a> <a id="1174" class="Symbol">(</a><a id="1175" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1175" class="Bound">Cᵉ</a> <a id="1178" class="Symbol">:</a> <a id="1180" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="1190" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1157" class="Bound">l1ᵉ</a> <a id="1194" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1161" class="Bound">l2ᵉ</a><a id="1197" class="Symbol">)</a> <a id="1199" class="Symbol">→</a> <a id="1201" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1205" class="Symbol">(</a><a id="1206" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1157" class="Bound">l1ᵉ</a> <a id="1210" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1212" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1161" class="Bound">l2ᵉ</a><a id="1215" class="Symbol">)</a>
<a id="1217" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1134" class="Function">rigid-obj-Categoryᵉ</a> <a id="1237" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1237" class="Bound">Cᵉ</a> <a id="1240" class="Symbol">=</a>
    <a id="1246" href="category-theory.rigid-objects-precategories%25E1%25B5%2589.html#1253" class="Function">rigid-obj-Precategoryᵉ</a> <a id="1269" class="Symbol">(</a><a id="1270" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1292" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1237" class="Bound">Cᵉ</a><a id="1294" class="Symbol">)</a>

<a id="1297" class="Keyword">module</a> <a id="1304" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1304" class="Module">_</a>
  <a id="1308" class="Symbol">{</a><a id="1309" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1309" class="Bound">l1ᵉ</a> <a id="1313" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1313" class="Bound">l2ᵉ</a> <a id="1317" class="Symbol">:</a> <a id="1319" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1324" class="Symbol">}</a> <a id="1326" class="Symbol">(</a><a id="1327" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a> <a id="1330" class="Symbol">:</a> <a id="1332" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="1342" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1309" class="Bound">l1ᵉ</a> <a id="1346" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1313" class="Bound">l2ᵉ</a><a id="1349" class="Symbol">)</a>
  <a id="1353" class="Keyword">where</a>

  <a id="1362" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1362" class="Function">obj-rigid-obj-Categoryᵉ</a> <a id="1386" class="Symbol">:</a> <a id="1388" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1134" class="Function">rigid-obj-Categoryᵉ</a> <a id="1408" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a> <a id="1411" class="Symbol">→</a> <a id="1413" href="category-theory.categories%25E1%25B5%2589.html#2501" class="Function">obj-Categoryᵉ</a> <a id="1427" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a>
  <a id="1432" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1362" class="Function">obj-rigid-obj-Categoryᵉ</a> <a id="1456" class="Symbol">=</a> <a id="1458" href="category-theory.rigid-objects-precategories%25E1%25B5%2589.html#1495" class="Function">obj-rigid-obj-Precategoryᵉ</a> <a id="1485" class="Symbol">(</a><a id="1486" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1508" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a><a id="1510" class="Symbol">)</a>

  <a id="1515" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1515" class="Function">is-rigid-rigid-obj-Categoryᵉ</a> <a id="1544" class="Symbol">:</a>
    <a id="1550" class="Symbol">(</a><a id="1551" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1551" class="Bound">xᵉ</a> <a id="1554" class="Symbol">:</a> <a id="1556" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1134" class="Function">rigid-obj-Categoryᵉ</a> <a id="1576" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a><a id="1578" class="Symbol">)</a> <a id="1580" class="Symbol">→</a>
    <a id="1586" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#823" class="Function">is-rigid-obj-Categoryᵉ</a> <a id="1609" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a> <a id="1612" class="Symbol">(</a><a id="1613" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1362" class="Function">obj-rigid-obj-Categoryᵉ</a> <a id="1637" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1551" class="Bound">xᵉ</a><a id="1639" class="Symbol">)</a>
  <a id="1643" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1515" class="Function">is-rigid-rigid-obj-Categoryᵉ</a> <a id="1672" class="Symbol">=</a>
    <a id="1678" href="category-theory.rigid-objects-precategories%25E1%25B5%2589.html#1611" class="Function">is-rigid-rigid-obj-Precategoryᵉ</a> <a id="1710" class="Symbol">(</a><a id="1711" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1733" href="category-theory.rigid-objects-categories%25E1%25B5%2589.html#1327" class="Bound">Cᵉ</a><a id="1735" class="Symbol">)</a>
</pre>
## See also

- Every object in a category is rigid if and only if it is
  [gaunt](category-theory.gaunt-categories.md).

## External links

- [rigid object](https://ncatlab.org/nlab/show/rigid+object) at $n$Lab