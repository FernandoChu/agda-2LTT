# Maps between categories

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="category-theory.maps-categories%25E1%25B5%2589.html" class="Module">category-theory.maps-categoriesᵉ</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="category-theory.categories%25E1%25B5%2589.html" class="Module">category-theory.categoriesᵉ</a>
<a id="172" class="Keyword">open</a> <a id="177" class="Keyword">import</a> <a id="184" href="category-theory.maps-precategories%25E1%25B5%2589.html" class="Module">category-theory.maps-precategoriesᵉ</a>

<a id="221" class="Keyword">open</a> <a id="226" class="Keyword">import</a> <a id="233" href="foundation.equivalences%25E1%25B5%2589.html" class="Module">foundation.equivalencesᵉ</a>
<a id="258" class="Keyword">open</a> <a id="263" class="Keyword">import</a> <a id="270" href="foundation.homotopies%25E1%25B5%2589.html" class="Module">foundation.homotopiesᵉ</a>
<a id="293" class="Keyword">open</a> <a id="298" class="Keyword">import</a> <a id="305" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="332" class="Keyword">open</a> <a id="337" class="Keyword">import</a> <a id="344" href="foundation.torsorial-type-families%25E1%25B5%2589.html" class="Module">foundation.torsorial-type-familiesᵉ</a>
<a id="380" class="Keyword">open</a> <a id="385" class="Keyword">import</a> <a id="392" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

A **map** from a [category](category-theory.categories.md) `C` to a category `D`
consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms

## Definition

### Maps between categories

<pre class="Agda"><a id="683" class="Keyword">module</a> <a id="690" href="category-theory.maps-categories%25E1%25B5%2589.html#690" class="Module">_</a>
  <a id="694" class="Symbol">{</a><a id="695" href="category-theory.maps-categories%25E1%25B5%2589.html#695" class="Bound">l1ᵉ</a> <a id="699" href="category-theory.maps-categories%25E1%25B5%2589.html#699" class="Bound">l2ᵉ</a> <a id="703" href="category-theory.maps-categories%25E1%25B5%2589.html#703" class="Bound">l3ᵉ</a> <a id="707" href="category-theory.maps-categories%25E1%25B5%2589.html#707" class="Bound">l4ᵉ</a> <a id="711" class="Symbol">:</a> <a id="713" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="718" class="Symbol">}</a>
  <a id="722" class="Symbol">(</a><a id="723" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a> <a id="726" class="Symbol">:</a> <a id="728" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="738" href="category-theory.maps-categories%25E1%25B5%2589.html#695" class="Bound">l1ᵉ</a> <a id="742" href="category-theory.maps-categories%25E1%25B5%2589.html#699" class="Bound">l2ᵉ</a><a id="745" class="Symbol">)</a>
  <a id="749" class="Symbol">(</a><a id="750" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a> <a id="753" class="Symbol">:</a> <a id="755" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="765" href="category-theory.maps-categories%25E1%25B5%2589.html#703" class="Bound">l3ᵉ</a> <a id="769" href="category-theory.maps-categories%25E1%25B5%2589.html#707" class="Bound">l4ᵉ</a><a id="772" class="Symbol">)</a>
  <a id="776" class="Keyword">where</a>

  <a id="785" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="799" class="Symbol">:</a> <a id="801" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="805" class="Symbol">(</a><a id="806" href="category-theory.maps-categories%25E1%25B5%2589.html#695" class="Bound">l1ᵉ</a> <a id="810" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="812" href="category-theory.maps-categories%25E1%25B5%2589.html#699" class="Bound">l2ᵉ</a> <a id="816" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="818" href="category-theory.maps-categories%25E1%25B5%2589.html#703" class="Bound">l3ᵉ</a> <a id="822" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="824" href="category-theory.maps-categories%25E1%25B5%2589.html#707" class="Bound">l4ᵉ</a><a id="827" class="Symbol">)</a>
  <a id="831" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="845" class="Symbol">=</a>
    <a id="851" href="category-theory.maps-precategories%25E1%25B5%2589.html#1332" class="Function">map-Precategoryᵉ</a> <a id="868" class="Symbol">(</a><a id="869" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="891" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a><a id="893" class="Symbol">)</a> <a id="895" class="Symbol">(</a><a id="896" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="918" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a><a id="920" class="Symbol">)</a>

  <a id="925" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="943" class="Symbol">:</a>
    <a id="949" class="Symbol">(</a><a id="950" href="category-theory.maps-categories%25E1%25B5%2589.html#950" class="Bound">Fᵉ</a> <a id="953" class="Symbol">:</a> <a id="955" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a><a id="968" class="Symbol">)</a> <a id="970" class="Symbol">→</a> <a id="972" href="category-theory.categories%25E1%25B5%2589.html#2501" class="Function">obj-Categoryᵉ</a> <a id="986" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a> <a id="989" class="Symbol">→</a> <a id="991" href="category-theory.categories%25E1%25B5%2589.html#2501" class="Function">obj-Categoryᵉ</a> <a id="1005" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a>
  <a id="1010" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="1028" class="Symbol">=</a>
    <a id="1034" href="category-theory.maps-precategories%25E1%25B5%2589.html#1498" class="Function">obj-map-Precategoryᵉ</a> <a id="1055" class="Symbol">(</a><a id="1056" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1078" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a><a id="1080" class="Symbol">)</a> <a id="1082" class="Symbol">(</a><a id="1083" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1105" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a><a id="1107" class="Symbol">)</a>

  <a id="1112" href="category-theory.maps-categories%25E1%25B5%2589.html#1112" class="Function">hom-map-Categoryᵉ</a> <a id="1130" class="Symbol">:</a>
    <a id="1136" class="Symbol">(</a><a id="1137" href="category-theory.maps-categories%25E1%25B5%2589.html#1137" class="Bound">Fᵉ</a> <a id="1140" class="Symbol">:</a> <a id="1142" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a><a id="1155" class="Symbol">)</a>
    <a id="1161" class="Symbol">{</a><a id="1162" href="category-theory.maps-categories%25E1%25B5%2589.html#1162" class="Bound">xᵉ</a> <a id="1165" href="category-theory.maps-categories%25E1%25B5%2589.html#1165" class="Bound">yᵉ</a> <a id="1168" class="Symbol">:</a> <a id="1170" href="category-theory.categories%25E1%25B5%2589.html#2501" class="Function">obj-Categoryᵉ</a> <a id="1184" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a><a id="1186" class="Symbol">}</a> <a id="1188" class="Symbol">→</a>
    <a id="1194" href="category-theory.categories%25E1%25B5%2589.html#2714" class="Function">hom-Categoryᵉ</a> <a id="1208" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a> <a id="1211" href="category-theory.maps-categories%25E1%25B5%2589.html#1162" class="Bound">xᵉ</a> <a id="1214" href="category-theory.maps-categories%25E1%25B5%2589.html#1165" class="Bound">yᵉ</a> <a id="1217" class="Symbol">→</a>
    <a id="1223" href="category-theory.categories%25E1%25B5%2589.html#2714" class="Function">hom-Categoryᵉ</a> <a id="1237" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a>
      <a id="1246" class="Symbol">(</a> <a id="1248" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="1266" href="category-theory.maps-categories%25E1%25B5%2589.html#1137" class="Bound">Fᵉ</a> <a id="1269" href="category-theory.maps-categories%25E1%25B5%2589.html#1162" class="Bound">xᵉ</a><a id="1271" class="Symbol">)</a>
      <a id="1279" class="Symbol">(</a> <a id="1281" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="1299" href="category-theory.maps-categories%25E1%25B5%2589.html#1137" class="Bound">Fᵉ</a> <a id="1302" href="category-theory.maps-categories%25E1%25B5%2589.html#1165" class="Bound">yᵉ</a><a id="1304" class="Symbol">)</a>
  <a id="1308" href="category-theory.maps-categories%25E1%25B5%2589.html#1112" class="Function">hom-map-Categoryᵉ</a> <a id="1326" class="Symbol">=</a>
    <a id="1332" href="category-theory.maps-precategories%25E1%25B5%2589.html#1720" class="Function">hom-map-Precategoryᵉ</a> <a id="1353" class="Symbol">(</a><a id="1354" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1376" href="category-theory.maps-categories%25E1%25B5%2589.html#723" class="Bound">Cᵉ</a><a id="1378" class="Symbol">)</a> <a id="1380" class="Symbol">(</a><a id="1381" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1403" href="category-theory.maps-categories%25E1%25B5%2589.html#750" class="Bound">Dᵉ</a><a id="1405" class="Symbol">)</a>
</pre>
## Properties

### Characterization of equality of maps between categories

<pre class="Agda"><a id="1496" class="Keyword">module</a> <a id="1503" href="category-theory.maps-categories%25E1%25B5%2589.html#1503" class="Module">_</a>
  <a id="1507" class="Symbol">{</a><a id="1508" href="category-theory.maps-categories%25E1%25B5%2589.html#1508" class="Bound">l1ᵉ</a> <a id="1512" href="category-theory.maps-categories%25E1%25B5%2589.html#1512" class="Bound">l2ᵉ</a> <a id="1516" href="category-theory.maps-categories%25E1%25B5%2589.html#1516" class="Bound">l3ᵉ</a> <a id="1520" href="category-theory.maps-categories%25E1%25B5%2589.html#1520" class="Bound">l4ᵉ</a> <a id="1524" class="Symbol">:</a> <a id="1526" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1531" class="Symbol">}</a>
  <a id="1535" class="Symbol">(</a><a id="1536" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="1539" class="Symbol">:</a> <a id="1541" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="1551" href="category-theory.maps-categories%25E1%25B5%2589.html#1508" class="Bound">l1ᵉ</a> <a id="1555" href="category-theory.maps-categories%25E1%25B5%2589.html#1512" class="Bound">l2ᵉ</a><a id="1558" class="Symbol">)</a>
  <a id="1562" class="Symbol">(</a><a id="1563" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a> <a id="1566" class="Symbol">:</a> <a id="1568" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="1578" href="category-theory.maps-categories%25E1%25B5%2589.html#1516" class="Bound">l3ᵉ</a> <a id="1582" href="category-theory.maps-categories%25E1%25B5%2589.html#1520" class="Bound">l4ᵉ</a><a id="1585" class="Symbol">)</a>
  <a id="1589" class="Keyword">where</a>

  <a id="1598" href="category-theory.maps-categories%25E1%25B5%2589.html#1598" class="Function">coherence-htpy-map-Categoryᵉ</a> <a id="1627" class="Symbol">:</a>
    <a id="1633" class="Symbol">(</a><a id="1634" href="category-theory.maps-categories%25E1%25B5%2589.html#1634" class="Bound">fᵉ</a> <a id="1637" href="category-theory.maps-categories%25E1%25B5%2589.html#1637" class="Bound">gᵉ</a> <a id="1640" class="Symbol">:</a> <a id="1642" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="1656" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="1659" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="1661" class="Symbol">)</a> <a id="1663" class="Symbol">→</a>
    <a id="1669" class="Symbol">(</a><a id="1670" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="1688" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="1691" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a> <a id="1694" href="category-theory.maps-categories%25E1%25B5%2589.html#1634" class="Bound">fᵉ</a> <a id="1697" href="foundation-core.homotopies%25E1%25B5%2589.html#2800" class="Function Operator">~ᵉ</a> <a id="1700" href="category-theory.maps-categories%25E1%25B5%2589.html#925" class="Function">obj-map-Categoryᵉ</a> <a id="1718" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="1721" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a> <a id="1724" href="category-theory.maps-categories%25E1%25B5%2589.html#1637" class="Bound">gᵉ</a><a id="1726" class="Symbol">)</a> <a id="1728" class="Symbol">→</a>
    <a id="1734" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1738" class="Symbol">(</a><a id="1739" href="category-theory.maps-categories%25E1%25B5%2589.html#1508" class="Bound">l1ᵉ</a> <a id="1743" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1745" href="category-theory.maps-categories%25E1%25B5%2589.html#1512" class="Bound">l2ᵉ</a> <a id="1749" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1751" href="category-theory.maps-categories%25E1%25B5%2589.html#1520" class="Bound">l4ᵉ</a><a id="1754" class="Symbol">)</a>
  <a id="1758" href="category-theory.maps-categories%25E1%25B5%2589.html#1598" class="Function">coherence-htpy-map-Categoryᵉ</a> <a id="1787" class="Symbol">=</a>
    <a id="1793" href="category-theory.maps-precategories%25E1%25B5%2589.html#3906" class="Function">coherence-htpy-map-Precategoryᵉ</a>
      <a id="1831" class="Symbol">(</a> <a id="1833" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1855" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="1857" class="Symbol">)</a>
      <a id="1865" class="Symbol">(</a> <a id="1867" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="1889" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="1891" class="Symbol">)</a>

  <a id="1896" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="1915" class="Symbol">:</a>
    <a id="1921" class="Symbol">(</a><a id="1922" href="category-theory.maps-categories%25E1%25B5%2589.html#1922" class="Bound">fᵉ</a> <a id="1925" href="category-theory.maps-categories%25E1%25B5%2589.html#1925" class="Bound">gᵉ</a> <a id="1928" class="Symbol">:</a> <a id="1930" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="1944" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="1947" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="1949" class="Symbol">)</a> <a id="1951" class="Symbol">→</a> <a id="1953" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1957" class="Symbol">(</a><a id="1958" href="category-theory.maps-categories%25E1%25B5%2589.html#1508" class="Bound">l1ᵉ</a> <a id="1962" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1964" href="category-theory.maps-categories%25E1%25B5%2589.html#1512" class="Bound">l2ᵉ</a> <a id="1968" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1970" href="category-theory.maps-categories%25E1%25B5%2589.html#1516" class="Bound">l3ᵉ</a> <a id="1974" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1976" href="category-theory.maps-categories%25E1%25B5%2589.html#1520" class="Bound">l4ᵉ</a><a id="1979" class="Symbol">)</a>
  <a id="1983" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="2002" class="Symbol">=</a>
    <a id="2008" href="category-theory.maps-precategories%25E1%25B5%2589.html#4594" class="Function">htpy-map-Precategoryᵉ</a> <a id="2030" class="Symbol">(</a><a id="2031" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2053" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="2055" class="Symbol">)</a> <a id="2057" class="Symbol">(</a><a id="2058" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2080" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2082" class="Symbol">)</a>

  <a id="2087" href="category-theory.maps-categories%25E1%25B5%2589.html#2087" class="Function">refl-htpy-map-Categoryᵉ</a> <a id="2111" class="Symbol">:</a>
    <a id="2117" class="Symbol">(</a><a id="2118" href="category-theory.maps-categories%25E1%25B5%2589.html#2118" class="Bound">fᵉ</a> <a id="2121" class="Symbol">:</a> <a id="2123" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="2137" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="2140" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2142" class="Symbol">)</a> <a id="2144" class="Symbol">→</a> <a id="2146" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="2165" href="category-theory.maps-categories%25E1%25B5%2589.html#2118" class="Bound">fᵉ</a> <a id="2168" href="category-theory.maps-categories%25E1%25B5%2589.html#2118" class="Bound">fᵉ</a>
  <a id="2173" href="category-theory.maps-categories%25E1%25B5%2589.html#2087" class="Function">refl-htpy-map-Categoryᵉ</a> <a id="2197" class="Symbol">=</a>
    <a id="2203" href="category-theory.maps-precategories%25E1%25B5%2589.html#4840" class="Function">refl-htpy-map-Precategoryᵉ</a> <a id="2230" class="Symbol">(</a><a id="2231" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2253" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="2255" class="Symbol">)</a> <a id="2257" class="Symbol">(</a><a id="2258" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2280" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2282" class="Symbol">)</a>

  <a id="2287" href="category-theory.maps-categories%25E1%25B5%2589.html#2287" class="Function">htpy-eq-map-Categoryᵉ</a> <a id="2309" class="Symbol">:</a>
    <a id="2315" class="Symbol">(</a><a id="2316" href="category-theory.maps-categories%25E1%25B5%2589.html#2316" class="Bound">fᵉ</a> <a id="2319" href="category-theory.maps-categories%25E1%25B5%2589.html#2319" class="Bound">gᵉ</a> <a id="2322" class="Symbol">:</a> <a id="2324" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="2338" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="2341" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2343" class="Symbol">)</a> <a id="2345" class="Symbol">→</a> <a id="2347" class="Symbol">(</a><a id="2348" href="category-theory.maps-categories%25E1%25B5%2589.html#2316" class="Bound">fᵉ</a> <a id="2351" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2354" href="category-theory.maps-categories%25E1%25B5%2589.html#2319" class="Bound">gᵉ</a><a id="2356" class="Symbol">)</a> <a id="2358" class="Symbol">→</a> <a id="2360" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="2379" href="category-theory.maps-categories%25E1%25B5%2589.html#2316" class="Bound">fᵉ</a> <a id="2382" href="category-theory.maps-categories%25E1%25B5%2589.html#2319" class="Bound">gᵉ</a>
  <a id="2387" href="category-theory.maps-categories%25E1%25B5%2589.html#2287" class="Function">htpy-eq-map-Categoryᵉ</a> <a id="2409" class="Symbol">=</a>
    <a id="2415" href="category-theory.maps-precategories%25E1%25B5%2589.html#5149" class="Function">htpy-eq-map-Precategoryᵉ</a>
      <a id="2446" class="Symbol">(</a> <a id="2448" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2470" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="2472" class="Symbol">)</a>
      <a id="2480" class="Symbol">(</a> <a id="2482" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2504" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2506" class="Symbol">)</a>

  <a id="2511" href="category-theory.maps-categories%25E1%25B5%2589.html#2511" class="Function">is-torsorial-htpy-map-Categoryᵉ</a> <a id="2543" class="Symbol">:</a>
    <a id="2549" class="Symbol">(</a><a id="2550" href="category-theory.maps-categories%25E1%25B5%2589.html#2550" class="Bound">fᵉ</a> <a id="2553" class="Symbol">:</a> <a id="2555" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="2569" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="2572" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2574" class="Symbol">)</a> <a id="2576" class="Symbol">→</a> <a id="2578" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2592" class="Symbol">(</a><a id="2593" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="2612" href="category-theory.maps-categories%25E1%25B5%2589.html#2550" class="Bound">fᵉ</a><a id="2614" class="Symbol">)</a>
  <a id="2618" href="category-theory.maps-categories%25E1%25B5%2589.html#2511" class="Function">is-torsorial-htpy-map-Categoryᵉ</a> <a id="2650" class="Symbol">=</a>
    <a id="2656" href="category-theory.maps-precategories%25E1%25B5%2589.html#5329" class="Function">is-torsorial-htpy-map-Precategoryᵉ</a>
      <a id="2697" class="Symbol">(</a> <a id="2699" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2721" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="2723" class="Symbol">)</a>
      <a id="2731" class="Symbol">(</a> <a id="2733" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2755" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2757" class="Symbol">)</a>

  <a id="2762" href="category-theory.maps-categories%25E1%25B5%2589.html#2762" class="Function">is-equiv-htpy-eq-map-Categoryᵉ</a> <a id="2793" class="Symbol">:</a>
    <a id="2799" class="Symbol">(</a><a id="2800" href="category-theory.maps-categories%25E1%25B5%2589.html#2800" class="Bound">fᵉ</a> <a id="2803" href="category-theory.maps-categories%25E1%25B5%2589.html#2803" class="Bound">gᵉ</a> <a id="2806" class="Symbol">:</a> <a id="2808" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="2822" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="2825" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="2827" class="Symbol">)</a> <a id="2829" class="Symbol">→</a> <a id="2831" href="foundation-core.equivalences%25E1%25B5%2589.html#1553" class="Function">is-equivᵉ</a> <a id="2841" class="Symbol">(</a><a id="2842" href="category-theory.maps-categories%25E1%25B5%2589.html#2287" class="Function">htpy-eq-map-Categoryᵉ</a> <a id="2864" href="category-theory.maps-categories%25E1%25B5%2589.html#2800" class="Bound">fᵉ</a> <a id="2867" href="category-theory.maps-categories%25E1%25B5%2589.html#2803" class="Bound">gᵉ</a><a id="2869" class="Symbol">)</a>
  <a id="2873" href="category-theory.maps-categories%25E1%25B5%2589.html#2762" class="Function">is-equiv-htpy-eq-map-Categoryᵉ</a> <a id="2904" class="Symbol">=</a>
    <a id="2910" href="category-theory.maps-precategories%25E1%25B5%2589.html#6447" class="Function">is-equiv-htpy-eq-map-Precategoryᵉ</a>
      <a id="2950" class="Symbol">(</a> <a id="2952" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="2974" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="2976" class="Symbol">)</a>
      <a id="2984" class="Symbol">(</a> <a id="2986" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3008" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="3010" class="Symbol">)</a>

  <a id="3015" href="category-theory.maps-categories%25E1%25B5%2589.html#3015" class="Function">equiv-htpy-eq-map-Categoryᵉ</a> <a id="3043" class="Symbol">:</a>
    <a id="3049" class="Symbol">(</a><a id="3050" href="category-theory.maps-categories%25E1%25B5%2589.html#3050" class="Bound">fᵉ</a> <a id="3053" href="category-theory.maps-categories%25E1%25B5%2589.html#3053" class="Bound">gᵉ</a> <a id="3056" class="Symbol">:</a> <a id="3058" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="3072" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="3075" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="3077" class="Symbol">)</a> <a id="3079" class="Symbol">→</a> <a id="3081" class="Symbol">(</a><a id="3082" href="category-theory.maps-categories%25E1%25B5%2589.html#3050" class="Bound">fᵉ</a> <a id="3085" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3088" href="category-theory.maps-categories%25E1%25B5%2589.html#3053" class="Bound">gᵉ</a><a id="3090" class="Symbol">)</a> <a id="3092" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="3095" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="3114" href="category-theory.maps-categories%25E1%25B5%2589.html#3050" class="Bound">fᵉ</a> <a id="3117" href="category-theory.maps-categories%25E1%25B5%2589.html#3053" class="Bound">gᵉ</a>
  <a id="3122" href="category-theory.maps-categories%25E1%25B5%2589.html#3015" class="Function">equiv-htpy-eq-map-Categoryᵉ</a> <a id="3150" class="Symbol">=</a>
    <a id="3156" href="category-theory.maps-precategories%25E1%25B5%2589.html#6721" class="Function">equiv-htpy-eq-map-Precategoryᵉ</a>
      <a id="3193" class="Symbol">(</a> <a id="3195" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3217" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="3219" class="Symbol">)</a>
      <a id="3227" class="Symbol">(</a> <a id="3229" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3251" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="3253" class="Symbol">)</a>

  <a id="3258" href="category-theory.maps-categories%25E1%25B5%2589.html#3258" class="Function">eq-htpy-map-Categoryᵉ</a> <a id="3280" class="Symbol">:</a>
    <a id="3286" class="Symbol">(</a><a id="3287" href="category-theory.maps-categories%25E1%25B5%2589.html#3287" class="Bound">fᵉ</a> <a id="3290" href="category-theory.maps-categories%25E1%25B5%2589.html#3290" class="Bound">gᵉ</a> <a id="3293" class="Symbol">:</a> <a id="3295" href="category-theory.maps-categories%25E1%25B5%2589.html#785" class="Function">map-Categoryᵉ</a> <a id="3309" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a> <a id="3312" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="3314" class="Symbol">)</a> <a id="3316" class="Symbol">→</a> <a id="3318" href="category-theory.maps-categories%25E1%25B5%2589.html#1896" class="Function">htpy-map-Categoryᵉ</a> <a id="3337" href="category-theory.maps-categories%25E1%25B5%2589.html#3287" class="Bound">fᵉ</a> <a id="3340" href="category-theory.maps-categories%25E1%25B5%2589.html#3290" class="Bound">gᵉ</a> <a id="3343" class="Symbol">→</a> <a id="3345" class="Symbol">(</a><a id="3346" href="category-theory.maps-categories%25E1%25B5%2589.html#3287" class="Bound">fᵉ</a> <a id="3349" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3352" href="category-theory.maps-categories%25E1%25B5%2589.html#3290" class="Bound">gᵉ</a><a id="3354" class="Symbol">)</a>
  <a id="3358" href="category-theory.maps-categories%25E1%25B5%2589.html#3258" class="Function">eq-htpy-map-Categoryᵉ</a> <a id="3380" class="Symbol">=</a>
    <a id="3386" href="category-theory.maps-precategories%25E1%25B5%2589.html#7005" class="Function">eq-htpy-map-Precategoryᵉ</a> <a id="3411" class="Symbol">(</a><a id="3412" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3434" href="category-theory.maps-categories%25E1%25B5%2589.html#1536" class="Bound">Cᵉ</a><a id="3436" class="Symbol">)</a> <a id="3438" class="Symbol">(</a><a id="3439" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3461" href="category-theory.maps-categories%25E1%25B5%2589.html#1563" class="Bound">Dᵉ</a><a id="3463" class="Symbol">)</a>
</pre>
## See also

- [Functors between categories](category-theory.functors-categories.md)
- [The category of maps and natural transformations between categories](category-theory.category-of-maps-categories.md)