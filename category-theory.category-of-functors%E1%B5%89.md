# The category of functors and natural transformations between two categories

<pre class="Agda"><a id="88" class="Keyword">module</a> <a id="95" href="category-theory.category-of-functors%25E1%25B5%2589.html" class="Module">category-theory.category-of-functorsᵉ</a> <a id="133" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="189" class="Keyword">open</a> <a id="194" class="Keyword">import</a> <a id="201" href="category-theory.categories%25E1%25B5%2589.html" class="Module">category-theory.categoriesᵉ</a>
<a id="229" class="Keyword">open</a> <a id="234" class="Keyword">import</a> <a id="241" href="category-theory.category-of-maps-categories%25E1%25B5%2589.html" class="Module">category-theory.category-of-maps-categoriesᵉ</a>
<a id="286" class="Keyword">open</a> <a id="291" class="Keyword">import</a> <a id="298" href="category-theory.functors-categories%25E1%25B5%2589.html" class="Module">category-theory.functors-categoriesᵉ</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="category-theory.functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.functors-precategoriesᵉ</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="category-theory.isomorphisms-in-categories%25E1%25B5%2589.html" class="Module">category-theory.isomorphisms-in-categoriesᵉ</a>
<a id="443" class="Keyword">open</a> <a id="448" class="Keyword">import</a> <a id="455" href="category-theory.natural-isomorphisms-functors-categories%25E1%25B5%2589.html" class="Module">category-theory.natural-isomorphisms-functors-categoriesᵉ</a>
<a id="513" class="Keyword">open</a> <a id="518" class="Keyword">import</a> <a id="525" href="category-theory.natural-isomorphisms-functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.natural-isomorphisms-functors-precategoriesᵉ</a>
<a id="586" class="Keyword">open</a> <a id="591" class="Keyword">import</a> <a id="598" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>
<a id="629" class="Keyword">open</a> <a id="634" class="Keyword">import</a> <a id="641" href="category-theory.precategory-of-functors%25E1%25B5%2589.html" class="Module">category-theory.precategory-of-functorsᵉ</a>

<a id="683" class="Keyword">open</a> <a id="688" class="Keyword">import</a> <a id="695" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="728" class="Keyword">open</a> <a id="733" class="Keyword">import</a> <a id="740" href="foundation.equivalences%25E1%25B5%2589.html" class="Module">foundation.equivalencesᵉ</a>
<a id="765" class="Keyword">open</a> <a id="770" class="Keyword">import</a> <a id="777" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="804" class="Keyword">open</a> <a id="809" class="Keyword">import</a> <a id="816" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
</pre>
</details>

## Idea

[Functors](category-theory.functors-categories.md) between
[categories](category-theory.categories.md) and
[natural transformations](category-theory.natural-transformations-functors-categories.md)
between them assemble to a new category whose identity functor and composition
structure are inherited pointwise from the codomain category. This is called the
**category of functors**.

## Definitons

### Extensionality of functors of precategories when the codomain is a category

<pre class="Agda"><a id="1358" class="Keyword">module</a> <a id="1365" href="category-theory.category-of-functors%25E1%25B5%2589.html#1365" class="Module">_</a>
  <a id="1369" class="Symbol">{</a><a id="1370" href="category-theory.category-of-functors%25E1%25B5%2589.html#1370" class="Bound">l1ᵉ</a> <a id="1374" href="category-theory.category-of-functors%25E1%25B5%2589.html#1374" class="Bound">l2ᵉ</a> <a id="1378" href="category-theory.category-of-functors%25E1%25B5%2589.html#1378" class="Bound">l3ᵉ</a> <a id="1382" href="category-theory.category-of-functors%25E1%25B5%2589.html#1382" class="Bound">l4ᵉ</a> <a id="1386" class="Symbol">:</a> <a id="1388" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1393" class="Symbol">}</a>
  <a id="1397" class="Symbol">(</a><a id="1398" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1401" class="Symbol">:</a> <a id="1403" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1416" href="category-theory.category-of-functors%25E1%25B5%2589.html#1370" class="Bound">l1ᵉ</a> <a id="1420" href="category-theory.category-of-functors%25E1%25B5%2589.html#1374" class="Bound">l2ᵉ</a><a id="1423" class="Symbol">)</a>
  <a id="1427" class="Symbol">(</a><a id="1428" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="1431" class="Symbol">:</a> <a id="1433" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="1446" href="category-theory.category-of-functors%25E1%25B5%2589.html#1378" class="Bound">l3ᵉ</a> <a id="1450" href="category-theory.category-of-functors%25E1%25B5%2589.html#1382" class="Bound">l4ᵉ</a><a id="1453" class="Symbol">)</a>
  <a id="1457" class="Symbol">(</a><a id="1458" href="category-theory.category-of-functors%25E1%25B5%2589.html#1458" class="Bound">is-category-Dᵉ</a> <a id="1473" class="Symbol">:</a> <a id="1475" href="category-theory.categories%25E1%25B5%2589.html#1906" class="Function">is-category-Precategoryᵉ</a> <a id="1500" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a><a id="1502" class="Symbol">)</a>
  <a id="1506" class="Keyword">where</a>

  <a id="1515" href="category-theory.category-of-functors%25E1%25B5%2589.html#1515" class="Function">equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ</a> <a id="1579" class="Symbol">:</a>
    <a id="1585" class="Symbol">(</a><a id="1586" href="category-theory.category-of-functors%25E1%25B5%2589.html#1586" class="Bound">Fᵉ</a> <a id="1589" href="category-theory.category-of-functors%25E1%25B5%2589.html#1589" class="Bound">Gᵉ</a> <a id="1592" class="Symbol">:</a> <a id="1594" href="category-theory.functors-precategories%25E1%25B5%2589.html#3980" class="Function">functor-Precategoryᵉ</a> <a id="1615" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1618" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a><a id="1620" class="Symbol">)</a> <a id="1622" class="Symbol">→</a>
    <a id="1628" href="category-theory.functors-precategories%25E1%25B5%2589.html#11177" class="Function">htpy-functor-Precategoryᵉ</a> <a id="1654" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1657" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="1660" href="category-theory.category-of-functors%25E1%25B5%2589.html#1586" class="Bound">Fᵉ</a> <a id="1663" href="category-theory.category-of-functors%25E1%25B5%2589.html#1589" class="Bound">Gᵉ</a> <a id="1666" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="1669" href="category-theory.natural-isomorphisms-functors-precategories%25E1%25B5%2589.html#4900" class="Function">natural-isomorphism-Precategoryᵉ</a> <a id="1702" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1705" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="1708" href="category-theory.category-of-functors%25E1%25B5%2589.html#1586" class="Bound">Fᵉ</a> <a id="1711" href="category-theory.category-of-functors%25E1%25B5%2589.html#1589" class="Bound">Gᵉ</a>
  <a id="1716" href="category-theory.category-of-functors%25E1%25B5%2589.html#1515" class="Function">equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ</a> <a id="1780" href="category-theory.category-of-functors%25E1%25B5%2589.html#1780" class="Bound">Fᵉ</a> <a id="1783" href="category-theory.category-of-functors%25E1%25B5%2589.html#1783" class="Bound">Gᵉ</a> <a id="1786" class="Symbol">=</a>
    <a id="1792" href="category-theory.category-of-maps-categories%25E1%25B5%2589.html#2032" class="Function">equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ</a> <a id="1852" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1855" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a>
      <a id="1864" class="Symbol">(</a> <a id="1866" href="category-theory.category-of-functors%25E1%25B5%2589.html#1458" class="Bound">is-category-Dᵉ</a><a id="1880" class="Symbol">)</a>
      <a id="1888" class="Symbol">(</a> <a id="1890" href="category-theory.functors-precategories%25E1%25B5%2589.html#4760" class="Function">map-functor-Precategoryᵉ</a> <a id="1915" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1918" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="1921" href="category-theory.category-of-functors%25E1%25B5%2589.html#1780" class="Bound">Fᵉ</a><a id="1923" class="Symbol">)</a>
      <a id="1931" class="Symbol">(</a> <a id="1933" href="category-theory.functors-precategories%25E1%25B5%2589.html#4760" class="Function">map-functor-Precategoryᵉ</a> <a id="1958" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="1961" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="1964" href="category-theory.category-of-functors%25E1%25B5%2589.html#1783" class="Bound">Gᵉ</a><a id="1966" class="Symbol">)</a>

  <a id="1971" href="category-theory.category-of-functors%25E1%25B5%2589.html#1971" class="Function">extensionality-functor-is-category-Precategoryᵉ</a> <a id="2019" class="Symbol">:</a>
    <a id="2025" class="Symbol">(</a><a id="2026" href="category-theory.category-of-functors%25E1%25B5%2589.html#2026" class="Bound">Fᵉ</a> <a id="2029" href="category-theory.category-of-functors%25E1%25B5%2589.html#2029" class="Bound">Gᵉ</a> <a id="2032" class="Symbol">:</a> <a id="2034" href="category-theory.functors-precategories%25E1%25B5%2589.html#3980" class="Function">functor-Precategoryᵉ</a> <a id="2055" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="2058" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a><a id="2060" class="Symbol">)</a> <a id="2062" class="Symbol">→</a>
    <a id="2068" class="Symbol">(</a> <a id="2070" href="category-theory.category-of-functors%25E1%25B5%2589.html#2026" class="Bound">Fᵉ</a> <a id="2073" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2076" href="category-theory.category-of-functors%25E1%25B5%2589.html#2029" class="Bound">Gᵉ</a><a id="2078" class="Symbol">)</a> <a id="2080" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a>
    <a id="2087" class="Symbol">(</a> <a id="2089" href="category-theory.natural-isomorphisms-functors-precategories%25E1%25B5%2589.html#4900" class="Function">natural-isomorphism-Precategoryᵉ</a> <a id="2122" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="2125" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="2128" href="category-theory.category-of-functors%25E1%25B5%2589.html#2026" class="Bound">Fᵉ</a> <a id="2131" href="category-theory.category-of-functors%25E1%25B5%2589.html#2029" class="Bound">Gᵉ</a><a id="2133" class="Symbol">)</a>
  <a id="2137" href="category-theory.category-of-functors%25E1%25B5%2589.html#1971" class="Function">extensionality-functor-is-category-Precategoryᵉ</a> <a id="2185" href="category-theory.category-of-functors%25E1%25B5%2589.html#2185" class="Bound">Fᵉ</a> <a id="2188" href="category-theory.category-of-functors%25E1%25B5%2589.html#2188" class="Bound">Gᵉ</a> <a id="2191" class="Symbol">=</a>
    <a id="2197" class="Symbol">(</a> <a id="2199" href="category-theory.category-of-functors%25E1%25B5%2589.html#1515" class="Function">equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ</a> <a id="2263" href="category-theory.category-of-functors%25E1%25B5%2589.html#2185" class="Bound">Fᵉ</a> <a id="2266" href="category-theory.category-of-functors%25E1%25B5%2589.html#2188" class="Bound">Gᵉ</a><a id="2268" class="Symbol">)</a> <a id="2270" href="foundation-core.equivalences%25E1%25B5%2589.html#14156" class="Function Operator">∘eᵉ</a>
    <a id="2278" class="Symbol">(</a> <a id="2280" href="category-theory.functors-precategories%25E1%25B5%2589.html#11384" class="Function">equiv-htpy-eq-functor-Precategoryᵉ</a> <a id="2315" href="category-theory.category-of-functors%25E1%25B5%2589.html#1398" class="Bound">Cᵉ</a> <a id="2318" href="category-theory.category-of-functors%25E1%25B5%2589.html#1428" class="Bound">Dᵉ</a> <a id="2321" href="category-theory.category-of-functors%25E1%25B5%2589.html#2185" class="Bound">Fᵉ</a> <a id="2324" href="category-theory.category-of-functors%25E1%25B5%2589.html#2188" class="Bound">Gᵉ</a><a id="2326" class="Symbol">)</a>
</pre>
### When the codomain is a category the functor precategory is a category

<pre class="Agda"><a id="2416" class="Keyword">module</a> <a id="2423" href="category-theory.category-of-functors%25E1%25B5%2589.html#2423" class="Module">_</a>
  <a id="2427" class="Symbol">{</a><a id="2428" href="category-theory.category-of-functors%25E1%25B5%2589.html#2428" class="Bound">l1ᵉ</a> <a id="2432" href="category-theory.category-of-functors%25E1%25B5%2589.html#2432" class="Bound">l2ᵉ</a> <a id="2436" href="category-theory.category-of-functors%25E1%25B5%2589.html#2436" class="Bound">l3ᵉ</a> <a id="2440" href="category-theory.category-of-functors%25E1%25B5%2589.html#2440" class="Bound">l4ᵉ</a> <a id="2444" class="Symbol">:</a> <a id="2446" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2451" class="Symbol">}</a>
  <a id="2455" class="Symbol">(</a><a id="2456" href="category-theory.category-of-functors%25E1%25B5%2589.html#2456" class="Bound">Cᵉ</a> <a id="2459" class="Symbol">:</a> <a id="2461" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="2474" href="category-theory.category-of-functors%25E1%25B5%2589.html#2428" class="Bound">l1ᵉ</a> <a id="2478" href="category-theory.category-of-functors%25E1%25B5%2589.html#2432" class="Bound">l2ᵉ</a><a id="2481" class="Symbol">)</a>
  <a id="2485" class="Symbol">(</a><a id="2486" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a> <a id="2489" class="Symbol">:</a> <a id="2491" href="category-theory.precategories%25E1%25B5%2589.html#3370" class="Function">Precategoryᵉ</a> <a id="2504" href="category-theory.category-of-functors%25E1%25B5%2589.html#2436" class="Bound">l3ᵉ</a> <a id="2508" href="category-theory.category-of-functors%25E1%25B5%2589.html#2440" class="Bound">l4ᵉ</a><a id="2511" class="Symbol">)</a>
  <a id="2515" class="Symbol">(</a><a id="2516" href="category-theory.category-of-functors%25E1%25B5%2589.html#2516" class="Bound">is-category-Dᵉ</a> <a id="2531" class="Symbol">:</a> <a id="2533" href="category-theory.categories%25E1%25B5%2589.html#1906" class="Function">is-category-Precategoryᵉ</a> <a id="2558" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a><a id="2560" class="Symbol">)</a>
  <a id="2564" class="Keyword">where</a>

  <a id="2573" class="Keyword">abstract</a>
    <a id="2586" href="category-theory.category-of-functors%25E1%25B5%2589.html#2586" class="Function">is-category-functor-precategory-is-category-Precategoryᵉ</a> <a id="2643" class="Symbol">:</a>
      <a id="2651" href="category-theory.categories%25E1%25B5%2589.html#1906" class="Function">is-category-Precategoryᵉ</a> <a id="2676" class="Symbol">(</a><a id="2677" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#5998" class="Function">functor-precategory-Precategoryᵉ</a> <a id="2710" href="category-theory.category-of-functors%25E1%25B5%2589.html#2456" class="Bound">Cᵉ</a> <a id="2713" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a><a id="2715" class="Symbol">)</a>
    <a id="2721" href="category-theory.category-of-functors%25E1%25B5%2589.html#2586" class="Function">is-category-functor-precategory-is-category-Precategoryᵉ</a> <a id="2778" href="category-theory.category-of-functors%25E1%25B5%2589.html#2778" class="Bound">Fᵉ</a> <a id="2781" href="category-theory.category-of-functors%25E1%25B5%2589.html#2781" class="Bound">Gᵉ</a> <a id="2784" class="Symbol">=</a>
      <a id="2792" href="foundation-core.equivalences%25E1%25B5%2589.html#15867" class="Function">is-equiv-htpy-equivᵉ</a>
        <a id="2821" class="Symbol">(</a> <a id="2823" class="Symbol">(</a> <a id="2825" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#11936" class="Function">equiv-iso-functor-natural-isomorphism-Precategoryᵉ</a> <a id="2876" href="category-theory.category-of-functors%25E1%25B5%2589.html#2456" class="Bound">Cᵉ</a> <a id="2879" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a> <a id="2882" href="category-theory.category-of-functors%25E1%25B5%2589.html#2778" class="Bound">Fᵉ</a> <a id="2885" href="category-theory.category-of-functors%25E1%25B5%2589.html#2781" class="Bound">Gᵉ</a><a id="2887" class="Symbol">)</a> <a id="2889" href="foundation-core.equivalences%25E1%25B5%2589.html#14156" class="Function Operator">∘eᵉ</a>
          <a id="2903" class="Symbol">(</a> <a id="2905" href="category-theory.category-of-functors%25E1%25B5%2589.html#1971" class="Function">extensionality-functor-is-category-Precategoryᵉ</a>
              <a id="2967" href="category-theory.category-of-functors%25E1%25B5%2589.html#2456" class="Bound">Cᵉ</a> <a id="2970" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a> <a id="2973" href="category-theory.category-of-functors%25E1%25B5%2589.html#2516" class="Bound">is-category-Dᵉ</a> <a id="2988" href="category-theory.category-of-functors%25E1%25B5%2589.html#2778" class="Bound">Fᵉ</a> <a id="2991" href="category-theory.category-of-functors%25E1%25B5%2589.html#2781" class="Bound">Gᵉ</a><a id="2993" class="Symbol">))</a>
        <a id="3004" class="Symbol">(</a> <a id="3006" class="Symbol">λ</a> <a id="3008" class="Keyword">where</a>
          <a id="3024" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="3030" class="Symbol">→</a>
            <a id="3044" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#12779" class="Function">compute-iso-functor-natural-isomorphism-eq-Precategoryᵉ</a> <a id="3100" href="category-theory.category-of-functors%25E1%25B5%2589.html#2456" class="Bound">Cᵉ</a> <a id="3103" href="category-theory.category-of-functors%25E1%25B5%2589.html#2486" class="Bound">Dᵉ</a> <a id="3106" href="category-theory.category-of-functors%25E1%25B5%2589.html#2778" class="Bound">Fᵉ</a> <a id="3109" href="category-theory.category-of-functors%25E1%25B5%2589.html#2781" class="Bound">Gᵉ</a> <a id="3112" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="3117" class="Symbol">)</a>
</pre>
## Definitions

### The category of functors and natural transformations between categories

<pre class="Agda"><a id="3225" class="Keyword">module</a> <a id="3232" href="category-theory.category-of-functors%25E1%25B5%2589.html#3232" class="Module">_</a>
  <a id="3236" class="Symbol">{</a><a id="3237" href="category-theory.category-of-functors%25E1%25B5%2589.html#3237" class="Bound">l1ᵉ</a> <a id="3241" href="category-theory.category-of-functors%25E1%25B5%2589.html#3241" class="Bound">l2ᵉ</a> <a id="3245" href="category-theory.category-of-functors%25E1%25B5%2589.html#3245" class="Bound">l3ᵉ</a> <a id="3249" href="category-theory.category-of-functors%25E1%25B5%2589.html#3249" class="Bound">l4ᵉ</a> <a id="3253" class="Symbol">:</a> <a id="3255" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3260" class="Symbol">}</a>
  <a id="3264" class="Symbol">(</a><a id="3265" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a> <a id="3268" class="Symbol">:</a> <a id="3270" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="3280" href="category-theory.category-of-functors%25E1%25B5%2589.html#3237" class="Bound">l1ᵉ</a> <a id="3284" href="category-theory.category-of-functors%25E1%25B5%2589.html#3241" class="Bound">l2ᵉ</a><a id="3287" class="Symbol">)</a> <a id="3289" class="Symbol">(</a><a id="3290" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a> <a id="3293" class="Symbol">:</a> <a id="3295" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="3305" href="category-theory.category-of-functors%25E1%25B5%2589.html#3245" class="Bound">l3ᵉ</a> <a id="3309" href="category-theory.category-of-functors%25E1%25B5%2589.html#3249" class="Bound">l4ᵉ</a><a id="3312" class="Symbol">)</a>
  <a id="3316" class="Keyword">where</a>

  <a id="3325" href="category-theory.category-of-functors%25E1%25B5%2589.html#3325" class="Function">functor-category-Categoryᵉ</a> <a id="3352" class="Symbol">:</a>
    <a id="3358" href="category-theory.categories%25E1%25B5%2589.html#2222" class="Function">Categoryᵉ</a> <a id="3368" class="Symbol">(</a><a id="3369" href="category-theory.category-of-functors%25E1%25B5%2589.html#3237" class="Bound">l1ᵉ</a> <a id="3373" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3375" href="category-theory.category-of-functors%25E1%25B5%2589.html#3241" class="Bound">l2ᵉ</a> <a id="3379" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3381" href="category-theory.category-of-functors%25E1%25B5%2589.html#3245" class="Bound">l3ᵉ</a> <a id="3385" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3387" href="category-theory.category-of-functors%25E1%25B5%2589.html#3249" class="Bound">l4ᵉ</a><a id="3390" class="Symbol">)</a> <a id="3392" class="Symbol">(</a><a id="3393" href="category-theory.category-of-functors%25E1%25B5%2589.html#3237" class="Bound">l1ᵉ</a> <a id="3397" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3399" href="category-theory.category-of-functors%25E1%25B5%2589.html#3241" class="Bound">l2ᵉ</a> <a id="3403" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3405" href="category-theory.category-of-functors%25E1%25B5%2589.html#3249" class="Bound">l4ᵉ</a><a id="3408" class="Symbol">)</a>
  <a id="3412" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3417" href="category-theory.category-of-functors%25E1%25B5%2589.html#3325" class="Function">functor-category-Categoryᵉ</a> <a id="3444" class="Symbol">=</a>
    <a id="3450" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#5998" class="Function">functor-precategory-Precategoryᵉ</a>
      <a id="3489" class="Symbol">(</a> <a id="3491" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3513" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a><a id="3515" class="Symbol">)</a>
      <a id="3523" class="Symbol">(</a> <a id="3525" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3547" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="3549" class="Symbol">)</a>
  <a id="3553" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3558" href="category-theory.category-of-functors%25E1%25B5%2589.html#3325" class="Function">functor-category-Categoryᵉ</a> <a id="3585" class="Symbol">=</a>
    <a id="3591" href="category-theory.category-of-functors%25E1%25B5%2589.html#2586" class="Function">is-category-functor-precategory-is-category-Precategoryᵉ</a>
      <a id="3654" class="Symbol">(</a> <a id="3656" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3678" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a><a id="3680" class="Symbol">)</a>
      <a id="3688" class="Symbol">(</a> <a id="3690" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="3712" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="3714" class="Symbol">)</a>
      <a id="3722" class="Symbol">(</a> <a id="3724" href="category-theory.categories%25E1%25B5%2589.html#5090" class="Function">is-category-Categoryᵉ</a> <a id="3746" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="3748" class="Symbol">)</a>

  <a id="3753" href="category-theory.category-of-functors%25E1%25B5%2589.html#3753" class="Function">extensionality-functor-Categoryᵉ</a> <a id="3786" class="Symbol">:</a>
    <a id="3792" class="Symbol">(</a><a id="3793" href="category-theory.category-of-functors%25E1%25B5%2589.html#3793" class="Bound">Fᵉ</a> <a id="3796" href="category-theory.category-of-functors%25E1%25B5%2589.html#3796" class="Bound">Gᵉ</a> <a id="3799" class="Symbol">:</a> <a id="3801" href="category-theory.functors-categories%25E1%25B5%2589.html#2321" class="Function">functor-Categoryᵉ</a> <a id="3819" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a> <a id="3822" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="3824" class="Symbol">)</a> <a id="3826" class="Symbol">→</a>
    <a id="3832" class="Symbol">(</a><a id="3833" href="category-theory.category-of-functors%25E1%25B5%2589.html#3793" class="Bound">Fᵉ</a> <a id="3836" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3839" href="category-theory.category-of-functors%25E1%25B5%2589.html#3796" class="Bound">Gᵉ</a><a id="3841" class="Symbol">)</a> <a id="3843" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="3846" href="category-theory.natural-isomorphisms-functors-categories%25E1%25B5%2589.html#4713" class="Function">natural-isomorphism-Categoryᵉ</a> <a id="3876" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a> <a id="3879" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a> <a id="3882" href="category-theory.category-of-functors%25E1%25B5%2589.html#3793" class="Bound">Fᵉ</a> <a id="3885" href="category-theory.category-of-functors%25E1%25B5%2589.html#3796" class="Bound">Gᵉ</a>
  <a id="3890" href="category-theory.category-of-functors%25E1%25B5%2589.html#3753" class="Function">extensionality-functor-Categoryᵉ</a> <a id="3923" href="category-theory.category-of-functors%25E1%25B5%2589.html#3923" class="Bound">Fᵉ</a> <a id="3926" href="category-theory.category-of-functors%25E1%25B5%2589.html#3926" class="Bound">Gᵉ</a> <a id="3929" class="Symbol">=</a>
    <a id="3935" class="Symbol">(</a> <a id="3937" href="category-theory.precategory-of-functors%25E1%25B5%2589.html#12239" class="Function">equiv-natural-isomorphism-iso-functor-Precategoryᵉ</a>
      <a id="3994" class="Symbol">(</a> <a id="3996" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="4018" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a><a id="4020" class="Symbol">)</a>
      <a id="4028" class="Symbol">(</a> <a id="4030" href="category-theory.categories%25E1%25B5%2589.html#2419" class="Function">precategory-Categoryᵉ</a> <a id="4052" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="4054" class="Symbol">)</a> <a id="4056" href="category-theory.category-of-functors%25E1%25B5%2589.html#3923" class="Bound">Fᵉ</a> <a id="4059" href="category-theory.category-of-functors%25E1%25B5%2589.html#3926" class="Bound">Gᵉ</a><a id="4061" class="Symbol">)</a> <a id="4063" href="foundation-core.equivalences%25E1%25B5%2589.html#14156" class="Function Operator">∘eᵉ</a>
    <a id="4071" class="Symbol">(</a> <a id="4073" href="category-theory.isomorphisms-in-categories%25E1%25B5%2589.html#21821" class="Function">extensionality-obj-Categoryᵉ</a> <a id="4102" href="category-theory.category-of-functors%25E1%25B5%2589.html#3325" class="Function">functor-category-Categoryᵉ</a> <a id="4129" href="category-theory.category-of-functors%25E1%25B5%2589.html#3923" class="Bound">Fᵉ</a> <a id="4132" href="category-theory.category-of-functors%25E1%25B5%2589.html#3926" class="Bound">Gᵉ</a><a id="4134" class="Symbol">)</a>

  <a id="4139" href="category-theory.category-of-functors%25E1%25B5%2589.html#4139" class="Function">eq-natural-isomorphism-functor-Categoryᵉ</a> <a id="4180" class="Symbol">:</a>
    <a id="4186" class="Symbol">(</a><a id="4187" href="category-theory.category-of-functors%25E1%25B5%2589.html#4187" class="Bound">Fᵉ</a> <a id="4190" href="category-theory.category-of-functors%25E1%25B5%2589.html#4190" class="Bound">Gᵉ</a> <a id="4193" class="Symbol">:</a> <a id="4195" href="category-theory.functors-categories%25E1%25B5%2589.html#2321" class="Function">functor-Categoryᵉ</a> <a id="4213" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a> <a id="4216" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a><a id="4218" class="Symbol">)</a> <a id="4220" class="Symbol">→</a>
    <a id="4226" href="category-theory.natural-isomorphisms-functors-categories%25E1%25B5%2589.html#4713" class="Function">natural-isomorphism-Categoryᵉ</a> <a id="4256" href="category-theory.category-of-functors%25E1%25B5%2589.html#3265" class="Bound">Cᵉ</a> <a id="4259" href="category-theory.category-of-functors%25E1%25B5%2589.html#3290" class="Bound">Dᵉ</a> <a id="4262" href="category-theory.category-of-functors%25E1%25B5%2589.html#4187" class="Bound">Fᵉ</a> <a id="4265" href="category-theory.category-of-functors%25E1%25B5%2589.html#4190" class="Bound">Gᵉ</a> <a id="4268" class="Symbol">→</a> <a id="4270" href="category-theory.category-of-functors%25E1%25B5%2589.html#4187" class="Bound">Fᵉ</a> <a id="4273" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="4276" href="category-theory.category-of-functors%25E1%25B5%2589.html#4190" class="Bound">Gᵉ</a>
  <a id="4281" href="category-theory.category-of-functors%25E1%25B5%2589.html#4139" class="Function">eq-natural-isomorphism-functor-Categoryᵉ</a> <a id="4322" href="category-theory.category-of-functors%25E1%25B5%2589.html#4322" class="Bound">Fᵉ</a> <a id="4325" href="category-theory.category-of-functors%25E1%25B5%2589.html#4325" class="Bound">Gᵉ</a> <a id="4328" class="Symbol">=</a>
    <a id="4334" href="foundation-core.equivalences%25E1%25B5%2589.html#8521" class="Function">map-inv-equivᵉ</a> <a id="4349" class="Symbol">(</a><a id="4350" href="category-theory.category-of-functors%25E1%25B5%2589.html#3753" class="Function">extensionality-functor-Categoryᵉ</a> <a id="4383" href="category-theory.category-of-functors%25E1%25B5%2589.html#4322" class="Bound">Fᵉ</a> <a id="4386" href="category-theory.category-of-functors%25E1%25B5%2589.html#4325" class="Bound">Gᵉ</a><a id="4388" class="Symbol">)</a>
</pre>