# Action on equivalences of functions

<pre class="Agda"><a id="48" class="Keyword">module</a> <a id="55" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-equivalences-functionsᵉ</a> <a id="100" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="156" class="Keyword">open</a> <a id="161" class="Keyword">import</a> <a id="168" href="foundation.action-on-higher-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-higher-identifications-functionsᵉ</a>
<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="328" class="Keyword">open</a> <a id="333" class="Keyword">import</a> <a id="340" href="foundation.equivalence-induction%25E1%25B5%2589.html" class="Module">foundation.equivalence-inductionᵉ</a>
<a id="374" class="Keyword">open</a> <a id="379" class="Keyword">import</a> <a id="386" href="foundation.univalence%25E1%25B5%2589.html" class="Module">foundation.univalenceᵉ</a>
<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="450" class="Keyword">open</a> <a id="455" class="Keyword">import</a> <a id="462" href="foundation-core.constant-maps%25E1%25B5%2589.html" class="Module">foundation-core.constant-mapsᵉ</a>
<a id="493" class="Keyword">open</a> <a id="498" class="Keyword">import</a> <a id="505" href="foundation-core.contractible-types%25E1%25B5%2589.html" class="Module">foundation-core.contractible-typesᵉ</a>
<a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
</pre>
</details>

## Idea

Given a map between universes `f : 𝒰 → 𝒱`, then applying the
[action on identifications](foundation.action-on-identifications-functions.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us the
{{#concept "action on equivalences" Agda=action-equiv-function}}

```text
  action-equiv-function f : X ≃ Y → f X ≃ f Y.
```

Alternatively, one can apply
[transport along identifications](foundation-core.transport-along-identifications.md)
to get
[transport along equivalences](foundation.transport-along-equivalences.md).
However, by univalence such an action must also be unique, hence these two
constructions coincide.

## Definition

<pre class="Agda"><a id="1371" class="Keyword">module</a> <a id="1378" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1378" class="Module">_</a>
  <a id="1382" class="Symbol">{</a><a id="1383" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a> <a id="1387" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1387" class="Bound">l2ᵉ</a> <a id="1391" class="Symbol">:</a> <a id="1393" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1398" class="Symbol">}</a> <a id="1400" class="Symbol">{</a><a id="1401" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1401" class="Bound">Bᵉ</a> <a id="1404" class="Symbol">:</a> <a id="1406" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1410" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1387" class="Bound">l2ᵉ</a><a id="1413" class="Symbol">}</a> <a id="1415" class="Symbol">(</a><a id="1416" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1419" class="Symbol">:</a> <a id="1421" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1425" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a> <a id="1429" class="Symbol">→</a> <a id="1431" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1401" class="Bound">Bᵉ</a><a id="1433" class="Symbol">)</a>
  <a id="1437" class="Keyword">where</a>

  <a id="1446" class="Keyword">abstract</a>
    <a id="1459" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1459" class="Function">unique-action-equiv-functionᵉ</a> <a id="1489" class="Symbol">:</a>
      <a id="1497" class="Symbol">(</a><a id="1498" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1498" class="Bound">Xᵉ</a> <a id="1501" class="Symbol">:</a> <a id="1503" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1507" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a><a id="1510" class="Symbol">)</a> <a id="1512" class="Symbol">→</a>
      <a id="1520" href="foundation-core.contractible-types%25E1%25B5%2589.html#908" class="Function">is-contrᵉ</a>
        <a id="1538" class="Symbol">(</a> <a id="1540" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1543" class="Symbol">((</a><a id="1545" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1545" class="Bound">Yᵉ</a> <a id="1548" class="Symbol">:</a> <a id="1550" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1554" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a><a id="1557" class="Symbol">)</a> <a id="1559" class="Symbol">→</a> <a id="1561" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1498" class="Bound">Xᵉ</a> <a id="1564" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="1567" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1545" class="Bound">Yᵉ</a> <a id="1570" class="Symbol">→</a> <a id="1572" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1575" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1498" class="Bound">Xᵉ</a> <a id="1578" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1581" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1584" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1545" class="Bound">Yᵉ</a><a id="1586" class="Symbol">)</a> <a id="1588" class="Symbol">(λ</a> <a id="1591" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1591" class="Bound">hᵉ</a> <a id="1594" class="Symbol">→</a> <a id="1596" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1591" class="Bound">hᵉ</a> <a id="1599" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1498" class="Bound">Xᵉ</a> <a id="1602" href="foundation-core.equivalences%25E1%25B5%2589.html#4139" class="Function">id-equivᵉ</a> <a id="1612" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1615" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="1620" class="Symbol">))</a>
    <a id="1627" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1459" class="Function">unique-action-equiv-functionᵉ</a> <a id="1657" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1657" class="Bound">Xᵉ</a> <a id="1660" class="Symbol">=</a>
      <a id="1668" href="foundation.equivalence-induction%25E1%25B5%2589.html#6016" class="Function">is-contr-map-ev-id-equivᵉ</a> <a id="1694" class="Symbol">(λ</a> <a id="1697" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1697" class="Bound">Yᵉ</a> <a id="1700" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1700" class="Bound">eᵉ</a> <a id="1703" class="Symbol">→</a> <a id="1705" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1708" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1657" class="Bound">Xᵉ</a> <a id="1711" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1714" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1717" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1697" class="Bound">Yᵉ</a><a id="1719" class="Symbol">)</a> <a id="1721" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="1730" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="1753" class="Symbol">:</a>
    <a id="1759" class="Symbol">{</a><a id="1760" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1760" class="Bound">Xᵉ</a> <a id="1763" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1763" class="Bound">Yᵉ</a> <a id="1766" class="Symbol">:</a> <a id="1768" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1772" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a><a id="1775" class="Symbol">}</a> <a id="1777" class="Symbol">→</a> <a id="1779" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1760" class="Bound">Xᵉ</a> <a id="1782" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="1785" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1763" class="Bound">Yᵉ</a> <a id="1788" class="Symbol">→</a> <a id="1790" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1793" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1760" class="Bound">Xᵉ</a> <a id="1796" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1799" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1802" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1763" class="Bound">Yᵉ</a>
  <a id="1807" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="1830" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1830" class="Bound">eᵉ</a> <a id="1833" class="Symbol">=</a> <a id="1835" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="1839" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="1842" class="Symbol">(</a><a id="1843" href="foundation.univalence%25E1%25B5%2589.html#1821" class="Postulate">eq-equivᵉ</a> <a id="1853" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1830" class="Bound">eᵉ</a><a id="1855" class="Symbol">)</a>

  <a id="1860" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1860" class="Function">compute-action-equiv-function-id-equivᵉ</a> <a id="1900" class="Symbol">:</a>
    <a id="1906" class="Symbol">(</a><a id="1907" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1907" class="Bound">Xᵉ</a> <a id="1910" class="Symbol">:</a> <a id="1912" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1916" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1383" class="Bound">l1ᵉ</a><a id="1919" class="Symbol">)</a> <a id="1921" class="Symbol">→</a> <a id="1923" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="1946" href="foundation-core.equivalences%25E1%25B5%2589.html#4139" class="Function">id-equivᵉ</a> <a id="1956" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1959" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
  <a id="1967" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1860" class="Function">compute-action-equiv-function-id-equivᵉ</a> <a id="2007" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2007" class="Bound">Xᵉ</a> <a id="2010" class="Symbol">=</a>
    <a id="2016" href="foundation.action-on-higher-identifications-functions%25E1%25B5%2589.html#1161" class="Function">ap²ᵉ</a> <a id="2021" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1416" class="Bound">fᵉ</a> <a id="2024" class="Symbol">(</a><a id="2025" href="foundation.univalence%25E1%25B5%2589.html#2907" class="Function">compute-eq-equiv-id-equivᵉ</a> <a id="2052" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2007" class="Bound">Xᵉ</a><a id="2054" class="Symbol">)</a>
</pre>
## Properties

### The action on equivalences of a constant map is constant

<pre class="Agda"><a id="compute-action-equiv-function-constᵉ"></a><a id="2146" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2146" class="Function">compute-action-equiv-function-constᵉ</a> <a id="2183" class="Symbol">:</a>
  <a id="2187" class="Symbol">{</a><a id="2188" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2188" class="Bound">l1ᵉ</a> <a id="2192" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2192" class="Bound">l2ᵉ</a> <a id="2196" class="Symbol">:</a> <a id="2198" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2203" class="Symbol">}</a> <a id="2205" class="Symbol">{</a><a id="2206" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2206" class="Bound">Bᵉ</a> <a id="2209" class="Symbol">:</a> <a id="2211" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2215" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2192" class="Bound">l2ᵉ</a><a id="2218" class="Symbol">}</a> <a id="2220" class="Symbol">(</a><a id="2221" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2221" class="Bound">bᵉ</a> <a id="2224" class="Symbol">:</a> <a id="2226" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2206" class="Bound">Bᵉ</a><a id="2228" class="Symbol">)</a> <a id="2230" class="Symbol">{</a><a id="2231" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2231" class="Bound">Xᵉ</a> <a id="2234" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2234" class="Bound">Yᵉ</a> <a id="2237" class="Symbol">:</a> <a id="2239" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2243" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2188" class="Bound">l1ᵉ</a><a id="2246" class="Symbol">}</a>
  <a id="2250" class="Symbol">(</a><a id="2251" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2251" class="Bound">eᵉ</a> <a id="2254" class="Symbol">:</a> <a id="2256" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2231" class="Bound">Xᵉ</a> <a id="2259" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="2262" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2234" class="Bound">Yᵉ</a><a id="2264" class="Symbol">)</a> <a id="2266" class="Symbol">→</a> <a id="2268" class="Symbol">(</a><a id="2269" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="2292" class="Symbol">(</a><a id="2293" href="foundation-core.constant-maps%25E1%25B5%2589.html#474" class="Function">constᵉ</a> <a id="2300" class="Symbol">(</a><a id="2301" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2305" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2188" class="Bound">l1ᵉ</a><a id="2308" class="Symbol">)</a> <a id="2310" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2221" class="Bound">bᵉ</a><a id="2312" class="Symbol">)</a> <a id="2314" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2251" class="Bound">eᵉ</a><a id="2316" class="Symbol">)</a> <a id="2318" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2321" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
<a id="2327" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2146" class="Function">compute-action-equiv-function-constᵉ</a> <a id="2364" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2364" class="Bound">bᵉ</a> <a id="2367" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2367" class="Bound">eᵉ</a> <a id="2370" class="Symbol">=</a> <a id="2372" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#2743" class="Function">ap-constᵉ</a> <a id="2382" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2364" class="Bound">bᵉ</a> <a id="2385" class="Symbol">(</a><a id="2386" href="foundation.univalence%25E1%25B5%2589.html#1821" class="Postulate">eq-equivᵉ</a> <a id="2396" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2367" class="Bound">eᵉ</a><a id="2398" class="Symbol">)</a>
</pre>
### The action on equivalences of any map preserves composition of equivalences

<pre class="Agda"><a id="distributive-action-equiv-function-comp-equivᵉ"></a><a id="2494" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2494" class="Function">distributive-action-equiv-function-comp-equivᵉ</a> <a id="2541" class="Symbol">:</a>
  <a id="2545" class="Symbol">{</a><a id="2546" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2546" class="Bound">l1ᵉ</a> <a id="2550" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2550" class="Bound">l2ᵉ</a> <a id="2554" class="Symbol">:</a> <a id="2556" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2561" class="Symbol">}</a> <a id="2563" class="Symbol">{</a><a id="2564" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2564" class="Bound">Bᵉ</a> <a id="2567" class="Symbol">:</a> <a id="2569" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2573" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2550" class="Bound">l2ᵉ</a><a id="2576" class="Symbol">}</a> <a id="2578" class="Symbol">(</a><a id="2579" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2579" class="Bound">fᵉ</a> <a id="2582" class="Symbol">:</a> <a id="2584" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2588" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2546" class="Bound">l1ᵉ</a> <a id="2592" class="Symbol">→</a> <a id="2594" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2564" class="Bound">Bᵉ</a><a id="2596" class="Symbol">)</a> <a id="2598" class="Symbol">{</a><a id="2599" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2599" class="Bound">Xᵉ</a> <a id="2602" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2602" class="Bound">Yᵉ</a> <a id="2605" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2605" class="Bound">Zᵉ</a> <a id="2608" class="Symbol">:</a> <a id="2610" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2614" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2546" class="Bound">l1ᵉ</a><a id="2617" class="Symbol">}</a> <a id="2619" class="Symbol">→</a>
  <a id="2623" class="Symbol">(</a><a id="2624" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2624" class="Bound">eᵉ</a> <a id="2627" class="Symbol">:</a> <a id="2629" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2599" class="Bound">Xᵉ</a> <a id="2632" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="2635" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2602" class="Bound">Yᵉ</a><a id="2637" class="Symbol">)</a> <a id="2639" class="Symbol">(</a><a id="2640" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2640" class="Bound">e&#39;ᵉ</a> <a id="2644" class="Symbol">:</a> <a id="2646" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2602" class="Bound">Yᵉ</a> <a id="2649" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="2652" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2605" class="Bound">Zᵉ</a><a id="2654" class="Symbol">)</a> <a id="2656" class="Symbol">→</a>
  <a id="2660" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="2683" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2579" class="Bound">fᵉ</a> <a id="2686" class="Symbol">(</a><a id="2687" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2640" class="Bound">e&#39;ᵉ</a> <a id="2691" href="foundation-core.equivalences%25E1%25B5%2589.html#14156" class="Function Operator">∘eᵉ</a> <a id="2695" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2624" class="Bound">eᵉ</a><a id="2697" class="Symbol">)</a> <a id="2699" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
  <a id="2704" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="2727" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2579" class="Bound">fᵉ</a> <a id="2730" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2624" class="Bound">eᵉ</a> <a id="2733" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a> <a id="2736" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="2759" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2579" class="Bound">fᵉ</a> <a id="2762" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2640" class="Bound">e&#39;ᵉ</a>
<a id="2766" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2494" class="Function">distributive-action-equiv-function-comp-equivᵉ</a> <a id="2813" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2813" class="Bound">fᵉ</a> <a id="2816" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2816" class="Bound">eᵉ</a> <a id="2819" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2819" class="Bound">e&#39;ᵉ</a> <a id="2823" class="Symbol">=</a>
    <a id="2829" class="Symbol">(</a> <a id="2831" href="foundation.action-on-higher-identifications-functions%25E1%25B5%2589.html#1161" class="Function">ap²ᵉ</a> <a id="2836" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2813" class="Bound">fᵉ</a> <a id="2839" class="Symbol">(</a><a id="2840" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="2845" class="Symbol">(</a><a id="2846" href="foundation.univalence%25E1%25B5%2589.html#6158" class="Function">compute-eq-equiv-comp-equivᵉ</a> <a id="2875" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2816" class="Bound">eᵉ</a> <a id="2878" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2819" class="Bound">e&#39;ᵉ</a><a id="2881" class="Symbol">)))</a> <a id="2885" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
    <a id="2892" class="Symbol">(</a> <a id="2894" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#2088" class="Function">ap-concatᵉ</a> <a id="2905" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2813" class="Bound">fᵉ</a> <a id="2908" class="Symbol">(</a><a id="2909" href="foundation.univalence%25E1%25B5%2589.html#1821" class="Postulate">eq-equivᵉ</a> <a id="2919" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2816" class="Bound">eᵉ</a><a id="2921" class="Symbol">)</a> <a id="2923" class="Symbol">(</a><a id="2924" href="foundation.univalence%25E1%25B5%2589.html#1821" class="Postulate">eq-equivᵉ</a> <a id="2934" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#2819" class="Bound">e&#39;ᵉ</a><a id="2937" class="Symbol">))</a>
</pre>
### The action on equivalences of any map preserves inverses

<pre class="Agda"><a id="compute-action-equiv-function-inv-equivᵉ"></a><a id="3015" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3015" class="Function">compute-action-equiv-function-inv-equivᵉ</a> <a id="3056" class="Symbol">:</a>
  <a id="3060" class="Symbol">{</a><a id="3061" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3061" class="Bound">l1ᵉ</a> <a id="3065" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3065" class="Bound">l2ᵉ</a> <a id="3069" class="Symbol">:</a> <a id="3071" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3076" class="Symbol">}</a> <a id="3078" class="Symbol">{</a><a id="3079" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3079" class="Bound">Bᵉ</a> <a id="3082" class="Symbol">:</a> <a id="3084" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3088" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3065" class="Bound">l2ᵉ</a><a id="3091" class="Symbol">}</a> <a id="3093" class="Symbol">(</a><a id="3094" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3094" class="Bound">fᵉ</a> <a id="3097" class="Symbol">:</a> <a id="3099" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3103" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3061" class="Bound">l1ᵉ</a> <a id="3107" class="Symbol">→</a> <a id="3109" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3079" class="Bound">Bᵉ</a><a id="3111" class="Symbol">)</a> <a id="3113" class="Symbol">{</a><a id="3114" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3114" class="Bound">Xᵉ</a> <a id="3117" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3117" class="Bound">Yᵉ</a> <a id="3120" class="Symbol">:</a> <a id="3122" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3126" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3061" class="Bound">l1ᵉ</a><a id="3129" class="Symbol">}</a>
  <a id="3133" class="Symbol">(</a><a id="3134" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3134" class="Bound">eᵉ</a> <a id="3137" class="Symbol">:</a> <a id="3139" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3114" class="Bound">Xᵉ</a> <a id="3142" href="foundation-core.equivalences%25E1%25B5%2589.html#2662" class="Function Operator">≃ᵉ</a> <a id="3145" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3117" class="Bound">Yᵉ</a><a id="3147" class="Symbol">)</a> <a id="3149" class="Symbol">→</a>
  <a id="3153" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="3176" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3094" class="Bound">fᵉ</a> <a id="3179" class="Symbol">(</a><a id="3180" href="foundation-core.equivalences%25E1%25B5%2589.html#9353" class="Function">inv-equivᵉ</a> <a id="3191" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3134" class="Bound">eᵉ</a><a id="3193" class="Symbol">)</a> <a id="3195" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3198" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="3203" class="Symbol">(</a><a id="3204" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#1730" class="Function">action-equiv-functionᵉ</a> <a id="3227" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3094" class="Bound">fᵉ</a> <a id="3230" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3134" class="Bound">eᵉ</a><a id="3232" class="Symbol">)</a>
<a id="3234" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3015" class="Function">compute-action-equiv-function-inv-equivᵉ</a> <a id="3275" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3275" class="Bound">fᵉ</a> <a id="3278" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3278" class="Bound">eᵉ</a> <a id="3281" class="Symbol">=</a>
  <a id="3285" class="Symbol">(</a> <a id="3287" href="foundation.action-on-higher-identifications-functions%25E1%25B5%2589.html#1161" class="Function">ap²ᵉ</a> <a id="3292" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3275" class="Bound">fᵉ</a> <a id="3295" class="Symbol">(</a><a id="3296" href="foundation-core.identity-types%25E1%25B5%2589.html#6276" class="Function">invᵉ</a> <a id="3301" class="Symbol">(</a><a id="3302" href="foundation.univalence%25E1%25B5%2589.html#7285" class="Function">commutativity-inv-eq-equivᵉ</a> <a id="3330" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3278" class="Bound">eᵉ</a><a id="3332" class="Symbol">)))</a> <a id="3336" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
  <a id="3341" class="Symbol">(</a> <a id="3343" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#2495" class="Function">ap-invᵉ</a> <a id="3351" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3275" class="Bound">fᵉ</a> <a id="3354" class="Symbol">(</a><a id="3355" href="foundation.univalence%25E1%25B5%2589.html#1821" class="Postulate">eq-equivᵉ</a> <a id="3365" href="foundation.action-on-equivalences-functions%25E1%25B5%2589.html#3278" class="Bound">eᵉ</a><a id="3367" class="Symbol">))</a>
</pre>