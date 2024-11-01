# Commuting triangles of morphisms of arrows

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="foundation.commuting-triangles-of-morphisms-arrows.html" class="Module">foundation.commuting-triangles-of-morphisms-arrows</a> <a id="113" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.homotopies-morphisms-arrows.html" class="Module">foundation.homotopies-morphisms-arrows</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="foundation.morphisms-arrows.html" class="Module">foundation.morphisms-arrows</a>
<a id="260" class="Keyword">open</a> <a id="265" class="Keyword">import</a> <a id="272" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a triangle of [morphisms of arrows](foundation.morphisms-arrows.md)

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

then we can ask that the triangle
{{#concept "commutes" Disambiguation="triangle of morphisms of arrows"}}

by asking for a [homotopy](foundation.homotopies-morphisms-arrows.md) of
morphisms of arrows

```text
  left ~ right ∘ top.
```

This is [equivalent](foundation-core.equivalences.md) to asking for a
[commuting prism of maps](foundation-core.commuting-prisms-of-maps.md), given
the square faces in the diagram

```text
        f
  ∙ ---------> ∙
  |\           |\
  | \          | \
  |  \         |  \
  |   ∨        |   ∨
  |    ∙ --- g ---> ∙
  |   /        |   /
  |  /         |  /
  | /          | /
  ∨∨           ∨∨
  ∙ ---------> ∙.
        h
```

## Definition

<pre class="Agda"><a id="1186" class="Keyword">module</a> <a id="1193" href="foundation.commuting-triangles-of-morphisms-arrows.html#1193" class="Module">_</a>
  <a id="1197" class="Symbol">{</a><a id="1198" href="foundation.commuting-triangles-of-morphisms-arrows.html#1198" class="Bound">l1</a> <a id="1201" href="foundation.commuting-triangles-of-morphisms-arrows.html#1201" class="Bound">l2</a> <a id="1204" href="foundation.commuting-triangles-of-morphisms-arrows.html#1204" class="Bound">l3</a> <a id="1207" href="foundation.commuting-triangles-of-morphisms-arrows.html#1207" class="Bound">l4</a> <a id="1210" href="foundation.commuting-triangles-of-morphisms-arrows.html#1210" class="Bound">l5</a> <a id="1213" href="foundation.commuting-triangles-of-morphisms-arrows.html#1213" class="Bound">l6</a> <a id="1216" class="Symbol">:</a> <a id="1218" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1223" class="Symbol">}</a>
  <a id="1227" class="Symbol">{</a><a id="1228" href="foundation.commuting-triangles-of-morphisms-arrows.html#1228" class="Bound">A</a> <a id="1230" class="Symbol">:</a> <a id="1232" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1235" href="foundation.commuting-triangles-of-morphisms-arrows.html#1198" class="Bound">l1</a><a id="1237" class="Symbol">}</a> <a id="1239" class="Symbol">{</a><a id="1240" href="foundation.commuting-triangles-of-morphisms-arrows.html#1240" class="Bound">A&#39;</a> <a id="1243" class="Symbol">:</a> <a id="1245" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1248" href="foundation.commuting-triangles-of-morphisms-arrows.html#1201" class="Bound">l2</a><a id="1250" class="Symbol">}</a> <a id="1252" class="Symbol">{</a><a id="1253" href="foundation.commuting-triangles-of-morphisms-arrows.html#1253" class="Bound">B</a> <a id="1255" class="Symbol">:</a> <a id="1257" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1260" href="foundation.commuting-triangles-of-morphisms-arrows.html#1204" class="Bound">l3</a><a id="1262" class="Symbol">}</a> <a id="1264" class="Symbol">{</a><a id="1265" href="foundation.commuting-triangles-of-morphisms-arrows.html#1265" class="Bound">B&#39;</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1273" href="foundation.commuting-triangles-of-morphisms-arrows.html#1207" class="Bound">l4</a><a id="1275" class="Symbol">}</a> <a id="1277" class="Symbol">{</a><a id="1278" href="foundation.commuting-triangles-of-morphisms-arrows.html#1278" class="Bound">C</a> <a id="1280" class="Symbol">:</a> <a id="1282" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1285" href="foundation.commuting-triangles-of-morphisms-arrows.html#1210" class="Bound">l5</a><a id="1287" class="Symbol">}</a> <a id="1289" class="Symbol">{</a><a id="1290" href="foundation.commuting-triangles-of-morphisms-arrows.html#1290" class="Bound">C&#39;</a> <a id="1293" class="Symbol">:</a> <a id="1295" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1298" href="foundation.commuting-triangles-of-morphisms-arrows.html#1213" class="Bound">l6</a><a id="1300" class="Symbol">}</a>
  <a id="1304" class="Symbol">(</a><a id="1305" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1307" class="Symbol">:</a> <a id="1309" href="foundation.commuting-triangles-of-morphisms-arrows.html#1228" class="Bound">A</a> <a id="1311" class="Symbol">→</a> <a id="1313" href="foundation.commuting-triangles-of-morphisms-arrows.html#1240" class="Bound">A&#39;</a><a id="1315" class="Symbol">)</a> <a id="1317" class="Symbol">(</a><a id="1318" href="foundation.commuting-triangles-of-morphisms-arrows.html#1318" class="Bound">g</a> <a id="1320" class="Symbol">:</a> <a id="1322" href="foundation.commuting-triangles-of-morphisms-arrows.html#1253" class="Bound">B</a> <a id="1324" class="Symbol">→</a> <a id="1326" href="foundation.commuting-triangles-of-morphisms-arrows.html#1265" class="Bound">B&#39;</a><a id="1328" class="Symbol">)</a> <a id="1330" class="Symbol">(</a><a id="1331" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a> <a id="1333" class="Symbol">:</a> <a id="1335" href="foundation.commuting-triangles-of-morphisms-arrows.html#1278" class="Bound">C</a> <a id="1337" class="Symbol">→</a> <a id="1339" href="foundation.commuting-triangles-of-morphisms-arrows.html#1290" class="Bound">C&#39;</a><a id="1341" class="Symbol">)</a>
  <a id="1345" class="Symbol">(</a><a id="1346" href="foundation.commuting-triangles-of-morphisms-arrows.html#1346" class="Bound">left</a> <a id="1351" class="Symbol">:</a> <a id="1353" href="foundation.morphisms-arrows.html#1649" class="Function">hom-arrow</a> <a id="1363" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1365" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a><a id="1366" class="Symbol">)</a> <a id="1368" class="Symbol">(</a><a id="1369" href="foundation.commuting-triangles-of-morphisms-arrows.html#1369" class="Bound">right</a> <a id="1375" class="Symbol">:</a> <a id="1377" href="foundation.morphisms-arrows.html#1649" class="Function">hom-arrow</a> <a id="1387" href="foundation.commuting-triangles-of-morphisms-arrows.html#1318" class="Bound">g</a> <a id="1389" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a><a id="1390" class="Symbol">)</a> <a id="1392" class="Symbol">(</a><a id="1393" href="foundation.commuting-triangles-of-morphisms-arrows.html#1393" class="Bound">top</a> <a id="1397" class="Symbol">:</a> <a id="1399" href="foundation.morphisms-arrows.html#1649" class="Function">hom-arrow</a> <a id="1409" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1411" href="foundation.commuting-triangles-of-morphisms-arrows.html#1318" class="Bound">g</a><a id="1412" class="Symbol">)</a>
  <a id="1416" class="Keyword">where</a>

  <a id="1425" href="foundation.commuting-triangles-of-morphisms-arrows.html#1425" class="Function">coherence-triangle-hom-arrow</a> <a id="1454" class="Symbol">:</a> <a id="1456" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1459" class="Symbol">(</a><a id="1460" href="foundation.commuting-triangles-of-morphisms-arrows.html#1198" class="Bound">l1</a> <a id="1463" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1465" href="foundation.commuting-triangles-of-morphisms-arrows.html#1201" class="Bound">l2</a> <a id="1468" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1470" href="foundation.commuting-triangles-of-morphisms-arrows.html#1210" class="Bound">l5</a> <a id="1473" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1475" href="foundation.commuting-triangles-of-morphisms-arrows.html#1213" class="Bound">l6</a><a id="1477" class="Symbol">)</a>
  <a id="1481" href="foundation.commuting-triangles-of-morphisms-arrows.html#1425" class="Function">coherence-triangle-hom-arrow</a> <a id="1510" class="Symbol">=</a>
    <a id="1516" href="foundation.homotopies-morphisms-arrows.html#2720" class="Function">htpy-hom-arrow</a> <a id="1531" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1533" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a> <a id="1535" href="foundation.commuting-triangles-of-morphisms-arrows.html#1346" class="Bound">left</a> <a id="1540" class="Symbol">(</a><a id="1541" href="foundation.morphisms-arrows.html#4187" class="Function">comp-hom-arrow</a> <a id="1556" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1558" href="foundation.commuting-triangles-of-morphisms-arrows.html#1318" class="Bound">g</a> <a id="1560" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a> <a id="1562" href="foundation.commuting-triangles-of-morphisms-arrows.html#1369" class="Bound">right</a> <a id="1568" href="foundation.commuting-triangles-of-morphisms-arrows.html#1393" class="Bound">top</a><a id="1571" class="Symbol">)</a>

  <a id="1576" href="foundation.commuting-triangles-of-morphisms-arrows.html#1576" class="Function">coherence-triangle-hom-arrow&#39;</a> <a id="1606" class="Symbol">:</a> <a id="1608" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1611" class="Symbol">(</a><a id="1612" href="foundation.commuting-triangles-of-morphisms-arrows.html#1198" class="Bound">l1</a> <a id="1615" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1617" href="foundation.commuting-triangles-of-morphisms-arrows.html#1201" class="Bound">l2</a> <a id="1620" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1622" href="foundation.commuting-triangles-of-morphisms-arrows.html#1210" class="Bound">l5</a> <a id="1625" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1627" href="foundation.commuting-triangles-of-morphisms-arrows.html#1213" class="Bound">l6</a><a id="1629" class="Symbol">)</a>
  <a id="1633" href="foundation.commuting-triangles-of-morphisms-arrows.html#1576" class="Function">coherence-triangle-hom-arrow&#39;</a> <a id="1663" class="Symbol">=</a>
    <a id="1669" href="foundation.homotopies-morphisms-arrows.html#2720" class="Function">htpy-hom-arrow</a> <a id="1684" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1686" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a> <a id="1688" class="Symbol">(</a><a id="1689" href="foundation.morphisms-arrows.html#4187" class="Function">comp-hom-arrow</a> <a id="1704" href="foundation.commuting-triangles-of-morphisms-arrows.html#1305" class="Bound">f</a> <a id="1706" href="foundation.commuting-triangles-of-morphisms-arrows.html#1318" class="Bound">g</a> <a id="1708" href="foundation.commuting-triangles-of-morphisms-arrows.html#1331" class="Bound">h</a> <a id="1710" href="foundation.commuting-triangles-of-morphisms-arrows.html#1369" class="Bound">right</a> <a id="1716" href="foundation.commuting-triangles-of-morphisms-arrows.html#1393" class="Bound">top</a><a id="1719" class="Symbol">)</a> <a id="1721" href="foundation.commuting-triangles-of-morphisms-arrows.html#1346" class="Bound">left</a>
</pre>