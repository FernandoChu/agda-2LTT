# Commuting triangles of morphisms of arrows

<pre class="Agda"><a id="55" class="Keyword">module</a> <a id="62" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html" class="Module">foundation.commuting-triangles-of-morphisms-arrowsᵉ</a> <a id="114" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="170" class="Keyword">open</a> <a id="175" class="Keyword">import</a> <a id="182" href="foundation.homotopies-morphisms-arrows%25E1%25B5%2589.html" class="Module">foundation.homotopies-morphisms-arrowsᵉ</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="foundation.morphisms-arrows%25E1%25B5%2589.html" class="Module">foundation.morphisms-arrowsᵉ</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>
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

<pre class="Agda"><a id="1190" class="Keyword">module</a> <a id="1197" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1197" class="Module">_</a>
  <a id="1201" class="Symbol">{</a><a id="1202" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1202" class="Bound">l1ᵉ</a> <a id="1206" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1206" class="Bound">l2ᵉ</a> <a id="1210" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1210" class="Bound">l3ᵉ</a> <a id="1214" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1214" class="Bound">l4ᵉ</a> <a id="1218" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1218" class="Bound">l5ᵉ</a> <a id="1222" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1222" class="Bound">l6ᵉ</a> <a id="1226" class="Symbol">:</a> <a id="1228" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1233" class="Symbol">}</a>
  <a id="1237" class="Symbol">{</a><a id="1238" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1238" class="Bound">Aᵉ</a> <a id="1241" class="Symbol">:</a> <a id="1243" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1247" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1202" class="Bound">l1ᵉ</a><a id="1250" class="Symbol">}</a> <a id="1252" class="Symbol">{</a><a id="1253" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1253" class="Bound">A&#39;ᵉ</a> <a id="1257" class="Symbol">:</a> <a id="1259" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1263" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1206" class="Bound">l2ᵉ</a><a id="1266" class="Symbol">}</a> <a id="1268" class="Symbol">{</a><a id="1269" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1269" class="Bound">Bᵉ</a> <a id="1272" class="Symbol">:</a> <a id="1274" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1278" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1210" class="Bound">l3ᵉ</a><a id="1281" class="Symbol">}</a> <a id="1283" class="Symbol">{</a><a id="1284" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1284" class="Bound">B&#39;ᵉ</a> <a id="1288" class="Symbol">:</a> <a id="1290" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1294" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1214" class="Bound">l4ᵉ</a><a id="1297" class="Symbol">}</a> <a id="1299" class="Symbol">{</a><a id="1300" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1300" class="Bound">Cᵉ</a> <a id="1303" class="Symbol">:</a> <a id="1305" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1309" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1218" class="Bound">l5ᵉ</a><a id="1312" class="Symbol">}</a> <a id="1314" class="Symbol">{</a><a id="1315" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1315" class="Bound">C&#39;ᵉ</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1325" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1222" class="Bound">l6ᵉ</a><a id="1328" class="Symbol">}</a>
  <a id="1332" class="Symbol">(</a><a id="1333" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1336" class="Symbol">:</a> <a id="1338" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1238" class="Bound">Aᵉ</a> <a id="1341" class="Symbol">→</a> <a id="1343" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1253" class="Bound">A&#39;ᵉ</a><a id="1346" class="Symbol">)</a> <a id="1348" class="Symbol">(</a><a id="1349" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1349" class="Bound">gᵉ</a> <a id="1352" class="Symbol">:</a> <a id="1354" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1269" class="Bound">Bᵉ</a> <a id="1357" class="Symbol">→</a> <a id="1359" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1284" class="Bound">B&#39;ᵉ</a><a id="1362" class="Symbol">)</a> <a id="1364" class="Symbol">(</a><a id="1365" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a> <a id="1368" class="Symbol">:</a> <a id="1370" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1300" class="Bound">Cᵉ</a> <a id="1373" class="Symbol">→</a> <a id="1375" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1315" class="Bound">C&#39;ᵉ</a><a id="1378" class="Symbol">)</a>
  <a id="1382" class="Symbol">(</a><a id="1383" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1383" class="Bound">leftᵉ</a> <a id="1389" class="Symbol">:</a> <a id="1391" href="foundation.morphisms-arrows%25E1%25B5%2589.html#1699" class="Function">hom-arrowᵉ</a> <a id="1402" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1405" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a><a id="1407" class="Symbol">)</a> <a id="1409" class="Symbol">(</a><a id="1410" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1410" class="Bound">rightᵉ</a> <a id="1417" class="Symbol">:</a> <a id="1419" href="foundation.morphisms-arrows%25E1%25B5%2589.html#1699" class="Function">hom-arrowᵉ</a> <a id="1430" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1349" class="Bound">gᵉ</a> <a id="1433" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a><a id="1435" class="Symbol">)</a> <a id="1437" class="Symbol">(</a><a id="1438" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1438" class="Bound">topᵉ</a> <a id="1443" class="Symbol">:</a> <a id="1445" href="foundation.morphisms-arrows%25E1%25B5%2589.html#1699" class="Function">hom-arrowᵉ</a> <a id="1456" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1459" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1349" class="Bound">gᵉ</a><a id="1461" class="Symbol">)</a>
  <a id="1465" class="Keyword">where</a>

  <a id="1474" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1474" class="Function">coherence-triangle-hom-arrowᵉ</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1510" class="Symbol">(</a><a id="1511" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1202" class="Bound">l1ᵉ</a> <a id="1515" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1517" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1206" class="Bound">l2ᵉ</a> <a id="1521" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1523" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1218" class="Bound">l5ᵉ</a> <a id="1527" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1529" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1222" class="Bound">l6ᵉ</a><a id="1532" class="Symbol">)</a>
  <a id="1536" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1474" class="Function">coherence-triangle-hom-arrowᵉ</a> <a id="1566" class="Symbol">=</a>
    <a id="1572" href="foundation.homotopies-morphisms-arrows%25E1%25B5%2589.html#2816" class="Function">htpy-hom-arrowᵉ</a> <a id="1588" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1591" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a> <a id="1594" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1383" class="Bound">leftᵉ</a> <a id="1600" class="Symbol">(</a><a id="1601" href="foundation.morphisms-arrows%25E1%25B5%2589.html#4402" class="Function">comp-hom-arrowᵉ</a> <a id="1617" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1620" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1349" class="Bound">gᵉ</a> <a id="1623" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a> <a id="1626" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1410" class="Bound">rightᵉ</a> <a id="1633" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1438" class="Bound">topᵉ</a><a id="1637" class="Symbol">)</a>

  <a id="1642" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1642" class="Function">coherence-triangle-hom-arrow&#39;ᵉ</a> <a id="1673" class="Symbol">:</a> <a id="1675" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1679" class="Symbol">(</a><a id="1680" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1202" class="Bound">l1ᵉ</a> <a id="1684" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1686" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1206" class="Bound">l2ᵉ</a> <a id="1690" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1692" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1218" class="Bound">l5ᵉ</a> <a id="1696" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1698" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1222" class="Bound">l6ᵉ</a><a id="1701" class="Symbol">)</a>
  <a id="1705" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1642" class="Function">coherence-triangle-hom-arrow&#39;ᵉ</a> <a id="1736" class="Symbol">=</a>
    <a id="1742" href="foundation.homotopies-morphisms-arrows%25E1%25B5%2589.html#2816" class="Function">htpy-hom-arrowᵉ</a> <a id="1758" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1761" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a> <a id="1764" class="Symbol">(</a><a id="1765" href="foundation.morphisms-arrows%25E1%25B5%2589.html#4402" class="Function">comp-hom-arrowᵉ</a> <a id="1781" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1333" class="Bound">fᵉ</a> <a id="1784" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1349" class="Bound">gᵉ</a> <a id="1787" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1365" class="Bound">hᵉ</a> <a id="1790" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1410" class="Bound">rightᵉ</a> <a id="1797" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1438" class="Bound">topᵉ</a><a id="1801" class="Symbol">)</a> <a id="1803" href="foundation.commuting-triangles-of-morphisms-arrows%25E1%25B5%2589.html#1383" class="Bound">leftᵉ</a>
</pre>