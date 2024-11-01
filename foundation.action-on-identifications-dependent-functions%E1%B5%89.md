# The action on identifications of dependent functions

<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-dependent-functionsᵉ</a> <a id="130" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="186" class="Keyword">open</a> <a id="191" class="Keyword">import</a> <a id="198" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation-core.dependent-identifications%25E1%25B5%2589.html" class="Module">foundation-core.dependent-identificationsᵉ</a>
<a id="282" class="Keyword">open</a> <a id="287" class="Keyword">import</a> <a id="294" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
</pre>
</details>

## Idea

Given a dependent function `f : (x : A) → B x` and an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`, we
cannot directly compare the values `f x` and `f y`, since `f x` is an element of
type `B x` while `f y` is an element of type `B y`. However, we can
[transport](foundation-core.transport-along-identifications.md) the value `f x`
along `p` to obtain an element of type `B y` that is comparable to the value
`f y`. In other words, we can consider the type of
[dependent identifications](foundation-core.dependent-identifications.md) over
`p` from `f x` to `f y`. The **dependent action on identifications** of `f` on
`p` is a dependent identification

```text
  apd f p : dependent-identification B p (f x) (f y).
```

## Definition

### Functorial action of dependent functions on identity types

<pre class="Agda"><a id="apdᵉ"></a><a id="1185" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1185" class="Function">apdᵉ</a> <a id="1190" class="Symbol">:</a>
  <a id="1194" class="Symbol">{</a><a id="1195" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1195" class="Bound">l1ᵉ</a> <a id="1199" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1199" class="Bound">l2ᵉ</a> <a id="1203" class="Symbol">:</a> <a id="1205" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1210" class="Symbol">}</a> <a id="1212" class="Symbol">{</a><a id="1213" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1213" class="Bound">Aᵉ</a> <a id="1216" class="Symbol">:</a> <a id="1218" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1222" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1195" class="Bound">l1ᵉ</a><a id="1225" class="Symbol">}</a> <a id="1227" class="Symbol">{</a><a id="1228" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1228" class="Bound">Bᵉ</a> <a id="1231" class="Symbol">:</a> <a id="1233" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1213" class="Bound">Aᵉ</a> <a id="1236" class="Symbol">→</a> <a id="1238" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1242" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1199" class="Bound">l2ᵉ</a><a id="1245" class="Symbol">}</a> <a id="1247" class="Symbol">(</a><a id="1248" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1248" class="Bound">fᵉ</a> <a id="1251" class="Symbol">:</a> <a id="1253" class="Symbol">(</a><a id="1254" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1254" class="Bound">xᵉ</a> <a id="1257" class="Symbol">:</a> <a id="1259" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1213" class="Bound">Aᵉ</a><a id="1261" class="Symbol">)</a> <a id="1263" class="Symbol">→</a> <a id="1265" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1228" class="Bound">Bᵉ</a> <a id="1268" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1254" class="Bound">xᵉ</a><a id="1270" class="Symbol">)</a> <a id="1272" class="Symbol">{</a><a id="1273" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1273" class="Bound">xᵉ</a> <a id="1276" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1276" class="Bound">yᵉ</a> <a id="1279" class="Symbol">:</a> <a id="1281" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1213" class="Bound">Aᵉ</a><a id="1283" class="Symbol">}</a>
  <a id="1287" class="Symbol">(</a><a id="1288" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1288" class="Bound">pᵉ</a> <a id="1291" class="Symbol">:</a> <a id="1293" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1273" class="Bound">xᵉ</a> <a id="1296" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="1299" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1276" class="Bound">yᵉ</a><a id="1301" class="Symbol">)</a> <a id="1303" class="Symbol">→</a> <a id="1305" href="foundation-core.dependent-identifications%25E1%25B5%2589.html#968" class="Function">dependent-identificationᵉ</a> <a id="1331" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1228" class="Bound">Bᵉ</a> <a id="1334" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1288" class="Bound">pᵉ</a> <a id="1337" class="Symbol">(</a><a id="1338" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1248" class="Bound">fᵉ</a> <a id="1341" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1273" class="Bound">xᵉ</a><a id="1343" class="Symbol">)</a> <a id="1345" class="Symbol">(</a><a id="1346" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1248" class="Bound">fᵉ</a> <a id="1349" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1276" class="Bound">yᵉ</a><a id="1351" class="Symbol">)</a>
<a id="1353" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1185" class="Function">apdᵉ</a> <a id="1358" href="foundation.action-on-identifications-dependent-functions%25E1%25B5%2589.html#1358" class="Bound">fᵉ</a> <a id="1361" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a> <a id="1367" class="Symbol">=</a> <a id="1369" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
</pre>
## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).