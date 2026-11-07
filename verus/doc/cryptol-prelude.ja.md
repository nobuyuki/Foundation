# Verus での Cryptol の prelude

[English](cryptol-prelude.md) | 日本語

spec 層が使う Cryptol の組み込み（`foldl`・`@`・`join`・`split`・`pmult` など）を、Verus の spec 関数と lemma として一度だけ書いたもの。
SPARK の crate の `spark/doc/cryptol-prelude.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じである。[README](../README.ja.md) へ戻る。

## Cryptol の prelude

`src/cryptol/`（`foundation_verus::cryptol`）は、spec 層が使う Cryptol の組み込みを、Cryptol の名前で一度だけ書く。
spec のモジュールは、Cryptol が組み込みを呼ぶところでこれを呼ぶ。
そのためレビューする人は Cryptol から Verus への翻訳をここで一度だけ確かめればよく、spec の本体にはアルゴリズムだけが残る。
関数はすべて `spec fn`（lemma は `proof fn`）である。Cryptol が幅について多相なところでは、ワードの型について generic にしてある。
trait [`Word`](../src/cryptol/mod.rs) は `u8`・`u16`・`u32` に実装してあり、SPARK の crate の generic formal `type Word is mod <>` に当たる。

| モジュール | Cryptol | 拠りどころ |
|---|---|---|
| [`folds`](../src/cryptol/folds.rs)（`foldl`、`foldl_take`） | `foldl f z xs`、``foldl f z (take`{N} xs)`` | Cryptol.cry:1146（primitive）とその例 `((0 + 1) + 2) + 3` |
| [`enumeration_folds`](../src/cryptol/enumeration_folds.rs)（`foldl`） | `foldl f z [from ..< to]` | 同上、と RefMan BasicTypes.rst:169 |
| [`words`](../src/cryptol/words.rs)（`bit`、`bit_in`、`head`） | ワード `[w]` の `x @ j`、`head x` | Cryptol.cry:900（primitive）、:796（ビットの順）、:855（head の本体） |
| [`join_split`](../src/cryptol/join_split.rs)（`join`、`split_at`、`value`） | `[n][w]` と `[n * w]` の間の `join`、`split` | Cryptol.cry:815 と :822（primitive、互いに逆と書かれている） |
| [`bit_sequences`](../src/cryptol/bit_sequences.rs)（`zero`、`literal`、`xor`） | `zero : [n]`、`` `v : [n] ``、`[n]` の `^` | Cryptol.cry:304（primitive）、RefMan BasicSyntax.rst:349 |
| [`sequences`](../src/cryptol/sequences.rs)（`reverse`、`repeat`） | `reverse`、`repeat` | Cryptol.cry:828（primitive）、:1215（repeat の本体） |
| [`bulk_indexing`](../src/cryptol/bulk_indexing.rs)（`bulk_index`） | `xs @@ is` | Cryptol.cry:906（その本体） |
| [`numeric`](../src/cryptol/numeric.rs)（`ceil_div`、`ceil_mod`） | 型の演算子 `/^`、`%^` | Cryptol.cry:135 と :141（primitive） |
| [`polynomial_products`](../src/cryptol/polynomial_products.rs)（`pmult`） | `pmult` | Cryptol.cry:1005（primitive）、RefMan BasicSyntax.rst:352 |
| [`polynomial_remainders`](../src/cryptol/polynomial_remainders.rs)（`pmod`） | `pmod` | Cryptol.cry:1015（primitive） |
| [`polynomial_quotients`](../src/cryptol/polynomial_quotients.rs)（`pdiv`） | `pdiv` | Cryptol.cry:1010（primitive） |

行番号は Cryptol 3.6.0 の `lib/Cryptol.cry` のもので、SPARK の crate の表と同じである（行も SPARK 版の表のものに対応する）。
レビューする人が知っておくべき選択:

- **fold は最後の要素から再帰する。** SPARK の prelude と同じである:
  ``foldl f z (take`{N} xs) = f (foldl f z (take`{N - 1} xs)) (xs @ (N - 1))``。
  これは実装のループの形である。N ステップ後のループ不変条件は最初の N 個の fold なので、1 ステップがそのまま定義になる。
- **クロージャはクロージャのまま**（SPARK の crate との違い）。
  Cryptol の fold の関数は、局所的な値に触れることがある（SHA-2 の `step3` はブロックに触れる）。
  Ada の generic formal の関数はクロージャではないので、SPARK の prelude はその値を明示的な第 1 引数として渡す。
  Verus には `spec_fn` のクロージャがあるので、ここでは Cryptol と同じく関数をクロージャにする。
- **ワードは数**（SPARK の crate と同じ）。
  `[w]` は Rust の符号なし整数（`Word` trait）で、ワードのビット `j` の重みは `2 ^^ (w - 1 - j)` である。
  `join_split::value` は、Cryptol では名前の要らないビットからワードへの変換である。
  多項式のモジュールもワードを同じように多項式として読む。重み `2 ^^ i` のビットが `x ^^ i` の係数である。
- **長さと添字は `int` と `nat`**（違い）。
  上限がないので、SPARK の crate の 128 ビットの `Bit_Index` とその範囲に当たるものはない。
- **型パラメータ。**
  Cryptol の数の型パラメータ `{u, v}` は、Rust で書けるところでは const generics にする。
  Cryptol がそれらを使った式（`1 + v`）を書くところでは `nat` の引数にする。Rust の const generics は計算できないからである。
  `remainders` と `quotients` は `v` を取らない。SPARK の crate はここで `pdiv` を `V - 1` で具体化している。

**使うところ。**
SHA-2（ブロックとラウンドの上の `foldl`、`@`、`join`、`split`、`zero`、`pad` のリテラル、`/^` と `%^`）、
HMAC（`repeat`、`zero`、`^`、バイトの `join`）、
AES（ラウンドの fold と GF28MultiplicationCorrect の `foldl`、`@@`、バイトとビットの間の `join` と `split`、ワードの `@` と `head`、`pmult`、`pmod`、`pdiv`、`reverse`）。

SPARK の crate には、何を prelude に移し、何を書き下したまま残したかの説明があり、それぞれに測った理由がついている（prover のステップを増やしたラッパー、`Byte` を返す `pmod`、遅い `SBox_Entries` での `[9] x [9]` の `pmult`、`pdiv` の最高次の項、`Types.Split`）。
ここでは書き下したまま残したものがないので省略する。GF28 の `pmod` も、GF2 の `pmult` と `pdiv` も prelude のものである。
種類の違う例外が 1 つだけあり、`SBoxCorrect`（[proving.ja.md](proving.ja.md#cryptol-自身の性質の証明し直し)）である。これは、これらの関数の trait を使わない写しを評価する。写しは prelude のものと等しいと証明してある。

**確かめ方。**
prelude についての lemma（spec 層が使う性質）は、ほかと一緒に Verus が証明する。
SPARK の crate はさらに、各 generic を FFI で Cryptol の組み込みと突き合わせ（`spark/cryptol/SPARK/Prelude.cry`、22 個の性質）、spec 層が呼ぶ各具体化を SAW で証明している。
ここではどちらも省略する。Verus の spec 関数は実行もコンパイルもできないからである（FFI での突き合わせと SAW が届くのは実行可能なコードだけ: [ffi.ja.md](ffi.ja.md)、[saw.ja.md](saw.ja.md#spec-層)）。
prelude を Cryptol と比べるのは、prelude で書いた spec 関数と等しいと証明した実行可能な関数を通してだけである。
