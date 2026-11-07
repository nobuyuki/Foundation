# AES・SHA-256・HMAC-SHA-256 の Verus 実装

[English](README.md) | 日本語

このディレクトリは Cargo の crate `foundation_verus` である。
[`../algorithms`](../algorithms) にある NSA の Cryptol 仕様のうち 3 つのアルゴリズムを Rust で実装し、Verus で証明している:

* **AES**（FIPS 197）: 鍵拡張・暗号化・復号。鍵長は 128・192・256 ビット。
* **SHA-256**（FIPS 180-4）: 一括とストリーミング。
* **HMAC-SHA-256**（FIPS 198-1）: 一括と逐次。

[`../spark`](../spark) にある SPARK の crate `foundation_spark`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`。このリポジトリはその上に作られている）を、Rust と Verus で部品ごとに写したものである。
各実装は、NSA の Cryptol を Verus に書き写したものと等しいことを Verus で証明している。
さらに実装を Cryptol そのものと突き合わせる。Cryptol の外部関数インターフェース（FFI）を通したテストと、SAW による証明である。

## 部品のつながり

```text
  NSA の Cryptol（algorithms/AES, SHA2, HMAC）
        ^                          ^
        |                          |
        |                          |
  spec 層: Verus の spec fn。Cryptol を宣言ごとに写す
        ^                          |
        | Verus、全入力で          |
        |                          | FFI での突き合わせ（テスト）と、
  実装層: Rust                     | 固定サイズでの SAW
  （ensures: 「結果は spec の      | （LLVM bitcode と MIR の上で）:
   値」） -------------------------+ 実装 = Cryptol
```

* **spec 層**は、Verus で許されるかぎり Cryptol に寄せて写している。
  名前も型も同じ（Cryptol のビット列は `Seq<bool>`、ワードは Rust の整数）で、再帰や fold の形も同じである。
  `spec fn` なので、証明の対象にはなるがコンパイルはされない。
  spec 層が使う Cryptol の組み込み（`foldl`・`@`・`join`・`split` など）は、[`src/cryptol/`](src/cryptol) に一度だけ書いてある（[doc/cryptol-prelude.ja.md](doc/cryptol-prelude.ja.md)）。
* **実装層**は、実行するために書いた普通の Rust である。
  各関数の `ensures` が「結果は spec 層の値である」と述べる。
  両者の間には、lemma（`proof fn`）と表現の層（バイトとビット、ストリーミングと一括）がある。
* **Verus** は、実装が spec 層と等しいことを全入力について証明する。
  あわせて、実行時エラー（オーバーフロー、範囲外の添字など）がどこにもないことも証明する。
* **FFI での突き合わせ**では、実行できる関数を Cryptol から呼び、NSA の Cryptol と比べる。
  入力空間が小さければ全数で、そうでなければランダムな入力と既知解の入力で比べる。
* **SAW** は、実装をコンパイルしたコードが NSA の Cryptol と等しいことを、Verus の spec を間に挟まずに証明する。
  鍵長とメッセージ長は固定で、経路は rustc の LLVM bitcode と MIR の 2 つである。

SPARK の crate との違い: SPARK 版の spec 層はコンパイルできる ghost コードなので、FFI での突き合わせと SAW で spec 層も Cryptol と比べている。
Verus の spec 関数はコンパイルされない。
そのためここでは、spec 層を Cryptol と比べるのは、spec 層と等しいと証明した実行可能な関数を通してだけである（[doc/ffi.ja.md](doc/ffi.ja.md)）。

ウォークスルーでは、実際のコードで Cryptol と Verus を並べ、この連鎖をたどる:

* [AES](doc/walkthroughs/aes.ja.md)
* [SHA-256](doc/walkthroughs/sha-256.ja.md)
* [HMAC-SHA-256](doc/walkthroughs/hmac-sha-256.ja.md)

## 証明したこと

* **Verus が調べる関数はすべて検証が通る**: 326 verified、0 errors（`cargo verus verify`、`d59a3f0` で）。16 CPU のデスクトップで約 14 秒。
  Verus のリソース上限を上げた関数はなく、遅い証明もない（[doc/proving.ja.md](doc/proving.ja.md)）。
* **何も仮定していない。** `assume`・`admit`・`axiom fn`・`external_body`・`#[verifier::external]`・停止性の免除は 1 つもない。
  Verus が見ないコードは `src/ffi/` の FFI エクスポートだけである。これはテストのために実行可能な関数を Cryptol へ出すもので、1 つずつ理由をつけて [`scripts/trust-surface.txt`](scripts/trust-surface.txt) に載せてある（100 件）。
  これを `scripts/check-trust-surface.sh` が検査する。SPARK の crate の同名のスクリプトと同じである。
* **実装は全入力で spec 層と等しい。**
  2^61 バイト未満のすべてのメッセージ長（HMAC では `Max_Text` より短いすべてのテキスト）を含む。
  ストリーミングの SHA-256 と HMAC では、メッセージをチャンクに分けるすべての分け方も含む。
* **AES について Cryptol 自身が述べる性質**（`algorithms/AES` が述べる 15 個のうち、SPARK の crate と同じ 13 個）を spec 層について証明した。すべての鍵長について一度で済ませている。
* **SAW**: 各経路（LLVM bitcode と MIR）で 84 件（AES 46 件、SHA-256 と HMAC で 38 件）。
  各経路で陰性対照 8 件が、失敗すべきとおりに失敗する（`saw/results.txt`、`d59a3f0` で）。
  AES は k = 128・192・256。SHA-256 の圧縮関数は全入力。
  ハッシュは 12 通りの長さ、HMAC は 7 通りの（鍵、テキスト）の組で、パディングの境目を選んだ。
  詳細と、SAW が扱わない部分: [doc/saw.ja.md](doc/saw.ja.md)。

証明して**いない**こと:

* spec 層が Cryptol と等しいこと。
  これは、丁寧に読むこと、証明し直した性質（AES）、そして spec 層と等しいと証明した実行可能な関数への FFI での突き合わせと SAW に拠っている。
  SAW は AES のすべてのサイズと SHA-256 の圧縮関数を扱うが、ハッシュと HMAC は SAW を回した長さだけである。
* コンパイラが正しいこと。Verus は Rust のソースについて推論し、SAW は rustc 1.98.1 と mir-json が出す bitcode と MIR について推論する。
* Verus 自身、vstd、SMT ソルバー。
* 実行時間。この AES は定数時間ではない。S-box は、鍵と状態のバイトを添字にした表引きである。

## テストしたこと

* **FFI での突き合わせ**: 73 個の性質（[`cryptol/properties.txt`](cryptol/properties.txt)）。
  SPARK の crate の性質のうち、実行可能な関数に対するものである（残りの 68 個は spec 関数をテストするもので、ここでは実行できない）。
  crate の関数を NSA の Cryptol と、Cryptol の `:exhaust` か `:check` で比べる。
  加えて FIPS 197・FIPS 180-4・RFC 4231 の既知解ベクトルを使う。[doc/ffi.ja.md](doc/ffi.ja.md)。
* **カバレッジ**: それらの性質のもとでの実行可能なコードのカバレッジを、region・行・分岐の結果ごとに測った。
  SPARK の crate が測っている **MC/DC はない**。rustc に MC/DC の計装がないためである。
  実装層は全部を通っている（region 947/947、分岐 80/80）。
  残る 11 の穴は FFI エクスポートの検査で、Cryptol の型が保証することを確かめている部分である。理由は [`coverage/explained.txt`](coverage/explained.txt) に書いた。
  [doc/coverage.ja.md](doc/coverage.ja.md)。
* **ミューテーションテスト**: 実行可能なコードに入れた 88 個の小さな欠陥（[`mutation/mutants.txt`](mutation/mutants.txt)）。
  SPARK の crate の 84 個から、Rust のスライスでは書けない 3 個を除き、`SHA2.Functions` の 7 個を 2 通りに書いたものである。
  FFI の性質が 73 個を捕まえる。
  残る 15 個のうち 10 個は振る舞いを変えない。
  5 個はストリーミングの SHA-256 の長さの符号化にある本物のバグで、性質が試すより長いメッセージでしか現れない。Verus は 5 個とも検証に失敗する。
  Verus は振る舞いを変えない 10 個のうち 5 個でも失敗する。証明の失敗は、バグを見つけたことを意味しない。
  [doc/coverage.ja.md](doc/coverage.ja.md) の「ミューテーションテスト」。
* **性能**: NSA の Rust 参照実装の AES（`../algorithms/AES/rust/`。手を加えず、rustc とプロファイルも同じ）と比べた。
  x86_64 のデスクトップで `opt-level` 3 のとき、速さは約 2 倍、サイズも約 2 倍である。[doc/performance.ja.md](doc/performance.ja.md)。

## 構成

| パス | 内容 |
|---|---|
| [`src/aes/`](src/aes)、[`src/sha2/`](src/sha2)、[`src/hmac/`](src/hmac) | アルゴリズムごとに、spec 層（Cryptol のモジュール 1 つにつきモジュール 1 つ）、実装（`aes_impl`・`sha256_stream`・`sha256_impl`）、その lemma |
| [`src/cryptol/`](src/cryptol) | Cryptol の組み込みを spec 関数と lemma にしたもの |
| [`src/ffi/`](src/ffi) | Cryptol への FFI エクスポート（`verus!` の外） |
| [`ffi/`](ffi) | FFI のライブラリ。`src/ffi/` の cdylib で、独立した workspace |
| [`cryptol/`](cryptol) | こちらで書いた Cryptol。エクスポートを呼ぶ性質のモジュールと `properties.txt` |
| [`saw/`](saw) | SAW の証明。`llvm/`（bitcode の上）と `mir/`（MIR の上）、最後の実行の記録 `results.txt` |
| [`coverage/`](coverage)、[`mutation/`](mutation) | カバレッジとミューテーションテストの入力 |
| [`perf/`](perf) | 性能測定の道具（独立した workspace）。`perf/rust/` が NSA 側 |
| [`scripts/`](scripts) | trust surface のゲートとその一覧、FFI・SAW・カバレッジの検査、ミューテーションテスト、性能比較 |
| [`doc/`](doc) | 下に挙げる詳しい文書 |

## 再現

`verus/` で:

```console
$ cargo build && cargo test
$ cargo verus verify                                   # 326 verified, 0 errors
$ scripts/check-trust-surface.sh
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh   # FFI つきの Cryptol 3.6.0 が要る
```

Verus `0.2026.10.16.bf5bb51` を `Cargo.toml`（`[workspace.metadata.verus]`）で固定している。
Rust は `1.98.1`（`rust-toolchain.toml`）、vstd は `=0.0.0-2026-10-11-0230` である。
Cryptol 3.6.0 と SAW 1.6 は Galois のリリースページから取る（"with solvers" のビルド）。
SAW を含め、道具はすべて無料である。bitcode は rustc が、MIR は mir-json が出す。
SAW・カバレッジ・ミューテーションテスト・性能まで含めた手順: [doc/reproducing.ja.md](doc/reproducing.ja.md)。

## 文書

| 文書 | 内容 |
|---|---|
| [doc/reproducing.ja.md](doc/reproducing.ja.md) | 道具と、すべての検査の手順 |
| [doc/proving.ja.md](doc/proving.ja.md) | Verus の実行、リソース上限、spec と実装が意図して食い違う箇所、Cryptol 自身の性質、ゲート |
| [doc/cryptol-prelude.ja.md](doc/cryptol-prelude.ja.md) | Cryptol の組み込みの Verus での書き方と、その際の選択 |
| [doc/ffi.ja.md](doc/ffi.ja.md) | FFI での突き合わせ: Cryptol から Rust を呼ぶ方法、合格の条件、届かない範囲 |
| [doc/coverage.ja.md](doc/coverage.ja.md) | FFI の性質のもとでのカバレッジと、ミューテーションテスト |
| [doc/performance.ja.md](doc/performance.ja.md) | NSA の Rust の AES と比べたサイズと速さ |
| [doc/saw.ja.md](doc/saw.ja.md) | SAW の証明: どのサイズで何を証明し、何をしていないか。bitcode と MIR。実行のしかた |
| [doc/bootstrap.ja.md](doc/bootstrap.ja.md) | Verus・Cryptol・SAW・mir-json の入れ方 |
| [doc/walkthroughs/](doc/walkthroughs) | AES・SHA-256・HMAC-SHA-256: Cryptol と Verus を並べて |
