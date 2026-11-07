# 証明

[English](proving.md) | 日本語

この crate を Verus でどう証明するか: コマンド、リソース上限、spec 層と実装が意図して 1 対 1 になっていない箇所、Verus で証明し直した Cryptol 自身の性質、ゲート。
SPARK の crate の `spark/doc/proving.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じである。ここに対応するもののない節は、その理由を書いた。[README](../README.ja.md) へ戻る。

## Verus の実行

この crate は `verus/` で `cargo verus verify` によって検証する。手元での実行も記録用の実行も同じである:

```console
$ cd verus
$ cargo verus verify
verification results:: 326 verified, 0 errors
```

Verus `0.2026.10.16.bf5bb51` を `Cargo.toml`（`[workspace.metadata.verus]`）で固定している。
Rust は `1.98.1`（`rust-toolchain.toml`）、`vstd` は `=0.0.0-2026-10-11-0230`（`Cargo.toml`）で、3 つは一緒に動かす。
`d59a3f0` での全体の実行は 16 CPU の x86_64 のデスクトップで約 14 秒かかる。いちばん遅いモジュール `aes::sbox_entries` は単独で約 12 秒である。
モジュール 1 つだけを検証するには

```console
$ cargo verus focus -- --verify-only-module aes::sbox_entries
```

とする。

Verus をやり直すかどうかは Cargo が crate の中身から決める。そのためファイルを touch しても検証はやり直されない。`cargo clean -p foundation_verus` ならやり直される。
普通の `cargo build` も通らなければならない。ghost コード（`spec`・`proof`・`ghost` 変数）は消去され、ghost コードでしか要らない `use` は `#[cfg(verus_only)]` の中に置いてある。

SPARK の crate の `scripts/prove.sh`（gnatprove を呼ぶ唯一の方法で、レベルとタイムアウトの切り替えを拒み、実行が結果を新しく書いたことを確かめる）に当たるものはない。
`cargo verus verify` は設定をソースから取り、調べたすべての関数を 1 行で報告する。

Verus `bf5bb51` は、配列の引数を添字で引く `assert(...) by (bit_vector)` で（インタープリタの中で）panic する。
Verus の issue [#3076](https://github.com/verus-lang/verus/issues/3076) の panic で、そちらでは `by (compute)` から到達している。
この crate の証明にそう書いたものはない。

## レベル

SPARK の crate は、ユニットごとの証明のレベルを GPR に書いている。
Verus にはレベルがない。問い合わせごとにリソース上限 `rlimit` があり、関数は `#[verifier::rlimit(n)]` でそれを上げられる。
**上げている関数はない。** どの証明も Verus の既定の範囲に収まる。
rlimit の消費で測っていちばん重いのは、`sha2::sha256_stream::lemma_update`（約 5M）、`aes::aes_impl::expand_key` と `aes::properties::MixColumnsStepInverts`（それぞれ約 3M）である。
rlimit は時間ではなくソルバー自身のステップで数えるので、負荷の高いマシンでも証明が時間切れになることはない（SPARK の crate の「手元の既定は負荷の高いマシンではぎりぎり」に当たるものはない）。

## ボード

省略。この crate にはボードがない。
SPARK の crate の `scripts/board.py` は、Cryptol の関数ごとに、spec・FFI での突き合わせ・証明・SAW の結果・穴を、gnatprove のユニットごとの結果から数える。
Verus が報告するのは合計（326 verified、0 errors）だけで、失敗した関数はエラーになる。そのため証明の結果のボードを作ってもあまり足しにならない。
FFI・SAW・カバレッジ・ミューテーションの記録は、それぞれ別に置いてある（[ffi.ja.md](ffi.ja.md)、[saw.ja.md](saw.ja.md)、[coverage.ja.md](coverage.ja.md)）。

## spec と実装が 1 対 1 でない箇所

spec 層は Cryptol を宣言ごとに写す。実装は実行に向いた形にしてある。
たいていは spec 関数 1 つに実行可能な関数が 1 つあり、それと等しいと証明してある。
下の箇所では、SPARK の crate と同じく、設計としてそうなっていない。どれも穴でも証明の欠けでもない。

| 行 | 何が担うか | なぜこの設計か |
|---|---|---|
| `AES::SBox::affine`、`GF2::inverse (AES)` | `aes_impl::sub_byte` の事後条件は表 `SBox()[b]` である（FFI: `SBox` を `:exhaust` で 256 通り）。`properties::SBoxCorrect` が、`sbox_entries` から、すべてのバイトについて `affine(b) == SBox()[b]` を証明する | SPARK の crate と同じ。実装は S-box の表を引き、SBox.cry はそれを `inverse` の上に作った `affine` と結ぶ `SBoxCorrect` を述べる |
| `SHA2::Preprocessing::pad (SHA-256)` | `sha256_stream::hash` の事後条件は spec の `hash` で、これは `pad` を通して定義される。`finalize` はパディングしたメッセージの最後の 1 つか 2 つのブロックだけを書き（`tail_pad`）、`lemma_final` がそれを `pad_bytes(M)` のものだと証明し、`lemma_pad_bytes_bits` がそれを `pad` のバイトだと証明する | SPARK の crate と同じ。ストリーミングのハッシュはパディングしたメッセージを作らない。SPARK 版と違い、`pad` を単独で FFI で突き合わせたり SAW で証明したりはしない。spec 関数は実行できないからである（[ffi.ja.md](ffi.ja.md)） |
| `SHA2::Functions::Ch`、`Maj`、`SIGMA_256_0/1`、`sigma_256_0/1`。`SHA2::Notation::ROTR`、`SHR`。定数 `K_256`、`H0_256` | 各モジュールの `exec` にある同名の実行可能な双子。それぞれ spec 関数と等しいと証明してある | SPARK の crate では `Unsigned_32` の上の spec 関数は実行可能で、それが実装である（種類は `impl = spec`）。Verus の `spec fn` はコンパイルされないので、同じ本体の双子を置く |
| `SHA2::Main::hash (SHA-256, bytes)` | `sha256_stream::hash`。`sha256_bytes::hash_bytes` とも、メッセージのビットの上の spec の `hash` とも等しいと証明してある | SPARK の crate と同じ。`hash_bytes` は表現の層で、バイト列のビットの上の `hash` と等しいと証明してある（`lemma_hash_bytes`） |
| `HMAC::Main::HMAC_init (SHA-256)` | `hmac::sha256_impl::init_key`。spec 関数 `K0` を計算すると証明してあり、`lemma_K0` が `K0` はビットの上の `HMAC_init` だと証明する | SPARK の crate の契約は実行可能な `Init_Key` と `Xor_Pad` を呼ぶ。Verus の契約は実行可能なコードを呼べないので、`K0` と `xor_pad` を spec 関数にし、実行可能な対応物を置く |

SAW が単独では証明しない実装の部分は、[saw.ja.md の「SAW が単独で証明するもの、呼び出し元の中で証明するもの、証明しないもの」](saw.ja.md#saw-が単独で証明するもの呼び出し元の中で証明するもの証明しないもの)にある。

## Cryptol 自身の性質の証明し直し

`aes::properties` は、`algorithms/AES` が自分について述べる 15 個の性質のうち、SPARK の crate の `AES.Spec.Properties` と同じ 13 個（`GF28MultiplicationCorrect`、`SBoxCorrect`、`SBoxInverts`、`Cipher.cry` の `*Inverts`、`InvCipherEquivalence`、`EncryptInverts` など）を、Verus の spec 層について述べて証明する。
`SBoxPolynomialIsIrreducible` と `inverseCorrect` は、SPARK の crate と同じく述べていない。

**ここではこれらは省けない。**
SPARK の crate では、これらは spec 層の念のための確認である。spec 層が Cryptol と等しいことは、SAW が k = 128・192・256 ですでに証明している。
ここでは SAW にそれはできない。Verus の spec 関数はコンパイルされないので、SAW が証明するのは実装層だけである（[saw.ja.md](saw.ja.md#spec-層)）。
spec 層が Cryptol の言うとおりに振る舞うことを証明で確かめるのは、これらの性質だけである。

**軽い。**
鍵長を取る 4 つは const `k` について generic で、`Key k` を要求する。そのためどれも、すべての鍵長について一度の証明で済む（SPARK の crate はディスパッチャの上で述べている）。
SPARK の crate で遅いユニットの `SBoxCorrect`（キャッシュなしで約 26 分、CI で 1 時間 40 分）は、Verus のインタープリタで FIPS 197 の Table 4 を 1 行ずつ評価し、約 12 秒で済む（やり方は [`aes::sbox_entries`](../src/aes/sbox_entries.rs) に書いた）。
それぞれの証明のしかたと、SPARK の crate の証明と違うところは、モジュールの doc comment（[`aes::properties`](../src/aes/properties.rs)）にある。

## 遅い証明

省略。遅い証明はない。
SPARK の crate は遅いユニット `SBox_Entries` を必要なときだけ証明し、その証明の入力が変わったことをゲートが検出する。
ここでは対応する `aes::sbox_entries` も毎回の実行に含まれる。

## ゲート

SPARK の crate の CI は、変更のたびにゲートを回す。
この crate には CI がなく、ゲートは同じやり方で手で回す:

- `scripts/check-trust-surface.sh`: Verus が証明しない `src/` の箇所（`verus!` の外のコード、`assume`、`admit`、`axiom fn`、外部の本体や仕様、停止性の免除、検証器が見ない cfg、`unsafe`、外部への束縛、vstd が証明しない vstd の関数の呼び出し）が、すべて理由つきで `scripts/trust-surface.txt` に載っていること。
  載っているのは `src/ffi/` の FFI エクスポートだけ（100 件）で、何も仮定していない。
- `cargo verus verify`: すべての関数の検証が通り、`0 errors` であること。
  SPARK の crate の `scripts/check-proof.sh` は、gnatprove の報告に載っていないユニットや飛ばされた実体があっても失敗する。
  Verus は `verus!` の中のすべての関数を検証し、検証できないものはエラーとして報告する。`verus!` の外にあるものは trust surface が受け持つ。
- `cargo build` と `cargo test`（FIPS 197・FIPS 180-4・RFC 4231 のベクトルと、チャンクに分けた SHA-256 と一括のものの比較）が、警告なしで通ること。

SPARK の crate の文書のゲート（`check-doc-placement.sh`、`check-docs.sh`、gnatdoc）と遅い証明のゲート（`test-slow-proofs.sh`）に当たるものはない。
遅い証明はなく、文書のゲートは用意していない。
いちばん近いのは rustc の `missing_docs` lint である。`RUSTFLAGS="-W missing_docs" cargo build` は文書のない項目を報告しない。
ただしこれが見るのは普通のビルドがコンパイルするものだけで、spec 関数と proof 関数は見ない。また crate ではこれを有効にしていない。
