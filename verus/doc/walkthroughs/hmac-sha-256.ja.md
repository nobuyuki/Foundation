# HMAC-SHA-256: NSA の Cryptol から Verus へ

[English](hmac-sha-256.md) | 日本語

crate が HMAC-SHA-256（FIPS 198-1）をどう実装し、NSA の HMAC の Cryptol `algorithms/HMAC/Main.cry` とどう結びつけているか。
SPARK の crate の `spark/doc/walkthroughs/hmac-sha-256.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じだが短くしてある。
各節は Verus のコードが何をし、どこが違うかを述べる。コードとその doc comment は、節が名指すファイルにある。
HMAC は SHA-256 をそのインターフェースを通してだけ使う。SHA-256 には別の文書 [sha-256.ja.md](sha-256.ja.md) がある。

## 3 つの層

- **spec 層**（`src/hmac/`: `mod.rs`、`main`、`sha256`）。Cryptol を写した `spec fn` で、`HMAC`、`HMAC_init`、`opad`、`ipad` は Main.cry と同じ名前・引数・場合分けの構造をもつ。
  trait `hmac::main::Parameters` が Cryptol の関数のハッシュの引数とサイズのパラメータの役をし、その実装 `hmac::sha256::SHA256` が SHA-256 での `packaging/Hash.cry` の `HMAC` の役をする。
- **実装層**（`hmac::sha256_impl`）。実行可能である。バイトの上で動き、2 つのストリーミングの SHA-256 の文脈でハッシュする。
  その `ensures` は、結果がビットの上で spec 層のものと等しいことを述べる。
  両者の間には、`sha256_bytes::bits_of`、`sha256_stream` のストリーミングの定理（`lemma_update`、`lemma_final`）、`sha256_impl` 自身の lemma がある。
- **確かめ方**: Verus は、長さの上限の範囲のすべての鍵とテキストについて、実装 = spec 層を証明する。
  FFI での突き合わせは、実行可能な関数を NSA の Cryptol に対して回す。
  SAW は、コンパイルした実装が NSA の Cryptol と等しいことを、いくつかの固定の長さで証明する。

```text
  NSA の Cryptol                             Verus
  --------------                             -----
  algorithms/HMAC/Main.cry   <-- 写す ----  hmac::main（trait Parameters、spec fn）
  packaging/Hash.cry: HMAC   <-- 写す ----  hmac::sha256（impl Parameters）
        ^       ^                                  ^
        |       |                                  | Verus: ビットの上で
        |       |                                  | 等しい、全入力
        |       |                            hmac::sha256_impl（実行可能）
        |       |                                  |  の土台
        |       |                            sha2::sha256_stream（実行可能）
        |       |
        |       +-- FFI（ランダムテスト、RFC 4231） -- 実行可能な関数
        +---------- SAW（固定の長さ） ---------------- 実行可能な関数の bitcode と MIR
```

連鎖は SPARK の crate と同じく閉じるが、輪が 1 つ少ない。
spec 層は実行もコンパイルもできないので、Cryptol と比べるのは、丁寧に読むことと、spec 層と等しいと証明した実行可能な関数を通してだけである。

## 記法の読み方

[sha-256.ja.md](sha-256.ja.md#記法の読み方) と同じである。
加えて、ビット列の上の Cryptol の `^` は prelude の `bit_sequences::xor`、`#` は `Seq` の `+`、``take`{λ}`` は `.take(λ)` である。

## spec 層を宣言ごとに

### `HMAC` のパラメータ: 型パラメータとハッシュの引数

[`main.rs`](../../src/hmac/main.rs)。Main.cry の `HMAC` は、ハッシュ関数 `Hk`・`Hn`・`HL` を引数として、サイズ `B`・`L` を型パラメータとして受け取る。
ここではそれらを、SHA-2 の `main` と同じく、同じ順で trait `Parameters` にする（SPARK の crate は generic の formal にしている）。
呼び出しごとのサイズ `k`（鍵の長さ）、`n`（テキストの長さ）、`λ` は呼び出しごとのままにする。`k` と `n` は `Seq` の長さで、`λ` は `nat` の引数である。
Cryptol はハッシュに入力の型 `[k * 8]`、`[B * 8 + n]`、`[(B + L) * 8]` を与える。ここではハッシュは `max_length` より短い任意のビット列を受け取り、`HMAC` と `HMAC_init` の `recommends` がそれらの制約をもつ。`packaging/Hash.cry` の `UpperLimit` の制約と同じである。

### 型の制約

`B` と `L` についての Cryptol の制約と、どのハッシュも `[L * 8]` を返すことは、`Parameters::type_constraints` の `ensures` で、`hmac::sha256` がそれを（`lemma_hash_len` で）証明する。
`k`・`n`・`λ` についての制約は `recommends` である。

### `opad` と `ipad`

`opad = join(repeat(B, 0x5C))`、`ipad = join(repeat(B, 0x36))`。バイトでの prelude の `repeat` と `join` を通す（`hmac/mod.rs`）。

### `HMAC_init`: 鍵の前処理

`HMAC_init(K)`。Cryptol のガードの順（`k == B`、`k > B`、`k < B`）で `K.len()` について場合分けする。
それぞれ、鍵のビット、ハッシュした鍵を 0 で埋めたもの、鍵を 0 で埋めたもの。
Main.cry では private だが、ここでは public である。SPARK の crate と同じく、実装をこれに対して証明するからである。

### `HMAC`

`HMAC(K, text, λ) = HL((K0 ^ opad) + Hn((K0 ^ ipad) + text)).take(λ)`。`K0 = HMAC_init(K)` は `let` にする。

### SHA-256 の具体化

[`sha256.rs`](../../src/hmac/sha256.rs)。`packaging/Hash.cry` の `HMAC` が SHA256.cry について Main.cry を具体化するのと同じく、`impl Parameters for SHA256` とする:
`B = 64`、`L = 32`、`Hk`・`Hn`・`HL` はどれも `sha2::main::hash::<SHA256>` で、その上限 `2 ^^ 64` ビットは Hash.cry の `2 ^^ UpperLimit` である。

## Verus での Cryptol の prelude

HMAC は、バイトの上の `repeat`、`zero`、`^`、`join` を使う。どれも、HMAC が使う型での prelude のもの（[cryptol-prelude.ja.md](../cryptol-prelude.ja.md)）である（`hmac/mod.rs`）。
SPARK の crate の `Byte_Index` とその範囲に当たるものはない。長さは `nat` である。

## 実装と、Verus がそれを spec に結びつける方法

[`sha256_impl.rs`](../../src/hmac/sha256_impl.rs)。

### 一括の MAC と鍵の前処理

`init_key(key)` は 64 バイトの K0 を返し、それが spec 関数 `K0(key@)` であることを保証する。
64 バイトより長い鍵は `sha256_stream::hash` でハッシュしてから埋め、短い鍵はそのまま埋める。
`lemma_K0` は、ビットの上の `K0` が `HMAC_init` であることを証明する。
`exec::xor_pad` は spec 関数 `xor_pad` を計算する。
`hmac_sha256(key, text)` は `bits_of(d@) == HMAC::<SHA256>(key@, bits_of(text@), 256)` を保証する。中身は `init`、1 回の `update`、`finalize` である。

SPARK の crate の契約は、実行可能な `Init_Key` と `Xor_Pad` を呼ぶ。
Verus の契約は実行可能なコードを呼べないので、`K0` と `xor_pad` を spec 関数にし、実行可能な関数がそれを計算すると証明する。

### 逐次のインターフェース

`Context` は、K0 xor ipad とそれに続くテキストを与える内側の `sha256_stream::Context` と、K0 xor opad をもつ。
`init(key)` は `models(c, key@, empty)` を保証する。`update(c, data)` は `absorbed` を保証する。`lemma_update` が `models(c, key, M + data)` を与える。`lemma_final` は、`finalize` の MAC がビットの上での鍵と `M` の `HMAC` であることを証明する。
`sha256_stream` と同じく、文脈は鍵もテキストももたず、lemma がそれを受け取る。
`finished` は、内側の文脈が digest をもつことを `exists` で述べる。SPARK の crate はここで実行可能な `SHA256_Stream.Final` の呼び出しを書いている。

### HMAC の証明が SHA-256 から借りるもの

`sha256_stream::lemma_update` と `lemma_final`（文脈は与えられたものの `hash_bytes` を計算する）と、`sha256_bytes::lemma_hash_bytes`（`hash_bytes` はビットの上の spec の `hash` である）。
SHA-256 の証明のほかの部分は使わない。

### 証明の進め方

`lemma_hmac` は、2 つのストリームのメッセージの外側の digest が、ビットの上で `λ = 256` での spec の `HMAC` であることを証明する。
材料は、連結のビット（`lemma_bits_of_append`）、0 のビット、K0 のビット（`lemma_K0`）、K0 とパッドの xor のビット（`lemma_pad_xor_bits`）である。
SPARK の crate の外延性の lemma（`Lemma_Word_Of_Ext`、`Lemma_Hash_Ext` など）と `To_Bytes` に当たるものはない。`Seq` の等しさは等しさだからである。
SPARK の crate が prover を時間内に収めるために別に述べている `Lemma_Prefix_Extends` に当たるものもない。

## NSA の Cryptol に対する確かめ方

### FFI での突き合わせ

[`cryptol/Verus/HMAC/SHA256.cry`](../../cryptol/Verus/HMAC/SHA256.cry):
`hmac_sha256` と逐次のインターフェース（`verus!` の中で証明した `ffi::hmac_sha256::hmac_chunked` を通す）を、ランダムな鍵とテキスト、境目の鍵長（63、64、65 バイト）、長い長さ、RFC 4231 のベクトルで。`init_key` を `HMAC_init` に対して。
SPARK の crate の、spec 関数についての性質（`prop_HMAC_bits` など）に当たるものはない（[ffi.ja.md](../ffi.ja.md)）。

### SAW

[saw.ja.md の「SHA-256 と HMAC-SHA-256」](../saw.ja.md#sha-256-と-hmac-sha-256):
`hmac_sha256` を ``HMAC`{256, 64, k, 8 * n, 32} hash hash hash`` に対して、7 通りの（鍵、テキスト）のバイト長 (0, 0)、(32, 3)、(32, 32)、(64, 3)、(64, 32)、(65, 3)、(100, 32) で、bitcode と MIR の上で証明する。
逐次のインターフェースは単独では証明しない。一括のものと同じ関数だからである。

### 全入力で証明したことと、していないこと

Verus が全入力で証明したこと: 実行可能な関数が spec 層の `HMAC` と等しいこと。`2 ^^ 61` バイトより短いすべての鍵、`Max_Text`（`2 ^^ 61 - 64` バイト）より短いすべてのテキスト、すべてのチャンク分けについてである。
証明していないこと: spec 層がすべての長さで NSA の `HMAC` と等しいこと（テストと、7 通りの長さでの SAW）。バイトの整数倍でないテキストの上の HMAC（実行可能な関数はバイトの上で動く）。

## spec と実装が 1 対 1 でない箇所

[proving.ja.md](../proving.ja.md#spec-と実装が-1-対-1-でない箇所) と同じ。
`HMAC_init` は spec 関数 `K0` を通して `init_key` が実装し、パッドは `xor_pad` を通して `exec::xor_pad` が実装する。契約が実行可能なコードを呼べないからである。
