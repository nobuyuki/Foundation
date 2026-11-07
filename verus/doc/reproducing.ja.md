# 結果の再現

[English](reproducing.md) | 日本語

SPARK の crate の `spark/doc/reproducing.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じである。
SPARK の crate には道筋が 2 つある。無料の道具による **FSF の道筋**と、GNAT Pro 27 の LLVM バックエンドが要る **SAW の道筋**である。
ここでは道具はすべて無料で、SAW が読む LLVM bitcode と MIR は rustc が出す。そのため道筋は 1 つで、その節は最初の見出しの下にまとめた。[README](../README.ja.md) へ戻る。

## 無料の道筋

### 道具

| 道具 | 版 | 使うところ |
|---|---|---|
| Rust（rustup） | 1.98.1、`llvm-tools` つき | ビルド、証明、FFI での突き合わせ、カバレッジ、性能（`rust-toolchain.toml`） |
| Verus | `0.2026.10.16.bf5bb51`（コミット `bf5bb51f3f1a6ede578fcbafe86cfa1ba1885021`）、その Z3 4.16.0 つき | 証明（`Cargo.toml` の `[workspace.metadata.verus]`） |
| vstd | `=0.0.0-2026-10-11-0230` | 証明（`Cargo.toml`。cargo が取ってくる） |
| FFI を有効にしてビルドした Cryptol と z3 | 3.6.0 | FFI での突き合わせ、カバレッジ、ミューテーションテスト |
| SAW | 1.6 | SAW |
| mir-json とその Rust | コミット `8cbf9af`、`nightly-2026-03-21` | MIR の上の SAW |
| python3、bash、GNU の `c++filt` | | スクリプト。`c++filt` は bitcode の上の SAW で使う |

入手先:

- **Rust 1.98.1**: rustup が `rust-toolchain.toml` を読む。カバレッジには `rustup component add llvm-tools --toolchain 1.98.1` が要る。
- **Verus**: 上のコミットのソース（github.com/verus-lang/verus）から、release プロファイルで、上の Rust でビルドする。
  `cargo verus` がこのビルドを見つけられなければならない。`Cargo.toml` の版がこれを指す。
- **Cryptol 3.6.0** と **SAW 1.6**: Galois のリリースページの
  `cryptol-3.6.0-ubuntu-24.04-X64-with-solvers.tar.gz`（sha256 `621860aa1dedc037e8fc8355bef3edf023e41e78efb7177146126f5a87309962`）と
  `saw-1.6-ubuntu-24.04-X64-with-solvers.tar.gz`（sha256 `0b25c8b32db8b4a7ec32d6700024af60bb2a0398ee350b630dd84ff377c938f7`）。
  SPARK の crate が固定しているものと同じである。
- **mir-json**: [bootstrap.ja.md](bootstrap.ja.md#mir-json)。

SPARK の crate はすべての版と sha256 を `scripts/toolchain-pins.env` で固定し、CI と準備のスクリプトがそれを読む。
ここでは版は道具が読む場所（`rust-toolchain.toml`、`Cargo.toml`）で固定し、ダウンロードするものはこの表で固定する。ピンのファイルを読む CI も準備のスクリプトもないからである。

### 手順

リポジトリを checkout したところから:

```console
$ cd verus
$ cargo build
$ cargo test
$ cargo verus verify                    # 326 verified, 0 errors
$ scripts/check-trust-surface.sh
```

**証明。** `cargo verus verify` がすべての関数を検証する。16 CPU の x86_64 のデスクトップで約 14 秒。
ゲートのスクリプトも、ボードも、遅い証明もない: [proving.ja.md](proving.ja.md)。

**Cryptol との突き合わせ。**

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh                  # すべての性質、約 6 分
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-ffi.sh prop_Impl_Dot    # 指定したものだけ
```

詳細: [ffi.ja.md](ffi.ja.md)。

**SAW。**

```console
$ PATH=<saw-1.6>/bin:<cryptol-3.6.0>/bin:$PATH MIR_JSON_DIR=<mir-json> scripts/check-saw.sh
```

両方の経路（LLVM bitcode と MIR）で約 15 分。`SAW_ROUTE=llvm` か `mir` で片方だけを回す。
clean な tree から回すと `saw/results.txt` を書く。詳細: [saw.ja.md](saw.ja.md)。

**カバレッジ**（Linux）:

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-coverage.sh    # 約 8 分
```

詳細: [coverage.ja.md](coverage.ja.md)。

**ミューテーションテスト**（数時間。[coverage.ja.md](coverage.ja.md#ミューテーションテスト)）:

```console
$ scripts/mutation.py setup /tmp/mut
$ scripts/mutation.py prove /tmp/mut
$ scripts/mutation.py ffi /tmp/mut && scripts/mutation.py ffi /tmp/mut --full
$ scripts/mutation.py saw /tmp/mut --baseline
$ scripts/mutation.py saw /tmp/mut ID ...          # FFI を生き延びたものと F のミュータント
$ scripts/mutation.py report /tmp/mut
```

**性能**（任意）:

```console
$ scripts/perf-aes.sh
```

詳細: [performance.ja.md](performance.ja.md)。

**文書のゲート**: 省略。ない（[proving.ja.md の「ゲート」](proving.ja.md#ゲート)）。

### x86_64 Linux で 1 コマンド

省略。準備のスクリプトはない。
SPARK の crate の `scripts/bootstrap-x86_64.sh` は、何も入っていない Ubuntu 24.04 のマシンを FFI での突き合わせが通るところまで持っていく。ここでは道具は手で入れる（[bootstrap.ja.md](bootstrap.ja.md)）。

### CI で回すもの

省略。CI はない。上の検査はすべて手で回す。SAW の実行は、回したコミットとともに `saw/results.txt` に記録する。

## SAW の道筋（GNAT Pro）

省略。ここでは SAW に独占的な道具は要らない。
SPARK の crate の bitcode は GNAT Pro 27 の LLVM バックエンドから作らなければならず、同じ版の LLVM の `llvm-link` も要る。
ここでは bitcode は rustc が（`--emit=llvm-bc`）、MIR は mir-json が出し、SAW は上の無料の道筋と同じように回す。

### 道具

省略。上の表にある。

### 手順

省略。上の「手順」にある。
記録した実行（`saw/results.txt`、`d59a3f0` で）は、16 CPU の x86_64 のデスクトップで 928 秒かかった。
`llvm/aes_impl.saw` が 11 秒、`llvm/sha256_impl.saw` が 30 秒、`mir/aes_impl.saw` が 20 秒、`mir/sha256_impl.saw` が 159 秒で、残りはビルドと陰性対照である。
