# 道具の準備

[English](bootstrap.md) | 日本語

[reproducing.ja.md](reproducing.ja.md) の道具のうち、rustup や cargo が取ってこないものの入れ方。
SPARK の crate の `spark/doc/bootstrap.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じである。その後にこちら独自の 3 節（Verus・SAW・mir-json）を足した。
ここに書いたことはすべて、x86_64 の Ubuntu 24.04 のデスクトップ 1 台で、2026-11-01 に手で行った。[README](../README.ja.md) へ戻る。

## Cryptol

FFI での突き合わせ・カバレッジ・ミューテーションテスト（`verus/cryptol/`）には、FFI を有効にしてビルドした Cryptol 3.6.0 が要る（`cryptol --version` が `FFI enabled` と出す）。
リリースの tarball `cryptol-3.6.0-ubuntu-24.04-X64-with-solvers.tar.gz`（sha256 は [reproducing.ja.md](reproducing.ja.md#道具) にある）がそれで、同じ `bin/` に z3・cvc4・cvc5・yices・abc も入っている。
専用のディレクトリに展開し、必要なスクリプトのときだけ `PATH` に入れる。

### `CRYPTOLPATH`

SPARK の crate と同じく、NSA のモジュールはリポジトリの最上位からの名前で呼ぶ（`algorithms::AES::Main`、`shared::...`）。
`scripts/check-ffi.sh` は `CRYPTOLPATH` にリポジトリの最上位と `verus/cryptol` を設定する。そのため性質のモジュールは `algorithms::AES::GF28` を NSA の名前で import できる。

Linux では、Cryptol はモジュールの外部実装を `.cry` ファイルの隣の `<Module>.so` に探す。`check-ffi.sh` は FFI のライブラリをそこへリンクする。
リポジトリにもともとある `algorithms/AES/{Cipher,KeyExpansion}.so` は、ビルドしていない NSA の Rust への symlink である。そのため Cryptol は見つからないと警告し、Cryptol の本体で代用する（その Rust をビルドすると突き合わせが失敗する理由は [ffi.ja.md](ffi.ja.md) にある）。

### aarch64 Linux（コンテナ、ソースからビルド）

省略。この crate は x86_64 Linux でしか動かしておらず、そこでは Galois のリリースを使う。
aarch64 Linux では、SPARK の crate の手順（ghcup で GHC 9.8.4 と cabal、Ubuntu のヘッダーの sysroot）に従えばよい。

### CI

省略。CI はない（[reproducing.ja.md](reproducing.ja.md#ci-で回すもの)）。

## x86_64 のインスタンスの準備

省略。準備のスクリプトはない。
SPARK の crate の `scripts/bootstrap-x86_64.sh` はピンのファイルから道具を入れるが、ここでは道具はこの文書のとおりに入れる。

## Verus

SPARK の crate にはない節。
Verus は、版の名前が示すコミット `bf5bb51f3f1a6ede578fcbafe86cfa1ba1885021`（github.com/verus-lang/verus）のソースから、その `BUILD.md` のとおり Rust 1.98.1 の release プロファイルでビルドする。
ビルドには Verus の Z3（4.16.0）が含まれる。`verus --version` は `Version: 0.2026.10.16.bf5bb51`、`Profile: release` と出す。

`cargo verus` はこのビルドを使わなければならない。版は `Cargo.toml` の `[workspace.metadata.verus]` に書いてある。
版を上げるときは、`rust-toolchain.toml` と `Cargo.toml` の `vstd` も一緒に上げる。

## SAW

SPARK の crate の文書にはない節（SPARK 版では、準備のスクリプトが x86_64 のインスタンスに SAW を入れる）。
リリースの tarball `saw-1.6-ubuntu-24.04-X64-with-solvers.tar.gz`（sha256 は [reproducing.ja.md](reproducing.ja.md#道具) にある）を使う。SPARK の crate が固定しているのと同じものである。
`saw --version` は `1.6 (68eed5f release-1.6)` と出す。同じ `bin/` に z3・cvc5・yices・bitwuzla・boolector・abc と SAW 自身の `cryptol` が入っている。

リリースの `.sig` は、SPARK の crate と同じく確かめていない。署名の鍵が keys.openpgp.org にも keyserver.ubuntu.com にもないため、固定するのは配布物の sha256 である。

`scripts/check-saw.sh` は、使える環境では `systemd-run --user` で `saw` の各実行のメモリを 10 GB までに抑える。

## mir-json

SPARK の crate にはない節（SPARK 版の SAW は bitcode しか読まない）。
SAW は Rust の MIR を mir-json を通して読む。使うのは、SAW 1.6 が submodule として持つコミット `8cbf9af1821075ef47cf784fef78d2650827730d`（github.com/GaloisInc/mir-json、JSON スキーマ 13）で、その `rust-toolchain.toml` が指定する Rust でビルドする:

```console
$ rustup toolchain install nightly-2026-03-21 --profile minimal --component rustc-dev,rust-src
$ git clone https://github.com/GaloisInc/mir-json src && cd src
$ git checkout 8cbf9af1821075ef47cf784fef78d2650827730d
$ cargo +nightly-2026-03-21 install --path . --locked --root <mir-json>
$ mir-json-translate-libs -o <mir-json>      # 標準ライブラリの MIR、rlibs/
```

`MIR_JSON_DIR=<mir-json>` で、`scripts/check-saw.sh` に置き場所を教える。
スクリプトはその `bin/` を `PATH` に、`rlibs/` を `SAW_RUST_LIBRARY_PATH` に入れ、`mir-json --version` が示すツールチェーンで `cargo saw-build` を呼ぶ。
