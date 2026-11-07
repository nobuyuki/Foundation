# Cryptol との FFI での突き合わせ

[English](ffi.md) | 日本語

crate の実行可能な関数を Cryptol の `foreign` インターフェースで Cryptol から呼び、全数かランダムのテストで NSA の Cryptol と比べる方法。
SPARK の crate の `spark/doc/ffi.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書である。[README](../README.ja.md) へ戻る。

## FFI の仕掛け

FFI での突き合わせは、crate が Cryptol の言うとおりに計算することを機械で確かめるものである。
実行可能な関数を C を通してエクスポートし、Cryptol から `foreign` で呼び、それが実装する NSA の関数と `:exhaust` か `:check` で比べる。
これはテストであり、証明ではない。

```console
$ FFI_JOBS=3 scripts/check-ffi.sh             # ビルドして、すべての性質を回す
$ scripts/check-ffi.sh prop_Impl_Dot          # 指定した性質だけ
```

必要なもの: FFI を有効にしてビルドした Cryptol 3.6（`cryptol --version` が "FFI enabled" と出す）を `PATH` に置くか `CRYPTOL` で指定する。
z3 を `PATH` に置く（Cryptol の型検査が使う。`with-solvers` のリリースでは両方が `bin/` にある）。
`rust-toolchain.toml` のツールチェーンの cargo と、python3。
スクリプトは `CRYPTOLPATH` にリポジトリの最上位と `cryptol/` を設定する。そのため性質のモジュールは `algorithms::AES::GF28` を NSA の名前で import できる。
スクリプトは SPARK の crate のものを、gprbuild を cargo に替えて使っている。macOS の手順（`.dylib`、hardened runtime の Cryptol を ad hoc に署名した写し）は残してあるが、動かしてはいない。

**部品。**

- `ffi/Cargo.toml` は FFI のライブラリ `target/release/libfoundation_verus_ffi.so` をビルドする。
  これは `cdylib` で、その `lib.rs` は crate の `ffi` モジュールを re-export する。
  独立した Cargo の workspace なので、`verus/` での `cargo verus verify` と `cargo build` はこれをビルドしない。release プロファイルでもオーバーフローの検査と debug assertion を残してある。
  （SPARK の crate の `foundation_spark_ffi.gpr` に当たる。）
- `src/ffi/`: Cryptol のモジュール 1 つにつき、`extern "C"` のエクスポートを集めた Rust のモジュール 1 つ（`ffi::aes_gf28` など）。それに `src/ffi/mod.rs` の補助関数。
  各ファイルは `scripts/trust-surface.txt` の `foreign-binding` の項目で、各エクスポートは `outside-verus` と `unsafe` の項目である。
- `cryptol/Verus/<path>/<File>.cry`: エクスポートを **Cryptol の本体なしで** `foreign verus_<name>` として宣言し、性質（`verus_x_times b == xTimes b`）を述べるモジュール（`Verus::AES::GF28`）。
  Cryptol はモジュールの外部実装を隣の `<File>.so` から読み込む。`check-ffi.sh` はそこにライブラリをリンクする（gitignore してある）。
- `cryptol/properties.txt`: モジュール、性質、関数、モード、テストの回数。
- `scripts/check-ffi.sh`: ビルドし、リンクし、性質を 1 つずつ別の `cryptol -b` で回し、`target/ffi/ffi-results.txt`（SPARK の crate の形式）を書く。各実行のスクリプトと出力は `target/ffi/run/` に残す。

**エクスポートするのは実行可能な関数だけ。**
SPARK の crate はライブラリを `-gnata` でビルドして ghost の spec 層を実行できるようにし、各 spec 関数を、それが書き写した Cryptol と直接突き合わせる。各実行可能な関数も突き合わせる。
Verus の `spec fn` はまったくコンパイルされない。そこでこの crate は実行可能な関数（実装層と、`sha2::functions::exec` のような spec 関数の実行可能な写し）をエクスポートする。それぞれ、自分が実装する spec 関数と等しいと証明してある。
spec 層は、その証明を通して確かめる。あるサンプルでエクスポートが Cryptol と一致すれば、そのサンプルでは spec 関数も一致する。
SPARK の crate も、同じ理由で、ランダムテストの大半を実行可能な関数に対して行っている（その文書の "Targeted, not volume"）。

その結果、SPARK の crate と比べて Cryptol と突き合わせずに残るもの（SPARK 版の 141 個の性質のうち 68 個は対応するものがない。`properties.txt` に一覧がある）:

- 実行可能な対応物のない spec 関数。上位の関数の一部としてだけ確かめられる。
  Preprocessing.cry の `pad` と `parse`（SPARK の crate の `prop_pad`、`prop_parse`）と、prelude の generic（SPARK 版の `SPARK/Prelude.cry`: `foldl`、`bit`、`join`、`split`、`pmult`、`pmod`、`pdiv` など）。後者はここに対応するモジュールがない。
- 長さがバイトの整数倍でないビット列の上の SHA-256 と HMAC（`prop_hash_bits`、`prop_HMAC_bits`）。
  実行可能な関数はバイトの上で動き、spec と等しいと証明してあるのもそこだけである。
- 実行可能な関数が同じ Cryptol と突き合わせられる場合の、spec 自身の関数
  （`prop_Dot` / `prop_Impl_Dot`、`prop_Cipher128` / `prop_Encrypt_Block128`、`prop_KeyExpansion128` / `prop_Expand_Key128`、`prop_step` / `prop_Compress`、`prop_HMAC_init` / `prop_Init_Key` など）。
  ここにあるのは各組の後者だけである。

SPARK の spec の性質が NSA の Cryptol そのものを公表されたベクトルとも突き合わせていたところ（`prop_hash_FIPS`、`prop_HMAC_RFC4231`）は、その半分を実行可能な関数の性質（`prop_Stream_Hash_FIPS`、`prop_HMAC_SHA256_RFC4231`）に残した。Main.cry の性質に `fips197C` があるのと同じである。

**エクスポート。**
各エクスポートは Cryptol の引数を Rust の値に読み込み、呼ぶ関数の事前条件のうち Cryptol の型が保証するはずのもの（`Key k`、`rcon` の `1 <= i <= 10`、SHA-256 の `Max_Bytes` と HMAC の `Max_Text`、メッセージに収まる整列したチャンク分け）を実行時に確かめ、証明済みの関数を呼び、結果を書く。
確認に失敗すると panic する。`extern "C"` の関数での panic は Cryptol を abort させるので、その実行は失敗する。
それ自身に論理をもつコードは `verus!` の中に置いて証明してある。逐次の HMAC のチャンク分けの上のループは `ffi::hmac_sha256::hmac_chunked` で、spec の `HMAC` と等しいと証明してある（SPARK の crate の `FFI.HMAC_SHA256_Impl.HMAC_Chunked` に当たる。SHA-256 のものは crate 自身の `sha256_stream::hash_chunked`）。
SPARK の crate は spec が ghost なので、モジュールごとに 2 つのユニット（ghost の shim と、それを GNAT のリンク名で import するエクスポート）が要る。
ここのエクスポートは普通の関数を呼ぶので、Cryptol のモジュール 1 つにつきモジュールは 1 つで、リンク名の細工もない。

**合格の条件。**
SPARK の crate と同じく、Cryptol 3.6 はライブラリを一度も呼ばなかった実行を、失敗にせずに報告することがある。そこで `check-ffi.sh` が性質を合格とするのは、次のすべてを満たすときだけである:

- `cryptol` が 0 で終わり、`ERROR`・反例・`[error]` が出ていない。
- 性質のモジュールが `Loading dynamic library <File>.so` と出している。
  本体のない `foreign` は、ライブラリがなくても読み込みに失敗しない。その場合は呼び出しのたびに評価のエラーになる。
  本体があると、ライブラリがないときに性質が Cryptol を Cryptol 自身と比べることになり、合格してしまう。
- `cryptol/` の外のモジュールが動的ライブラリを読み込んでいない。
  NSA の、Cryptol の本体をもつ `foreign` 宣言（`AES::Cipher`、`AES::KeyExpansion`、`Keccak::StepMappings`）は、その本体で代用される。リポジトリの `.so` ファイルが、ビルドしていない `rust/*/target/` への symlink だからである。
  誰かがその Rust をビルドすると、比較が黙って Verus 対 NSA の Rust に変わってしまう。そこで `check-ffi.sh` はその場合は失敗させる。
- Cryptol が `Passed N tests.`（N は予定した回数）と出し、`:exhaust` なら `Q.E.D.` と出している。

**ビット列の渡し方。**
Cryptol の C の呼び出し規約で渡せるのは、定数 `K <= 64` の `[K]`（`uint8_t` から `uint64_t` として）と、そういうワードの列（`[n][8]` は `uint8_t *` として。サイズの変数はそれぞれ先に `size_t` で渡す）だけである。
列の結果は引数の後ろのポインタを通して書かれ、`()` は何も渡さない。任意の長さの `[l]` は受けつけない。
そのため Main.cry の `[k]` の鍵と `[128]` のブロックは Cryptol の側でバイトに分け、結果を join する: ``join (verus_encrypt`{k} (split key) (split in))``。
これが `aes_impl::main::encrypt` の受け取るもので、証明もこれについて行っている。
SHA-256 と HMAC はメッセージを `[n][8]` で受け取り、``SHA256::hash (join M)`` と比べる。
型に依存する長さは、Cryptol が渡した分だけ読む。`[Nr k + 1]Block` は、`Key k` を確かめた後に `k / 32 + 7` ブロックとして読む。

**量でなく狙いで。**
性質とテストの回数は、SPARK の crate の、実行可能な関数に対するものと同じである。
バイト単位の関数は全数（`xTimes`、`(•)`、S-box、`Rcon`）。
ラウンドの変換は 10,000 回。ブロック暗号と鍵スケジュールは鍵長ごとに 1,000 回。
バイト単位の AES は合成したもの（`implEncrypt`）を 1,000 回、全体（`execEncrypt`）を 100 回。
SHA-256 はパディングの境目と、より長い長さの固定の一覧（SPARK の crate が選んだもの）。
HMAC は 63・64・65 バイトの鍵と境目の鍵長。切れ目 12 個のランダムなチャンク分け。
それに公表されたベクトル（FIPS 197 の Appendix A から C、Tests.cry のもの、FIPS 180-4 のもの、RFC 4231 のもの）。
N は性質ごとに `properties.txt` にある。
