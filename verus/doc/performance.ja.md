# 性能

[English](performance.md) | 日本語

x86_64 の Linux のデスクトップで、crate の AES のサイズと速さを NSA の Rust の参照実装の AES と比べる。
SPARK の crate の `spark/doc/performance.md` に対応する文書である。[README](../README.ja.md) へ戻る。

## 実行のしかた

`scripts/perf-aes.sh` は、crate の AES（`aes::aes_impl`）を、リポジトリにある参照実装、NSA の Rust の crate `Cipher` と `KeyExpansion`（`../algorithms/AES/rust/`。手を加えずに path 依存で使う）と比べる。
対象は AES だけである。SPARK の crate と同じく、比べる相手になる参照実装の SHA-256 や HMAC がない。

```console
$ scripts/perf-aes.sh                     # 表示し、target/perf/perf-report.md に書く
$ PERF_SKIP_BENCH=1 scripts/perf-aes.sh   # ビルドとサイズだけ
$ PERF_QUICK=1 scripts/perf-aes.sh        # 動作確認。測定ではない
```

必要なものは cargo、`git`、binutils の `nm` と `size`、`python3`。
Linux で動き、macOS でも時間だけは測れる。macOS では報告にサイズの表が入らない。
Mach-O のシンボルにはサイズがなく、SPARK のスクリプトは代わりにリンカのマップを読むが、それにはマップの Rust の名前を demangle する必要がある。
ここでの macOS の実行は、Linux とは似ていないマシンでの参考値であって、同じ比較の 2 つ目のプラットフォームではない。
全体の実行はビルドを含めて約 40 秒かかる。

測定の道具は SPARK の crate の `spark/perf/` と同じ構成である。
`perf/` は crate の側で、`perf.gpr` の代わりに、`ffi/` と同じく独立した workspace をもつ Cargo のパッケージである。
`src/perf_aes.rs` にラッパー（`perf_aes.ads` と `.adb`）、`src/perf_bench.rs` にベンチマーク（`perf_bench.adb`）がある。
`perf/rust/` は NSA の側で、SPARK の crate の `spark/perf/rust/` から、コメントと `[workspace]` の表のほかは変えていない。
どちらも crate の一部ではなく、検証もせず、`src/` を対象とする trust surface の走査にも入らない。
スクリプトがビルドするもの:

| ビルド | フラグ |
|---|---|
| `verus-O2`、`verus-O3` | `perf/Cargo.toml` のプロファイル `perf-o2`/`perf-o3`: release、`opt-level` 2 / 3、`lto = "fat"`、`codegen-units = 1`。NSA の側と同じ |
| `verus-O3-checks` | プロファイル `perf-o3-checks`: `perf-o3` に `overflow-checks` と `debug-assertions` を有効にしたもの |
| `verus-release` | 素の `--release`: `opt-level` 3、LTO なし、codegen unit 16 |
| `rust-O2`、`rust-O3` | `perf/rust/Cargo.toml` のプロファイル `perf-o2`/`perf-o3`。SPARK の crate のもの |
| `rust-release` | 素の `--release` |

ほかはすべて release の既定である。オーバーフローの検査なし、debug assertion なし、`panic = "unwind"`。
スライスの範囲検査は残る。Rust にはそれを外すスイッチがなく、添字が範囲外にならないという Verus の証明は rustc には届かない。rustc は `requires` を見ないからである。
`verus-O3-checks` は、証明によって不要になった実行時検査を残す SPARK の crate の `spark-O3-checks` に当たる。
`perf.adc` の `Assertion_Policy (Ignore)` に当たる設定はない。Verus は cargo のビルドからすべての spec・proof・ghost の項目を消去する。
**両側を同じ rustc で**（`rust-toolchain.toml`、1.98.1）、同じプロファイルでコンパイルする。
SPARK の比較は GCC と rustc を比べている。ここではビルドの違いはソースだけである。
`target-cpu` は指定せず、ターゲットに対する rustc の既定を使う。
（`verus-release` は SPARK に対応するものがない。`rust-release` と比べるために置いた。）

**測り方。**
`perf_bench.rs` は、`perf_bench.adb` と同じく、NSA の側の `main.rs` がすることを同じ順にする。
各側は、演算ごとに inline 化しないラッパー 1 つを通して AES を呼ぶ。
crate の関数は鍵長を const generic（Cryptol の `{k}`）で受け取り、SPARK の crate と NSA のものは実行時に受け取る。
そこで crate のラッパーは鍵長を実行時に受け取り、`match` で 3 つの具体化に振り分ける。
両方の道具が鍵長を `black_box` に通すので、どのラッパーも定数の鍵長に特化されない（SPARK の道具は同じ理由で `Volatile` から読む）。
各道具はまず FIPS-197 の Appendix C.1–C.3 を確かめる: 暗号化し、復号して戻す。crate の側では両方の復号で戻す。
次に各演算の時間を、10 000 回の連鎖した呼び出し（各出力が次の入力になる）のバッチで測る。ウォームアップに 20 バッチ、測定に 101 バッチで、`Instant`（Linux では `CLOCK_MONOTONIC`）を使う。
1 回の呼び出しあたりの時間の中央値と四分位を報告する。

サイズは、リンクした実行ファイルのシンボルから `nm -S -C` で読む。
"AES" は crate のすべてのシンボル（`foundation_verus::*`）、または NSA の 2 つの crate のすべてのシンボルである。
ラッパーは `perf_aes::*` と `aes_perf::{expand_key, encrypt, decrypt}`。
道具と Rust の std は数えない。SPARK のスクリプトと同じく、無名の定数も数えない。
crate の S-box `S_BOX` と `INV_S_BOX` はそこに入る。これらは `const` で、rustc はシンボルなしで出す。
NSA の `SBOX` と `INVSBOX` は `static` で、シンボルがある。
そのため crate の "AES data" は 0 で、512 バイトの S-box は表に入っていない。
NSA の 812 バイトは、S-box、`RCON`、2 つの `PERM` の表である。

**何を比べているか。**
SPARK の文書が自分の比較について言うとおり、NSA の Rust は参照実装で、S-box は表、`mul_bytes` はシフトと加算、`xTimes` には秘密の値についての `if` があり、T-table もハードウェアの AES 命令も使わない。
crate も同じアルゴリズムである。S-box は表、`x_times` はシフトと条件つきの簡約で、`MixColumns` の積は `x_times` の和である。
NSA の `inv_cipher` は `cipher` のラウンドを逆順に戻す。これは `decrypt_block_prime`（InvCipher'）と同じである。
`decrypt_block` は FIPS の InvCipher で、NSA の Rust にはない。そこで両方を NSA の `decrypt` と比べる。

## x86_64、Linux（デスクトップ）

Intel Core i9-9900K（8 コア、論理 CPU 16）、Linux 7.1、rustc 1.98.1、2026-11-02 09:24 UTC。
全体の実行を続けて 2 回行い、数字は 1 回目のものである。
2 回目の中央値は 75 のセルのうち 71 で 1 回目の 3% 以内、すべてで 5.5% 以内に収まり、サイズは同一である。
**共用のデスクトップで、遊んでいるマシンではない**: 1 分の load は 1 回目の前に 0.98、2 回目の後に 1.44 だった（ベンチマーク自身もその 1 つ）。証明やほかのベンチマークは動かしていない。
スレッドはコアに固定していない。
四分位の幅は、中央のセルで 0.9%、75 のセルのうち 56 で 2% 以内、すべてで 4.4% 以内である。

サイズ（バイト）:

| ビルド | AES text | AES data | ラッパー | AES 合計 | 実行ファイルの text |
|---|---:|---:|---:|---:|---:|
| `verus-O2` | 2430 | 0 | 7294 | 9724 | 282 954 |
| `verus-O3` | 2151 | 0 | 5794 | 7945 | 285 866 |
| `verus-O3-checks` | 2151 | 0 | 5794 | 7945 | 286 778 |
| `verus-release` | 2170 | 0 | 6190 | 8360 | 298 819 |
| `rust-O2` | 3316 | 812 | 15 | 4143 | 276 714 |
| `rust-O3` | 3447 | 812 | 15 | 4274 | 280 026 |
| `rust-release` | 3297 | 812 | 18 | 4127 | 292 979 |

* **"AES text" ではなく "AES 合計" を読む。**
  rustc は、LTO なしのものも含めすべてのビルドで、crate の暗号と鍵スケジュールをラッパーに inline 化する。
  これらは generic なので、具体化はそれを名指す crate `perf_aes` の中でコンパイルされる。
  関数として残るのは、具体化が共有する末端だけである。`opt-level` 3 では `mix_columns` 728、`inv_mix_column` 452、`inv_round` 352、`inv_round_prime` 330、`round` 289 バイト。
  ラッパーは `encrypt` 2400、`expand_key` 1673、`decrypt_prime` 1029、`decrypt` 692 バイト。
  NSA のラッパーは末尾呼び出しである。
  NSA の `key_expansion` は 1324 バイト、`inv_mixcolumns_step` 668、`cipher` 645、`inv_cipher` 643。
* **crate の AES は NSA のものの約 2 倍の大きさ**: `opt-level` 3 で 1.9 倍（7945 対 4274 バイト）、2 で 2.3 倍、LTO なしで 2.0 倍。
  crate の 512 バイトの S-box を数に入れると、`opt-level` 3 で 2.0 倍（8457 対 4274）。
  crate の演算はどれも鍵長ごと（const generic の `k`）に 3 回コンパイルされ、NSA のものは 1 回である。
* **`verus-O3-checks` は `verus-O3` と同じ機械語である。**
  crate の AES とラッパーの逆アセンブルは、2 つのビルドで命令ごとに同一である。
  違うのは panic の位置のアドレスだけで、それは std のデータである。
  オーバーフローの検査と debug assertion を有効にしても、rustc は AES に何も足さない。足すはずの検査は最適化で 1 つも残らない。
  実行ファイルの 912 バイトの差は std と道具にある。
* サイズは rustc が何を inline 化するかに左右される。

時間（1 回の呼び出しあたりの ns、中央値。第 1・第 3 四分位は報告にある）:

| 演算 | `verus-O3` | `rust-O3` | `verus-O2` | `rust-O2` | `verus-release` | `rust-release` |
|---|---:|---:|---:|---:|---:|---:|
| AES-128 `expand_key` | 73.9 | 336.0 | 80.3 | 335.7 | 73.9 | 312.7 |
| AES-128 暗号化 | 246.6 | 444.7 | 239.4 | 479.6 | 244.9 | 438.1 |
| AES-128 復号（`decrypt_block`） | 369.1 | 712.9 | 382.5 | 762.9 | 372.8 | 757.4 |
| AES-128 `decrypt_block_prime` | 380.1 | 712.9 | 395.0 | 762.9 | 375.5 | 757.4 |
| AES-192 `expand_key` | 95.2 | 389.5 | 103.9 | 382.6 | 96.1 | 347.0 |
| AES-192 暗号化 | 299.0 | 536.3 | 289.0 | 571.3 | 296.8 | 526.5 |
| AES-192 復号（`decrypt_block`） | 449.2 | 865.6 | 463.9 | 921.9 | 453.5 | 916.4 |
| AES-192 `decrypt_block_prime` | 453.2 | 865.6 | 479.7 | 921.9 | 457.3 | 916.4 |
| AES-256 `expand_key` | 113.2 | 446.7 | 113.5 | 445.5 | 108.5 | 411.9 |
| AES-256 暗号化 | 350.7 | 624.0 | 338.4 | 708.5 | 349.3 | 617.8 |
| AES-256 復号（`decrypt_block`） | 529.2 | 1014.3 | 546.0 | 1077.8 | 535.6 | 1072.4 |
| AES-256 `decrypt_block_prime` | 533.5 | 1014.3 | 564.6 | 1077.8 | 538.8 | 1072.4 |

（`decrypt_block_prime` の行の Rust の列は、NSA の 1 つしかない復号を繰り返したものである。
`verus-O3` と同じコードの `verus-O3-checks` は、すべてのセルで `verus-O3` の 4% 以内（0.98–1.04 倍）に収まる。
これは、ここでコードの配置とマシンだけが生む効果の大きさであり、ほかの列が見分けられる差の限界でもある。）

`opt-level` 3 で分かること:

* **crate の AES は NSA のものの約 2 倍速い**: 鍵拡張 0.22–0.25 倍、暗号化 0.55–0.56 倍、復号 0.52 倍（`decrypt_block`）と 0.52–0.53 倍（`decrypt_block_prime`。NSA の `inv_cipher` と同じ構造）。
  SPARK の crate は、その x86_64 のインスタンスで、同じ Rust（rustc 1.95.0、別の CPU）に対して暗号化 0.51–0.53 倍、鍵拡張 0.39–0.42 倍、復号 1.01–1.03 倍だった。
  ここでは両方のコンパイラが rustc なので、差はソースにある。ソースのどこにあるかは調べていない。
* **比はプロファイルを変えても保たれる**: `opt-level` 2 では crate は鍵拡張で 0.24–0.27 倍、暗号化で 0.48–0.51 倍、復号で 0.50–0.52 倍。LTO なしでは 0.24–0.28 倍、0.56–0.57 倍、0.49–0.50 倍。
* **`opt-level` 2 と 3 の差も LTO も、どちらの側にもあまり効かない**。上の 4% の範囲か、その近くである。
  crate は 2 で暗号化が 3–4% 速く、復号が 3–6% 遅く、鍵拡張が最大 9% 遅い。LTO なしの crate は `perf-o3` の 4% 以内である。
  NSA のものは 2 で暗号が 6–14% 遅い。
  NSA の `key_expansion` は、素の release ビルドのほうが `perf-o3` より 7–11% 速い。SPARK の文書もそう見ている（その x86_64 のインスタンスで 25–27%）。NSA の復号は 6% 遅い。
* **ここでは検査の代価はない**: 証明がオーバーフローを起こりえなくし、このコードでは rustc も自力で同じ結論に達する（上を参照）。
  範囲検査は別である。証明があってもなくても、どのビルドにも残る。`perf-o3` の crate の AES にはまだ範囲検査の panic の呼び出しが 28 個あり、NSA のものには 15 個ある。
